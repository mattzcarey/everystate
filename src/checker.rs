//! Explicit-state breadth-first model checker (port of checker.ts).
use crate::ast::{E, N};
use crate::eval::*;
use crate::intern::*;
use crate::model::*;
use crate::value::*;
use std::cmp::Ordering;
use std::rc::Rc;

#[derive(Clone)]
pub struct TraceStep {
    pub state: StateRef,
    pub action: Option<usize>,
    pub id: i64,
}
#[derive(Clone, Copy)]
pub struct Outdegree {
    pub min: u32,
    pub avg: u32,
    pub p95: u32,
    pub max: u32,
}
pub struct CheckResult {
    pub status: &'static str,
    pub name: Option<String>,
    pub message: Option<String>,
    pub trace: Option<Vec<TraceStep>>,
    /// liveness: index (0-based) of the state the lasso returns to; -1 = stuttering
    pub loop_to: Option<i64>,
    pub loop_action: Option<usize>,
    pub live_branches: usize,
    /// TLC-style list of nested expression positions for evaluation errors
    pub call_stack: Option<String>,
    /// TLC message code for `message`, when it is not a generic error
    pub code: Option<u32>,
    pub generated: u64,
    pub distinct: u64,
    pub queue: u64,
    pub depth: u32,
    pub init_generated: u64,
    pub init_distinct: u64,
    pub print_summary: bool,
    pub outdegree: Option<Outdegree>,
}

/// Progress notifications (the CLI prints TLC's progress messages from these).
pub trait Events {
    fn init_done(&mut self, _init_generated: u64, _init_distinct: u64) {}
    fn progress(&mut self, _depth: u32, _generated: u64, _distinct: u64, _queue: u64) {}
    /// phase: "branches" | "start" | "end"
    fn liveness(&mut self, _phase: &str, _branches: usize, _depth: u32, _generated: u64, _distinct: u64) {}
    /// A remark about the run itself (the parallel search going back to one worker).
    fn note(&mut self, _text: &str) {}
}
pub struct NoEvents;
impl Events for NoEvents {}

pub struct CheckOptions {
    pub check_deadlock: bool,
    pub record_graph: bool,
    /// parallel breadth-first search (`-workers N`, N > 1); None = one worker
    pub par: Option<ParConfig>,
}

/// How to run the search on several threads. Every worker thread builds its own copy of the model
/// (`factory`), because the evaluator, the syntax tree and all values are single-threaded.
#[derive(Clone)]
pub struct ParConfig {
    pub workers: usize,
    pub factory: std::sync::Arc<dyn Fn() -> R<Model> + Send + Sync>,
    /// a level is searched in parallel when it has at least this many states
    pub min_frontier: usize,
    /// ... and, unless `eager`, the search has been running for a moment (starting the workers costs
    /// about as much as checking a small model)
    pub eager: bool,
    /// states per unit of work handed to a worker; 0 = chosen per level
    pub chunk: usize,
}

/// Open-addressing hash set of 64-bit fingerprints mapping to state ids.
pub struct FpSet {
    keys: Vec<u64>, // 0 = empty
    ids: Vec<u32>,
    size: usize,
    mask: usize,
}
impl FpSet {
    pub fn new() -> FpSet {
        FpSet::with_capacity(1 << 16)
    }
    /// `cap` must be a power of two.
    pub fn with_capacity(cap: usize) -> FpSet {
        FpSet { keys: vec![0; cap], ids: vec![0; cap], size: 0, mask: cap - 1 }
    }
    pub fn len(&self) -> usize {
        self.size
    }
    /// The id stored for `fp`, without inserting.
    #[inline]
    pub fn get(&self, fp: u64) -> Option<u32> {
        let fp = if fp == 0 { 0x9E37_79B9_7F4A_7C15 } else { fp };
        let mut i = (fp as usize) & self.mask;
        loop {
            let k = self.keys[i];
            if k == 0 {
                return None;
            }
            if k == fp {
                return Some(self.ids[i]);
            }
            i = (i + 1) & self.mask;
        }
    }
    /// Returns the existing id, or None after inserting `id`.
    #[inline]
    pub fn put(&mut self, fp: u64, id: u32) -> Option<u32> {
        if self.size * 2 >= self.keys.len() {
            self.grow();
        }
        let fp = if fp == 0 { 0x9E37_79B9_7F4A_7C15 } else { fp };
        let mut i = (fp as usize) & self.mask;
        loop {
            let k = self.keys[i];
            if k == 0 {
                self.keys[i] = fp;
                self.ids[i] = id;
                self.size += 1;
                return None;
            }
            if k == fp {
                return Some(self.ids[i]);
            }
            i = (i + 1) & self.mask;
        }
    }
    /// Whether `fp` is in the set.
    #[inline]
    pub fn contains(&self, fp: u64) -> bool {
        let fp = if fp == 0 { 0x9E37_79B9_7F4A_7C15 } else { fp };
        let mut i = (fp as usize) & self.mask;
        loop {
            let k = self.keys[i];
            if k == 0 {
                return false;
            }
            if k == fp {
                return true;
            }
            i = (i + 1) & self.mask;
        }
    }
    fn grow(&mut self) {
        let cap = self.keys.len() * 2;
        let ok = std::mem::replace(&mut self.keys, vec![0; cap]);
        let oi = std::mem::replace(&mut self.ids, vec![0; cap]);
        self.mask = cap - 1;
        for (j, &k) in ok.iter().enumerate() {
            if k == 0 {
                continue;
            }
            let mut i = (k as usize) & self.mask;
            while self.keys[i] != 0 {
                i = (i + 1) & self.mask;
            }
            self.keys[i] = k;
            self.ids[i] = oi[j];
        }
    }
}

// ---- state fingerprints ----
// A state's fingerprint is `fp_finish` of the sum (mod 2^64) of one term per variable; a term mixes the
// variable's index with the word of its value (`value_word`: content-based, cached inside composite values).
// Being a sum, the fingerprint of a successor is its parent's with the terms of the changed variables
// replaced, so unchanged variables cost one pointer comparison each.
#[inline]
fn mix64(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^ (x >> 31)
}
#[inline]
fn var_term(i: usize, word: u64) -> u64 {
    mix64(word ^ (i as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15))
}
#[inline]
fn fp_finish(sum: u64) -> u64 {
    mix64(sum ^ 0x243F_6A88_85A3_08D3)
}
fn fp_sum(vals: &[Value]) -> R<u64> {
    let mut sum = 0u64;
    for (i, v) in vals.iter().enumerate() {
        sum = sum.wrapping_add(var_term(i, value_word(v)?));
    }
    Ok(sum)
}
/// The two values are certainly equal: the same scalar or the same shared composite.
#[inline]
fn same_value(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Model(x), Value::Model(y)) => x == y,
        (Value::Tuple(x), Value::Tuple(y)) => Rc::ptr_eq(x, y),
        (Value::Record(x), Value::Record(y)) => Rc::ptr_eq(x, y),
        (Value::Fcn(x), Value::Fcn(y)) => Rc::ptr_eq(x, y),
        (Value::Set(x), Value::Set(y)) => Rc::ptr_eq(x, y),
        _ => false,
    }
}

/// The fingerprint terms of the variables of a state whose successors are being fingerprinted.
#[derive(Default)]
pub(crate) struct ParentTerms {
    term: Vec<u64>,
    sum: u64,
}

/// Where `successors_with` puts the successors it finds.
trait Sink {
    fn emit(&mut self, vals: &[Value], action: u32);
    fn mark(&self) -> usize;
    /// Forgets the successors emitted since `mark`.
    fn truncate(&mut self, mark: usize);
}
struct StateSink<'a> {
    out: &'a mut Vec<StateRef>,
    act: &'a mut Vec<u32>,
}
impl Sink for StateSink<'_> {
    fn emit(&mut self, vals: &[Value], action: u32) {
        self.out.push(StateData::new(vals.to_vec()));
        self.act.push(action);
    }
    fn mark(&self) -> usize {
        self.act.len()
    }
    fn truncate(&mut self, mark: usize) {
        self.out.truncate(mark);
        self.act.truncate(mark);
    }
}
struct RowSink<'a> {
    out: &'a mut Vec<Value>,
    act: &'a mut Vec<u32>,
    n: usize,
}
impl Sink for RowSink<'_> {
    fn emit(&mut self, vals: &[Value], action: u32) {
        self.out.extend_from_slice(vals);
        self.act.push(action);
    }
    fn mark(&self) -> usize {
        self.act.len()
    }
    fn truncate(&mut self, mark: usize) {
        self.out.truncate(mark * self.n);
        self.act.truncate(mark);
    }
}

/// Applies a model-value permutation; None when the value is unchanged.
/// `m` is a dense table indexed by string id (identity where the entry equals the index or is missing).
pub fn permute(v: &Value, m: &[u32]) -> R<Option<Value>> {
    fn all(vs: &[Value], m: &[u32]) -> R<Option<Vec<Value>>> {
        let mut out: Option<Vec<Value>> = None;
        for (i, x) in vs.iter().enumerate() {
            if let Some(y) = permute(x, m)? {
                let o = out.get_or_insert_with(|| vs.to_vec());
                o[i] = y;
            }
        }
        Ok(out)
    }
    Ok(match v {
        Value::Model(x) => match m.get(x.0 as usize) {
            Some(y) if *y != x.0 => Some(Value::Model(StrId(*y))),
            _ => None,
        },
        Value::Tuple(t) => all(t, m)?.map(|e| Value::Tuple(TupleV::rc(e))),
        Value::Record(r) => all(&r.vals, m)?.map(|vals| Value::Record(Rc::new(RecordV::new(r.names.clone(), vals)))),
        Value::Fcn(f) => {
            let d = all(&f.dom, m)?;
            let vs = all(&f.vals, m)?;
            match (d, vs) {
                (None, None) => None,
                (None, Some(vals)) => Some(Value::Fcn(Rc::new(FcnV::new(f.dom.clone(), vals)))),
                (Some(d), vs) => {
                    let vals = vs.unwrap_or_else(|| f.vals.clone());
                    Some(make_fcn_from_pairs(d.into_iter().zip(vals).collect())?)
                }
            }
        }
        Value::Set(s) => match &s.k {
            SetK::Interval(..) => None,
            _ => match all(s.elems()?, m)? {
                None => None,
                Some(e) => Some(mk_set(e)?),
            },
        },
        _ => None,
    })
}

pub struct Checker<'a> {
    pub model: &'a Model,
    pub ev: &'static Evaluator,
    pub opts: CheckOptions,
    pub states: Vec<StateRef>,
    pub parent: Vec<u32>,
    pub level: Vec<u32>,
    pub act: Vec<i32>,
    /// For every state, its index among the successors of its parent (for an initial state, among the
    /// states the initial predicate enumerates): the choice `rebuild` has to make again. Empty unless
    /// `drop_states`.
    pub(crate) ord: Vec<u32>,
    /// recorded graph: successor ids / actions per state (if record_graph)
    pub succ: Vec<Vec<u32>>,
    pub succ_act: Vec<Vec<u32>>,
    /// actual successor states per edge (only with VIEW/SYMMETRY + liveness)
    pub succ_state: Option<Vec<Vec<StateRef>>>,
    pub inits: Vec<u32>,
    pub(crate) fps: FpSet,
    pub generated: u64,
    pub init_generated: u64,
    pub init_distinct: u64,
    pub head: usize,
    pub depth: u32,
    nvars: usize,
    /// the symmetry permutations as dense tables indexed by string id
    perms: Vec<Vec<u32>>,
    /// memo of `permute` for compound values: (value hash, permutation index) -> (value, its image)
    perm_memo: std::cell::RefCell<std::collections::HashMap<(u64, u32), (Value, Option<Value>)>>,
    pub(crate) outdeg: Vec<u32>,
    pub(crate) cur_level: u32,
    /// Also the placeholder in `states` for a state that the parallel search holds in serialized form
    /// only (see `state_at`).
    pub(crate) empty: StateRef,
    /// Index of the first state of the next level while the search may still go parallel; usize::MAX otherwise.
    #[cfg_attr(target_arch = "wasm32", allow(dead_code))]
    pub(crate) level_end: usize,
    pub(crate) last_progress: f64,
    #[cfg_attr(target_arch = "wasm32", allow(dead_code))]
    pub(crate) t_start: f64,
    #[cfg(not(target_arch = "wasm32"))]
    pub(crate) par: Option<Box<crate::par::Par>>,
    /// Successors are kept as rows of a reusable buffer and a state is allocated only when its fingerprint
    /// is new. Possible when nothing but the fingerprint set looks at a generated state: no CONSTRAINT,
    /// ACTION_CONSTRAINT, VIEW, SYMMETRY, action property or recorded graph. EVERYSTATE_ENGINE=classic
    /// switches it off (every successor is then allocated before it is looked up).
    flat: bool,
    /// A state's values are dropped once its successors have been generated; only its fingerprint (`fps`),
    /// its parent, its level and its `ord` are kept, and `state_at` rebuilds the values from the initial
    /// states when a trace needs them (see `rebuild`). True in flat mode with one worker, where nothing
    /// but the search itself reads the values of a state it has finished with; `EVERYSTATE_RETAIN=all`
    /// turns it off.
    drop_states: bool,
    /// EVERYSTATE_EVAL=compiled: the compiled actions and invariants (see compile.rs)
    plans: Option<crate::compile::Plans>,
}

pub const NO_PARENT: u32 = u32::MAX;

/// EVERYSTATE_ENGINE=classic selects the code paths as they were before the data-layout work (for
/// differential testing: both settings must give identical results).
pub fn classic_engine() -> bool {
    matches!(std::env::var("EVERYSTATE_ENGINE").as_deref(), Ok("classic"))
}

/// EVERYSTATE_RETAIN=all keeps the values of every state (for differential testing, and for a
/// specification whose evaluation cannot be repeated: see `Checker::rebuild`).
pub fn retain_all() -> bool {
    matches!(std::env::var("EVERYSTATE_RETAIN").as_deref(), Ok("all"))
}

impl<'a> Checker<'a> {
    pub fn new(model: &'a Model, opts: CheckOptions) -> Checker<'a> {
        let ev = model.ev;
        let opts_record = opts.record_graph;
        let flat = !classic_engine()
            && !opts_record
            && model.constraints.is_empty()
            && model.action_constraints.is_empty()
            && model.implied_actions.is_empty()
            && model.view.is_none()
            && model.symmetry.is_none();
        // The parallel search keeps the states of a level in serialized form and rebuilds them with
        // `Par::load` (`par.rs`), so it is left out of the retention change.
        let sequential = opts.par.as_ref().map_or(true, |c| c.workers <= 1);
        ev.steps.enabled.set(std::env::var_os("EVERYSTATE_CACHE_STATS").is_some_and(|v| !v.is_empty() && v != "0"));
        ev.stats.active.set(true);
        ev.stats.check_deadlock.set(opts.check_deadlock);
        {
            // TLCGet("spec"): the structure of TLC's record, without coverage statistics (built on demand)
            type Item = (String, Loc, String);
            let root = model.root_name.clone();
            let preds = |ps: &[Pred]| -> Vec<Item> { ps.iter().map(|p| (p.name.clone(), p.e.loc, p.e.module_str().unwrap_or_else(|| root.clone()))).collect() };
            let cats: Vec<Vec<Item>> = vec![
                preds(&model.inits),
                model.actions.iter().map(|a| (a.name.clone(), a.loc, a.module.clone())).collect(),
                preds(&model.invariants),
                preds(&model.implied_inits),
                preds(&model.implied_actions),
                preds(&model.live_props),
                preds(&model.fairness),
                preds(&model.constraints),
                preds(&model.action_constraints),
                model.vars.iter().map(|v| (v.name.to_string(), [0; 4], v.module.to_string())).collect(),
            ];
            *ev.spec_info.borrow_mut() = Some(Box::new(move || {
                use crate::stdlib::js_names;
                let mut sets = vec![];
                for c in &cats {
                    let mut items = vec![];
                    for (nm, loc, module) in c {
                        let inner = make_record(
                            &js_names(&["beginLine", "beginColumn", "endLine", "endColumn", "module"]),
                            vec![Value::Int(loc[0] as i64), Value::Int(loc[1] as i64), Value::Int(loc[2] as i64), Value::Int(loc[3] as i64), Value::Str(str_id(module))],
                        );
                        items.push(make_record(&js_names(&["name", "location"]), vec![Value::Str(str_id(nm)), inner]));
                    }
                    sets.push(mk_set(items)?);
                }
                Ok(make_record(&js_names(&["inits", "actions", "invariants", "impliedinits", "impliedactions", "impliedtemporals", "temporals", "constraints", "actionconstraints", "variables"]), sets))
            }));
        }
        Checker {
            model,
            ev,
            opts,
            states: vec![],
            parent: vec![],
            level: vec![],
            act: vec![],
            ord: vec![],
            succ: vec![],
            succ_act: vec![],
            succ_state: None,
            inits: vec![],
            fps: FpSet::new(),
            generated: 0,
            init_generated: 0,
            init_distinct: 0,
            head: 0,
            depth: 0,
            nvars: model.vars.len(),
            perm_memo: Default::default(),
            perms: model.symmetry.as_ref().map_or(vec![], |sym| {
                sym.iter()
                    .map(|p| {
                        let n = p.keys().map(|k| k.0 as usize + 1).max().unwrap_or(0);
                        let mut t: Vec<u32> = (0..n as u32).collect();
                        for (a, b) in p {
                            t[a.0 as usize] = b.0;
                        }
                        t
                    })
                    .collect()
            }),
            outdeg: vec![],
            cur_level: 0,
            empty: StateData::blank(0),
            plans: if crate::compile::enabled() { Some(crate::compile::compile(model)) } else { None },
            flat,
            // Only the search itself reads the values of a state it has finished with, and only when
            // nothing reads the state graph after the search: a dump and a liveness check keep every
            // state (`record_graph`), and so does the parallel search, whose states exist as bytes
            // (`par.rs`).
            drop_states: sequential && !opts_record && !retain_all(),
            level_end: usize::MAX,
            last_progress: 0.0,
            t_start: 0.0,
            #[cfg(not(target_arch = "wasm32"))]
            par: None,
        }
    }

    /// State `i`. The states found by the parallel search are kept serialized and rebuilt on demand, and
    /// so are the states whose values were dropped (see `drop_states`).
    pub fn state_at(&self, i: usize) -> R<StateRef> {
        let s = &self.states[i];
        if Rc::ptr_eq(s, &self.empty) {
            #[cfg(not(target_arch = "wasm32"))]
            if let Some(p) = &self.par {
                return Ok(p.load(i, self.nvars));
            }
            return self.rebuild(i);
        }
        Ok(s.clone())
    }

    pub(crate) fn sync_stats(&self) {
        let st = &self.ev.stats;
        st.level.set(self.cur_level as i64);
        st.distinct.set(self.states.len() as i64);
        st.generated.set(self.generated as i64);
        st.queue.set(self.states.len() as i64 - self.head as i64);
        st.diameter.set(self.depth as i64);
    }
    pub(crate) fn set_level(&mut self, l: u32) {
        self.cur_level = l;
        self.ev.stats.level.set(l as i64);
    }

    /// `permute` with a memo: the same variable values (a set of messages, say) recur in many states, and
    /// permuting and re-sorting them once per permutation is what symmetry reduction costs.
    fn permute_memo(&self, v: &Value, p: &[u32], pi: u32) -> R<Option<Value>> {
        if !matches!(v, Value::Tuple(_) | Value::Record(_) | Value::Fcn(_) | Value::Set(_)) {
            return permute(v, p);
        }
        let mut h = Hasher::new();
        h.value(v)?;
        let key = (h.finish(), pi);
        if let Some((orig, img)) = self.perm_memo.borrow().get(&key) {
            // the hash only finds the entry; equality decides
            if matches!(val_eq(orig, v), Ok(true)) {
                return Ok(img.clone());
            }
        }
        let img = permute(v, p)?;
        let mut memo = self.perm_memo.borrow_mut();
        // bounded: the images are extra copies of state values
        if memo.len() >= 1 << 17 {
            memo.clear();
        }
        memo.insert(key, (v.clone(), img.clone()));
        Ok(img)
    }

    /// The values that identify a state: the VIEW value, or all variables, of the symmetry-canonical state.
    pub fn fingerprint_input(&self, s: &StateRef) -> R<Vec<Value>> {
        let m = self.model;
        let mut canon: Option<Vec<Value>> = None;
        if m.symmetry.is_some() {
            let base = s.snapshot(self.nvars);
            // Variables are compared cheapest first (by shallow size, which no permutation changes, so the
            // order is the same for every state of an orbit): most permutations are decided on a small
            // function and the big sets are never permuted. With a VIEW the declared order is kept.
            let mut order: Vec<usize> = (0..base.len()).collect();
            if m.view.is_none() {
                let weight = |v: &Value| -> usize {
                    match v {
                        Value::Tuple(t) => t.len(),
                        Value::Record(r) => r.vals.len(),
                        Value::Fcn(f) => f.dom.len(),
                        Value::Set(s) => match &s.k {
                            SetK::Enum(e) => e.len(),
                            _ => usize::MAX,
                        },
                        _ => 0,
                    }
                };
                order.sort_by_key(|&i| weight(&base[i]));
            }
            let mut u: Vec<Value> = Vec::new();
            for (pi, p) in self.perms.iter().enumerate() {
                // Lexicographic comparison with the best candidate so far, variable by variable: most
                // permutations lose early and the rest of the state is never permuted.
                u.clear();
                u.extend(base.iter().cloned());
                let mut wins = false;
                let mut lost = false;
                for &i in &order {
                    if let Some(x) = self.permute_memo(&base[i], p, pi as u32)? {
                        u[i] = x;
                    }
                    if !wins {
                        match compare(&u[i], &canon.as_ref().unwrap_or(&base)[i])? {
                            Ordering::Greater => {
                                lost = true;
                                break;
                            }
                            Ordering::Less => wins = true,
                            Ordering::Equal => {}
                        }
                    }
                }
                if wins && !lost {
                    canon = Some(std::mem::take(&mut u));
                }
            }
        }
        if let Some(view) = &m.view {
            let t = match canon {
                Some(c) => StateData::new(c),
                None => s.clone(),
            };
            self.ev.set_state(&t, None);
            self.ev.init_mode.set(false);
            return Ok(vec![self.ev.eval(view.e, &view.ctx)?]);
        }
        Ok(match canon {
            Some(c) => c,
            None => s.snapshot(self.nvars),
        })
    }

    pub fn fingerprint(&self, s: &StateRef) -> R<u64> {
        let sum = if self.model.symmetry.is_none() && self.model.view.is_none() { s.with(|vals| fp_sum(&vals[..self.nvars]))? } else { fp_sum(&self.fingerprint_input(s)?)? };
        Ok(fp_finish(sum))
    }

    /// Successors can be kept as rows and looked up before a state is built for them (see `flat`).
    pub(crate) fn is_flat(&self) -> bool {
        self.flat
    }
    /// The terms of `s`, for `row_fingerprint`. (The state was fingerprinted when it was found: the words
    /// of its values are cached.)
    pub(crate) fn parent_terms(&self, s: &StateRef, pt: &mut ParentTerms) -> R<()> {
        let nv = self.nvars;
        pt.term.resize(nv, 0);
        pt.sum = 0;
        s.with(|pv| {
            for k in 0..nv {
                pt.term[k] = var_term(k, value_word(&pv[k])?);
                pt.sum = pt.sum.wrapping_add(pt.term[k]);
            }
            Ok(())
        })
    }
    /// The fingerprint of a successor of `s` given as a row of variables (no VIEW, no SYMMETRY): the
    /// fingerprint of `s` with the terms of the changed variables replaced. Equal to `fingerprint` of the
    /// state with these variables.
    #[inline]
    pub(crate) fn row_fingerprint(&self, s: &StateRef, pt: &ParentTerms, row: &[Value]) -> R<u64> {
        s.with(|pv| {
            let mut sum = pt.sum;
            for k in 0..self.nvars {
                if !same_value(&row[k], &pv[k]) {
                    sum = sum.wrapping_sub(pt.term[k]).wrapping_add(var_term(k, value_word(&row[k])?));
                }
            }
            Ok(fp_finish(sum))
        })
    }

    pub fn result(&self, status: &'static str) -> CheckResult {
        CheckResult {
            status,
            name: None,
            message: None,
            trace: None,
            loop_to: None,
            loop_action: None,
            live_branches: 0,
            call_stack: None,
            code: None,
            generated: self.generated,
            distinct: self.states.len() as u64,
            queue: (self.states.len() - self.head.min(self.states.len())) as u64,
            depth: self.depth,
            init_generated: self.init_generated,
            init_distinct: self.init_distinct,
            print_summary: true,
            outdegree: self.outdegree(),
        }
    }
    pub fn error(&self, message: String, trace: Option<Vec<TraceStep>>) -> CheckResult {
        let mut r = self.result("error");
        r.message = Some(message);
        r.trace = trace;
        r
    }

    fn outdegree(&self) -> Option<Outdegree> {
        if self.outdeg.is_empty() {
            return None;
        }
        let mut d = self.outdeg.clone();
        d.sort_unstable();
        let sum: u64 = d.iter().map(|x| *x as u64).sum();
        let avg = (sum as f64 / d.len() as f64 + 0.5).floor() as u32;
        let p = ((d.len() as f64 * 0.95).ceil() as usize).saturating_sub(1).min(d.len() - 1);
        Some(Outdegree { min: d[0], avg, p95: d[p], max: d[d.len() - 1] })
    }

    /// The trace to `id`. `Err` is the result to report in its place: a state the trace passes through
    /// can no longer be rebuilt (see `rebuild`).
    pub fn trace_to(&self, id: usize) -> Result<Vec<TraceStep>, CheckResult> {
        let mut out = vec![];
        let mut i = id as u32;
        loop {
            let a = self.act[i as usize];
            let state = match self.state_at(i as usize) {
                Ok(s) => s,
                Err(e) => return Err(self.error(self.describe_err(&e, false), None)),
            };
            out.push(TraceStep { state, action: if a >= 0 { Some(a as usize) } else { None }, id: i as i64 });
            i = self.parent[i as usize];
            if i == NO_PARENT {
                break;
            }
        }
        out.reverse();
        Ok(out)
    }
    fn trace_plus(&self, sid: usize, t: &StateRef, a: usize, id: i64) -> Result<Vec<TraceStep>, CheckResult> {
        let mut tr = self.trace_to(sid)?;
        tr.push(TraceStep { state: t.clone(), action: Some(a), id });
        Ok(tr)
    }

    // ---- rebuilding a state whose values were dropped ----

    /// The values of state `id`, rebuilt by executing the chain of actions that led to it from the initial
    /// state it started at. Every state on the way is checked against the fingerprint the search stored for
    /// it, so a specification whose evaluation does not repeat (Print, TLCSet, TLCGet of a statistic,
    /// RandomElement) gives an error instead of a trace that names the wrong state.
    fn rebuild(&self, id: usize) -> R<StateRef> {
        let mut chain: Vec<usize> = vec![];
        let mut i = id;
        loop {
            chain.push(i);
            let p = self.parent[i];
            if p == NO_PARENT {
                break;
            }
            i = p as usize;
        }
        chain.reverse();
        let root = chain[0];
        let mut s = self.init_state_at(self.ord[root] as usize)?;
        self.check_rebuilt(&s, root)?;
        for &w in &chain[1..] {
            s = self.successor_at(&s, w)?;
        }
        Ok(s)
    }

    /// `s` is the state with id `id`: the fingerprint of `s` is the one the search stored under that id.
    /// (A fingerprint identifies a state, so this is the check that the rebuild reached the same state.)
    fn check_rebuilt(&self, s: &StateRef, id: usize) -> R<()> {
        let fp = self.fingerprint(s)?;
        if self.fps.get(fp) == Some(id as u32) {
            return Ok(());
        }
        let message = format!(
            "The counterexample trace cannot be shown: a state whose values were dropped (to save memory) was rebuilt from the initial states and came out different from the one the search found, so it is a different state ({} instead of state {}).\nThat happens when the evaluation of the specification depends on the order of exploration, through Print, TLCSet, a statistic read with TLCGet, or RandomElement. Re-run with EVERYSTATE_RETAIN=all, which keeps the values of every state.",
            fp, id
        );
        Err(Box::new(Fail::Check { status: "error", message }))
    }

    /// The `ord`-th state the initial predicate enumerates, in the enumeration order of the search.
    fn init_state_at(&self, ord: usize) -> R<StateRef> {
        // The enumeration runs to the end; only the wanted state is kept, so this costs one initial pass
        // and not a second copy of the initial states.
        let mut want: Option<StateRef> = None;
        self.enumerate_init_each(&mut |k, s| {
            if k == ord {
                want = Some(s);
            }
            Ok(())
        })?;
        match want {
            Some(s) => Ok(s),
            None => Err(Box::new(Fail::Check {
                status: "error",
                message: format!("The counterexample trace cannot be shown: the initial predicate enumerates fewer than {} states.", ord + 1),
            })),
        }
    }

    /// The successor of `s` that became state `id`: the `ord`-th state `s` generates, checked against the
    /// fingerprint of `id`.
    fn successor_at(&self, s: &StateRef, id: usize) -> R<StateRef> {
        // `ord` counts the successors `s` generates, before constraints are applied, which is what the
        // search counted too; `flat` picks the generator it counted them with.
        let nv = self.nvars;
        let mut rows: Vec<Value> = vec![];
        let mut succs: Vec<StateRef> = vec![];
        let mut acts: Vec<u32> = vec![];
        if self.flat {
            self.successors_flat(s, &mut rows, &mut acts)?;
        } else {
            self.successors(s, &mut succs, &mut acts)?;
        }
        let k = self.ord[id] as usize;
        if k >= acts.len() {
            return Err(Box::new(Fail::Check {
                status: "error",
                message: format!("The counterexample trace cannot be shown: the state before state {} generates {} successors now, not {}.", id, acts.len(), k + 1),
            }));
        }
        let t = if self.flat { StateData::new(rows[k * nv..(k + 1) * nv].to_vec()) } else { succs[k].clone() };
        self.check_rebuilt(&t, id)?;
        Ok(t)
    }

    pub fn eval_pred(&self, p: &Pred, s: &StateRef, t: Option<&StateRef>) -> R<bool> {
        self.eval_pred_at(p.e, &p.ctx, s, t)
    }
    pub fn eval_pred_at(&self, e: N, ctx: &C, s: &StateRef, t: Option<&StateRef>) -> R<bool> {
        let ev = self.ev;
        ev.set_state(s, t);
        ev.init_mode.set(false);
        ev.prime_depth.set(0);
        ev.call_depth.set(0);
        ev.n_assigned.set(0);
        ev.eval_bool(e, ctx)
    }

    /// Re-run a failing evaluation while recording the chain of nested expressions being evaluated.
    pub fn nested_expressions(&self, p: &Pred, s: &StateRef, t: Option<&StateRef>) -> String {
        let ev = self.ev;
        ev.trace_stack.borrow_mut().clear();
        ev.set_tracing(true);
        let _ = self.eval_pred(p, s, t);
        ev.set_tracing(false);
        let stack = std::mem::take(&mut *ev.trace_stack.borrow_mut());
        let mut lines: Vec<String> = vec![];
        let mut last: Option<N> = None;
        for n in stack {
            if std::ptr::eq(n, p.e) || last.map_or(false, |l| std::ptr::eq(l, n)) || n.loc[0] == 0 || matches!(n.e, E::Num(_) | E::Str(..)) {
                continue;
            }
            last = Some(n);
            lines.push(format!(
                "{}. Line {}, column {} to line {}, column {} in {}",
                lines.len(),
                n.loc[0],
                n.loc[1],
                n.loc[2],
                n.loc[3],
                n.module_str().unwrap_or_else(|| self.model.root_name.clone())
            ));
        }
        if lines.is_empty() { "    The error call stack is empty.\n".to_string() } else { lines.join("\n") + "\n" }
    }

    pub fn check_assumptions(&self) -> Option<CheckResult> {
        let ev = self.ev;
        for a in &self.model.root.assumes {
            if a.axiom {
                continue; // TLC does not evaluate AXIOMs
            }
            ev.set_state(&self.empty, None);
            ev.init_mode.set(false);
            let at = loc_str(&a.e.loc, &a.module.to_string());
            if std::env::var_os("EVERYSTATE_DEBUG_ASSUMES").is_some() {
                // debugging aid: report every failing assumption instead of stopping at the first
                if std::env::var("EVERYSTATE_DEBUG_ASSUMES").map_or(false, |v| v == "2") {
                    eprintln!("CHECK {}", at);
                }
                match ev.eval(a.e, &None) {
                    Ok(Value::Bool(true)) => {}
                    Ok(v) => eprintln!("ASSUME {}: {}", at, if matches!(v, Value::Bool(false)) { "FALSE" } else { "not boolean" }),
                    Err(e) => eprintln!("ASSUME {}: {}", at, self.describe_err(&e, false).replace('\n', " | ")),
                }
                continue;
            }
            match ev.eval(a.e, &None) {
                Err(e) => {
                    let mut r = match *e {
                        Fail::Tla(t) => self.error(format!("Evaluating assumption {} failed.\n{}", at, t.msg), None),
                        _ => self.error(format!("Evaluating assumption {} failed.", at), None),
                    };
                    r.code = Some(2105);
                    r.print_summary = false;
                    return Some(r);
                }
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    let mut r = self.result("assumption");
                    r.message = Some(format!("Assumption {} is false.", at));
                    r.print_summary = false;
                    return Some(r);
                }
                Ok(_) => {
                    let mut r = self.error(format!("The assumption {} was not a boolean.", at), None);
                    r.print_summary = false;
                    return Some(r);
                }
            }
        }
        None
    }

    pub fn describe_err(&self, e: &Fail, with_loc: bool) -> String {
        match e {
            Fail::Tla(t) => {
                if t.kind == "stack" {
                    return "Stack overflow while evaluating the specification (recursion too deep). Re-run with a larger stack.".into();
                }
                let mut m = t.msg.clone();
                if with_loc {
                    if let Some(l) = t.loc {
                        if l[0] > 0 {
                            m += &format!("\n(evaluating the expression at line {}, col {} to line {}, col {} of module {})", l[0], l[1], l[2], l[3], t.module.as_deref().unwrap_or("?"));
                        }
                    }
                }
                m
            }
            Fail::Found => "internal error: unexpected control flow".into(),
            Fail::Check { message, .. } => message.clone(),
        }
    }

    pub fn missing(&self, s: &StateData) -> Vec<String> {
        let mut v: Vec<String> = self.model.vars.iter().enumerate().filter(|(j, _)| s.is_undef(*j)).map(|(_, d)| d.name.to_string()).collect();
        v.sort();
        v
    }

    /// All states satisfying the initial predicate, in enumeration order (duplicates included).
    pub fn enumerate_init(&self) -> R<Vec<StateRef>> {
        let mut found: Vec<StateRef> = vec![];
        self.enumerate_init_each(&mut |_, s| {
            found.push(s);
            Ok(())
        })?;
        Ok(found)
    }

    /// The states satisfying the initial predicate, in enumeration order, given one at a time to `f` with
    /// the number of states it has seen before (`enumerate_init` when all of them are wanted).
    fn enumerate_init_each(&self, f: &mut dyn FnMut(usize, StateRef) -> R<()>) -> R<()> {
        let ev = self.ev;
        let nv = self.nvars;
        let buf = StateData::blank(nv);
        ev.set_state(&buf, None);
        ev.init_mode.set(true);
        ev.prime_depth.set(0);
        ev.n_assigned.set(0);
        fn go(ck: &Checker, preds: &[Pred], i: usize, buf: &StateRef, k: &mut usize, f: &mut dyn FnMut(usize, StateRef) -> R<()>) -> R<()> {
            if i == preds.len() {
                for j in 0..ck.nvars {
                    if buf.is_undef(j) {
                        let missing = ck.missing(buf);
                        let many = missing.len() > 1;
                        return Err(Box::new(Fail::Check {
                            status: "init-error",
                            message: format!(
                                "current state is not a legal state\nWhile working on the initial state:\nThe variable{} {} {} not assigned a value by the initial predicate.",
                                if many { "s" } else { "" },
                                missing.join(", "),
                                if many { "are" } else { "is" }
                            ),
                        }));
                    }
                }
                let n = *k;
                *k += 1;
                return f(n, StateData::new(buf.snapshot(ck.nvars)));
            }
            ck.ev.enumerate(preds[i].e, &preds[i].ctx, &mut || go(ck, preds, i + 1, buf, k, f))
        }
        let mut k = 0usize;
        let r = go(self, &self.model.inits, 0, &buf, &mut k, f);
        ev.init_mode.set(false);
        r
    }

    /// As `enumerate_init`, with a failure already turned into a result; no initial predicate gives no states.
    pub fn init_states(&self) -> Result<Vec<StateRef>, CheckResult> {
        if self.model.inits.is_empty() {
            return Ok(vec![]);
        }
        self.enumerate_init().map_err(|e| match *e {
            Fail::Check { status, message } => {
                let mut r = self.result(status);
                r.message = Some(message);
                r
            }
            ref other => self.error(self.describe_err(other, true), None),
        })
    }

    // Enumerate initial states.
    fn compute_init(&mut self, #[allow(unused_variables)] events: &mut dyn Events) -> Option<CheckResult> {
        let m = self.model;
        if m.inits.is_empty() {
            return None;
        }
        let found = match self.enumerate_init() {
            Ok(f) => f,
            Err(e) => {
                return Some(match *e {
                    Fail::Check { status, message } => {
                        let mut r = self.result(status);
                        r.message = Some(message);
                        r
                    }
                    ref other => self.error(self.describe_err(other, true), None),
                })
            }
        };
        self.set_level(1);
        // the workers may take the initial states up to one the sequential code has to look at
        #[cfg(not(target_arch = "wasm32"))]
        let skip = {
            let done = crate::par::init(self, &found, events);
            self.sync_stats();
            done
        };
        #[cfg(target_arch = "wasm32")]
        let skip = 0usize;
        for (k, s) in found.into_iter().enumerate().skip(skip) {
            self.generated += 1;
            self.init_generated += 1;
            let mut unseen = true;
            let mut id: i64 = -1;
            let step: R<()> = (|| {
                let mut in_model = true;
                for c in &m.constraints {
                    if !self.eval_pred(c, &s, None)? {
                        in_model = false;
                        break;
                    }
                }
                if in_model {
                    let fp = self.fingerprint(&s)?;
                    let nid = self.states.len();
                    id = nid as i64;
                    unseen = self.fps.put(fp, nid as u32).is_none();
                    if unseen {
                        self.states.push(s.clone());
                        self.parent.push(NO_PARENT);
                        self.level.push(1);
                        self.act.push(-1);
                        if self.drop_states {
                            self.ord.push(k as u32);
                        }
                        self.inits.push(nid as u32);
                        if self.opts.record_graph {
                            self.succ.push(vec![]);
                            self.succ_act.push(vec![]);
                            if let Some(ss) = &mut self.succ_state {
                                ss.push(vec![]);
                            }
                        }
                        self.depth = self.depth.max(1);
                        self.init_distinct += 1;
                    }
                }
                Ok(())
            })();
            self.sync_stats();
            let one = |id: i64| Some(vec![TraceStep { state: s.clone(), action: None, id }]);
            if let Err(e) = step {
                return Some(self.error(self.describe_err(&e, true), one(-1)));
            }
            if unseen {
                for inv in &m.invariants {
                    match self.eval_pred(inv, &s, None) {
                        Err(e) => {
                            let mut r = self.error(format!("Evaluating invariant {} failed.\n{}", inv.name, self.describe_err(&e, true)), one(-1));
                            r.code = Some(2111);
                            return Some(r);
                        }
                        Ok(false) => {
                            let mut r = self.result("invariant-init");
                            r.name = Some(inv.name.clone());
                            r.trace = one(id);
                            r.print_summary = false;
                            return Some(r);
                        }
                        Ok(true) => {}
                    }
                }
                for p in &m.implied_inits {
                    match self.eval_pred(p, &s, None) {
                        Err(e) => {
                            return Some(self.error(format!("Evaluating property {} failed.\n{}", p.name, self.describe_err(&e, true)), one(-1)));
                        }
                        Ok(false) => {
                            let mut r = self.result("implied-init");
                            r.name = Some(p.name.clone());
                            r.trace = one(id);
                            r.print_summary = false;
                            return Some(r);
                        }
                        Ok(true) => {}
                    }
                }
            }
        }
        None
    }

    // Successors of one state, as (state, action index) pairs in action order.
    pub fn successors(&self, s: &StateRef, out: &mut Vec<StateRef>, out_act: &mut Vec<u32>) -> R<()> {
        self.successors_with(s, &mut StateSink { out, act: out_act })
    }
    /// As `successors`, without allocating a state per successor: the variables of each successor are
    /// appended to `out` (`nvars` values per successor).
    pub(crate) fn successors_flat(&self, s: &StateRef, out: &mut Vec<Value>, out_act: &mut Vec<u32>) -> R<()> {
        self.successors_with(s, &mut RowSink { out, act: out_act, n: self.nvars })
    }
    fn successors_with(&self, s: &StateRef, sink: &mut dyn Sink) -> R<()> {
        if let Some(plans) = &self.plans {
            plans.tick();
        }
        let ev = self.ev;
        let m = self.model;
        let n = self.nvars;
        let actions = &m.actions;
        let mut nxt = StateData::blank(n);
        for (ai, a) in actions.iter().enumerate() {
            // The buffer is all-unassigned again after an enumeration; reuse it unless a lazy value kept a
            // reference to it (ours plus the evaluator's make two).
            if Rc::strong_count(&nxt) > 2 {
                nxt = StateData::blank(n);
            }
            ev.set_state(s, Some(&nxt));
            ev.init_mode.set(false);
            ev.prime_depth.set(0);
            ev.call_depth.set(0);
            ev.n_assigned.set(0);
            if let (Some(plans), false) = (&self.plans, ev.steps.enabled.get()) {
                let mark = sink.mark();
                let attempt = plans.run_action(ev, ai, s, &nxt, n, &mut || {
                    if !nxt.all_defined(n) {
                        // (the tree-walker, run again below, words the error)
                        return Err(Box::new(Fail::Check { status: "incomplete", message: String::new() }));
                    }
                    nxt.with(|v| sink.emit(&v[..n], ai as u32));
                    Ok(())
                });
                match attempt {
                    Some(Ok(())) => continue,
                    Some(Err(_)) => {
                        // The compiled attempt failed: forget what it produced and let the tree-walker
                        // evaluate the action from the start (it decides whether, and how, this is an error).
                        sink.truncate(mark);
                        nxt = StateData::blank(n);
                        ev.set_state(s, Some(&nxt));
                        ev.init_mode.set(false);
                        ev.prime_depth.set(0);
                        ev.call_depth.set(0);
                        ev.n_assigned.set(0);
                    }
                    None => {}
                }
            }
            let nxt = &nxt;
            let mut found = || {
                if !nxt.all_defined(n) {
                    let missing = self.missing(nxt);
                    let which = if actions.len() == 1 { "the next-state action".to_string() } else { format!("action {} of the next-state relation", a.name) };
                    return Err(Box::new(Fail::Check {
                        status: "incomplete",
                        message: format!(
                            "Successor state is not completely specified by {}. The following variable{} not defined: {}.",
                            which,
                            if missing.len() > 1 { "s are" } else { " is" },
                            missing.join(", ")
                        ),
                    }));
                }
                nxt.with(|v| sink.emit(&v[..n], ai as u32));
                Ok(())
            };
            if ev.steps.enabled.get() {
                ev.enumerate_units(ai, a.e, &a.ctx, &mut found)?;
            } else {
                ev.enumerate(a.e, &a.ctx, &mut found)?;
            }
        }
        Ok(())
    }

    /// An invariant in a state: compiled code when there is some and it succeeds, else the tree-walker.
    pub(crate) fn eval_invariant(&self, i: usize, s: &StateRef) -> R<bool> {
        if let Some(plans) = &self.plans {
            let ev = self.ev;
            ev.set_state(s, None);
            ev.init_mode.set(false);
            ev.prime_depth.set(0);
            ev.call_depth.set(0);
            ev.n_assigned.set(0);
            if let Some(b) = plans.run_invariant(ev, i, s, self.nvars) {
                return Ok(b);
            }
        }
        self.eval_pred(&self.model.invariants[i], s, None)
    }

    pub fn run(&mut self, events: &mut dyn Events) -> CheckResult {
        let r = self.search(events);
        #[cfg(not(target_arch = "wasm32"))]
        crate::par::finish(self);
        if self.ev.steps.enabled.get() {
            let m = self.model;
            let report = self.ev.steps.report(&|ai| format!("{}{}", m.actions[ai].name, m.actions[ai].params));
            eprint!("{}", report);
        }
        if let (Some(p), true) = (&self.plans, std::env::var_os("EVERYSTATE_EVAL_STATS").is_some()) {
            eprint!("{}", p.report());
        }
        r
    }

    fn search(&mut self, events: &mut dyn Events) -> CheckResult {
        let m = self.model;
        self.t_start = self.ev.host.borrow().now_ms();
        if let Some(r) = self.check_assumptions() {
            return r;
        }
        #[cfg(not(target_arch = "wasm32"))]
        crate::par::prepare(self);
        if let Some(r) = self.compute_init(events) {
            return r;
        }
        events.init_done(self.init_generated, self.init_distinct);
        let mut succs: Vec<StateRef> = vec![];
        let mut succ_act: Vec<u32> = vec![];
        let flat = self.flat;
        let nv = self.nvars;
        // flat mode: the variables of all successors of the current state, and the fingerprint terms of
        // the current state's variables
        let mut rows: Vec<Value> = vec![];
        let mut pterms = ParentTerms::default();
        let record = self.opts.record_graph;
        let ev = self.ev;
        self.last_progress = ev.host.borrow().now_ms();
        if m.inits.is_empty() {
            return self.result("ok");
        }
        if m.actions.is_empty() {
            let mut r = self.error("No next state actions defined to generate successor states from.".into(), None);
            r.code = Some(2115);
            r.print_summary = false;
            return r;
        }
        while self.head < self.states.len() && !ev.stats.stop_requested.get() {
            let sid = self.head;
            #[cfg(not(target_arch = "wasm32"))]
            if sid == self.level_end {
                // a level starts here: it is searched by the workers when that pays
                self.level_end = self.states.len();
                if crate::par::level(self, events) {
                    continue;
                }
            }
            self.head += 1;
            let s = self.states[sid].clone();
            let lvl = self.level[sid];
            self.cur_level = lvl;
            self.sync_stats();
            succs.clear();
            succ_act.clear();
            rows.clear();
            let generated = if flat { self.successors_flat(&s, &mut rows, &mut succ_act) } else { self.successors(&s, &mut succs, &mut succ_act) };
            if let Err(e) = generated {
                let trace = match self.trace_to(sid) {
                    Ok(t) => t,
                    Err(r) => return r,
                };
                return match *e {
                    Fail::Check { status, message } => {
                        let mut r = self.result(status);
                        r.message = Some(message);
                        r.trace = Some(trace);
                        r.queue = (self.states.len() - self.head) as u64;
                        r
                    }
                    ref other => self.error(self.describe_err(other, true), Some(trace)),
                };
            }
            let extra = ev.extra_generated.replace(0);
            self.generated += extra;
            let mut fresh = 0u32;
            if flat && !succ_act.is_empty() {
                if let Err(e) = self.parent_terms(&s, &mut pterms) {
                    let trace = match self.trace_to(sid) {
                        Ok(t) => t,
                        Err(r) => return r,
                    };
                    return self.error(self.describe_err(&e, true), Some(trace));
                }
            }
            for i in 0..succ_act.len() {
                let ai = succ_act[i] as usize;
                self.generated += 1;
                ev.stats.generated.set(self.generated as i64);
                let mut known_fp: Option<u64> = None;
                let t = if flat {
                    let row = &rows[i * nv..(i + 1) * nv];
                    match self.row_fingerprint(&s, &pterms, row) {
                        // seen before: nothing else looks at this successor, so no state is built for it
                        Ok(fp) if self.fps.contains(fp) => continue,
                        Ok(fp) => known_fp = Some(fp),
                        Err(_) => {} // reported below, as when every successor is a state
                    }
                    StateData::new(row.to_vec())
                } else {
                    succs[i].clone()
                };
                let mut in_model = true;
                let mut unseen = true;
                let mut id: i64 = -1;
                let step: R<()> = (|| {
                    self.set_level(lvl + 1);
                    for c in &m.constraints {
                        if !self.eval_pred(c, &t, None)? {
                            in_model = false;
                            break;
                        }
                    }
                    self.set_level(lvl);
                    if in_model {
                        for c in &m.action_constraints {
                            if !self.eval_pred(c, &s, Some(&t))? {
                                in_model = false;
                                break;
                            }
                        }
                    }
                    self.set_level(lvl + 1);
                    if in_model {
                        let fp = match known_fp {
                            Some(fp) => fp,
                            None => self.fingerprint(&t)?,
                        };
                        let nid = self.states.len();
                        match self.fps.put(fp, nid as u32) {
                            None => {
                                id = nid as i64;
                                self.states.push(t.clone());
                                self.parent.push(sid as u32);
                                self.level.push(lvl + 1);
                                self.act.push(ai as i32);
                                if self.drop_states {
                                    self.ord.push(i as u32);
                                }
                                if record {
                                    self.succ.push(vec![]);
                                    self.succ_act.push(vec![]);
                                    if let Some(ss) = &mut self.succ_state {
                                        ss.push(vec![]);
                                    }
                                }
                                if lvl + 1 > self.depth {
                                    self.depth = lvl + 1;
                                    ev.stats.diameter.set(self.depth as i64);
                                }
                                fresh += 1;
                                ev.stats.distinct.set(self.states.len() as i64);
                                ev.stats.queue.set(self.states.len() as i64 - self.head as i64);
                            }
                            Some(ex) => {
                                unseen = false;
                                id = ex as i64;
                            }
                        }
                        if record {
                            self.succ[sid].push(id as u32);
                            self.succ_act[sid].push(ai as u32);
                            if let Some(ss) = &mut self.succ_state {
                                ss[sid].push(t.clone());
                            }
                        }
                    }
                    Ok(())
                })();
                if let Err(e) = step {
                    let trace = match self.trace_plus(sid, &t, ai, -1) {
                        Ok(t) => t,
                        Err(r) => return r,
                    };
                    return self.error(self.describe_err(&e, true), Some(trace));
                }
                if unseen {
                    for (ii, inv) in m.invariants.iter().enumerate() {
                        match self.eval_invariant(ii, &t) {
                            Err(e) => {
                                let trace = match self.trace_plus(sid, &t, ai, id) {
                                    Ok(t) => t,
                                    Err(r) => return r,
                                };
                                let mut r = self.error(format!("Evaluating invariant {} failed.\n{}", inv.name, self.describe_err(&e, false)), Some(trace));
                                r.code = Some(2111);
                                if !in_model {
                                    r.call_stack = Some(self.nested_expressions(inv, &t, None));
                                }
                                if in_model {
                                    r.queue = r.queue.saturating_sub(1); // the new state has not been enqueued yet
                                }
                                return r;
                            }
                            Ok(false) => {
                                let mut r = self.result("invariant");
                                r.name = Some(inv.name.clone());
                                r.trace = Some(match self.trace_plus(sid, &t, ai, id) {
                                    Ok(t) => t,
                                    Err(r) => return r,
                                });
                                if in_model {
                                    r.queue = r.queue.saturating_sub(1);
                                }
                                return r;
                            }
                            Ok(true) => {}
                        }
                    }
                }
                self.set_level(lvl);
                for p in &m.implied_actions {
                    match self.eval_pred(p, &s, Some(&t)) {
                        Err(e) => {
                            let trace = match self.trace_plus(sid, &t, ai, id) {
                                Ok(t) => t,
                                Err(r) => return r,
                            };
                            return self.error(format!("Evaluating action property {} failed.\n{}", p.name, self.describe_err(&e, true)), Some(trace));
                        }
                        Ok(false) => {
                            let mut r = self.result("action-property");
                            r.name = Some(p.name.clone());
                            r.trace = Some(match self.trace_plus(sid, &t, ai, id) {
                                Ok(t) => t,
                                Err(r) => return r,
                            });
                            if in_model && unseen {
                                r.queue = r.queue.saturating_sub(1);
                            }
                            return r;
                        }
                        Ok(true) => {}
                    }
                }
            }
            self.outdeg.push(fresh);
            if succ_act.is_empty() && self.opts.check_deadlock {
                let mut r = self.result("deadlock");
                r.trace = Some(match self.trace_to(sid) {
                    Ok(t) => t,
                    Err(r) => return r,
                });
                return r;
            }
            if sid & 1023 == 0 {
                let now = ev.host.borrow().now_ms();
                if now - self.last_progress > 60000.0 {
                    self.last_progress = now;
                    events.progress(self.depth, self.generated, self.states.len() as u64, (self.states.len() - self.head) as u64);
                }
            }
            if self.drop_states {
                // The successors have been generated and their invariants checked: nothing reads this
                // state's values again except a trace, which rebuilds them from the initial states
                // (`state_at`). The fingerprint, the parent, the level and the ordinal are kept, so the
                // state keeps its identity and its place in the graph.
                self.states[sid] = self.empty.clone();
            }
        }
        self.sync_stats();
        self.result("ok")
    }
}
