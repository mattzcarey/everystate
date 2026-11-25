//! Parallel breadth-first search (`-workers N`).
//!
//! Values, the syntax tree and the evaluator are single-threaded (`Rc`, `Cell`), so the workers share
//! nothing but bytes: every worker thread builds its own copy of the model, and states cross threads
//! in a serialized form (string and model-value ids are process-wide, see `intern`).
//!
//! The search stays level-synchronised and its result is the one of the sequential search, state for
//! state. One level at a time:
//!
//! 1. The workers take chunks of the level in increasing order. For every state they compute the
//!    successors, constraints and fingerprints exactly as the sequential loop does, look the
//!    fingerprints up in the fingerprint set (frozen while the workers run), and evaluate the
//!    invariants of every successor that may be new. They report, per state and in successor order,
//!    the candidates for new states.
//! 2. The main thread merges the reports in state order: the first occurrence of a fingerprint gets the
//!    next state id, as in the sequential search, so ids, parents, counts, depth and the state graph
//!    are identical to a one-worker run.
//!
//! Whatever is not this plain path is not handled here at all. When a worker meets a violation, an
//! error, a deadlock, or an operator whose effect depends on the order of exploration (Print, TLCSet,
//! TLCGet of a register or a statistic, RandomElement, I/O, a string that does not exist yet ...), it
//! reports the position of that state and stops; the workers never print, write or decide anything.
//! The level is merged up to that state and the sequential loop of `Checker::search` takes over from
//! exactly there: it re-expands the state and reports what it finds, with its own code. After an
//! order-dependent operator it finishes the level, so that every such effect happens in the sequential
//! order, and the next level goes to (fresh) workers again; the third time the search stays sequential
//! and says so.
//!
//! The candidates for initial states are dealt with in the same way (`Par::init`).
//!
//! States found by a parallel level exist as bytes only; `Checker::state_at` rebuilds one for a trace,
//! and `finish` rebuilds all of them when the state graph is going to be read (`-dump`, liveness).
//!
//! Test hooks (environment): EVERYSTATE_PAR_MIN, EVERYSTATE_PAR_CHUNK (see `cli::par_config`) and
//! EVERYSTATE_PAR_DEBUG (a summary of what the workers did, on standard error).
use crate::checker::{Checker, Events, FpSet, ParConfig, NO_PARENT};
use crate::eval::{set_stack_limit, StateData, StateRef};
use crate::host::Host;
use crate::intern::*;
use crate::model::{build_model, Model};
use crate::value::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher as StdHasher};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Arc, RwLock};

// ---------- serialized values ----------
const T_FALSE: u8 = 0;
const T_TRUE: u8 = 1;
const T_INT: u8 = 2;
const T_STR: u8 = 3;
const T_MODEL: u8 = 4;
const T_TUPLE: u8 = 5;
const T_RECORD: u8 = 6;
const T_FCN: u8 = 7;
const T_ENUM: u8 = 8;
const T_INTERVAL: u8 = 9;
const T_SUBSET: u8 = 10;
const T_FCNSET: u8 = 11;
const T_RECSET: u8 = 12;
const T_CROSS: u8 = 13;
const T_SEQ: u8 = 14;
const T_INF: u8 = 15;
const T_ANY: u8 = 16;
const T_KSUBSET: u8 = 17;
const T_CUP: u8 = 18;
const T_CAP: u8 = 19;
const T_DIFF: u8 = 20;
const T_UNION: u8 = 21;

#[inline]
fn put_u(out: &mut Vec<u8>, mut x: u64) {
    while x >= 0x80 {
        out.push((x as u8) | 0x80);
        x >>= 7;
    }
    out.push(x as u8);
}
#[inline]
fn put_i(out: &mut Vec<u8>, x: i64) {
    put_u(out, ((x << 1) ^ (x >> 63)) as u64);
}
#[inline]
fn get_u(b: &[u8], pos: &mut usize) -> u64 {
    let mut x = 0u64;
    let mut shift = 0;
    loop {
        let c = b[*pos];
        *pos += 1;
        x |= ((c & 0x7f) as u64) << shift;
        if c < 0x80 {
            return x;
        }
        shift += 7;
    }
}
#[inline]
fn get_i(b: &[u8], pos: &mut usize) -> i64 {
    let u = get_u(b, pos);
    ((u >> 1) as i64) ^ -((u & 1) as i64)
}

/// Appends `v`; false when the value has no serialized form (an operator, a lazy function, a set
/// defined by a predicate), in which case `out` is left with a partial encoding.
fn ser_value(v: &Value, out: &mut Vec<u8>) -> bool {
    match v {
        Value::Bool(b) => out.push(if *b { T_TRUE } else { T_FALSE }),
        Value::Int(i) => {
            out.push(T_INT);
            put_i(out, *i);
        }
        Value::Str(s) => {
            out.push(T_STR);
            put_u(out, s.0 as u64);
        }
        Value::Model(s) => {
            out.push(T_MODEL);
            put_u(out, s.0 as u64);
        }
        Value::Tuple(t) => {
            out.push(T_TUPLE);
            put_u(out, t.len() as u64);
            for x in t.iter() {
                if !ser_value(x, out) {
                    return false;
                }
            }
        }
        Value::Record(r) => {
            out.push(T_RECORD);
            put_u(out, r.names.len() as u64);
            for n in r.names.iter() {
                put_u(out, n.0 as u64);
            }
            for x in &r.vals {
                if !ser_value(x, out) {
                    return false;
                }
            }
        }
        Value::Fcn(f) => {
            out.push(T_FCN);
            put_u(out, f.dom.len() as u64);
            // the domain is length-prefixed: the reader shares equal domains without decoding them again
            let mark = out.len();
            for x in f.dom.iter() {
                if !ser_value(x, out) {
                    return false;
                }
            }
            let len = out.len() - mark;
            let mut tmp = Vec::with_capacity(5);
            put_u(&mut tmp, len as u64);
            out.splice(mark..mark, tmp);
            for x in &f.vals {
                if !ser_value(x, out) {
                    return false;
                }
            }
        }
        Value::Set(s) => return ser_set(s, out),
        Value::Undef | Value::Closure(_) | Value::DefRef(_) | Value::LazyFcn(_) | Value::Thunk(_) => return false,
    }
    true
}
fn ser_set(s: &SetV, out: &mut Vec<u8>) -> bool {
    let all = |ss: &[Rc<SetV>], out: &mut Vec<u8>| ss.iter().all(|x| ser_set(x, out));
    match &s.k {
        SetK::Enum(e) => {
            out.push(T_ENUM);
            put_u(out, e.len() as u64);
            e.iter().all(|x| ser_value(x, out))
        }
        SetK::Interval(lo, hi) => {
            out.push(T_INTERVAL);
            put_i(out, *lo);
            put_i(out, *hi);
            true
        }
        SetK::Subset(b) => {
            out.push(T_SUBSET);
            ser_set(b, out)
        }
        SetK::FcnSet(d, r) => {
            out.push(T_FCNSET);
            ser_set(d, out) && ser_set(r, out)
        }
        SetK::RecSet(names, sets) => {
            out.push(T_RECSET);
            put_u(out, names.len() as u64);
            for n in names.iter() {
                put_u(out, n.0 as u64);
            }
            all(sets, out)
        }
        SetK::Cross(sets) => {
            out.push(T_CROSS);
            put_u(out, sets.len() as u64);
            all(sets, out)
        }
        SetK::Seq(b) => {
            out.push(T_SEQ);
            ser_set(b, out)
        }
        SetK::Inf(k) => {
            out.push(T_INF);
            out.push(*k as u8);
            true
        }
        SetK::Any => {
            out.push(T_ANY);
            true
        }
        SetK::KSubset(k, b) => {
            out.push(T_KSUBSET);
            put_i(out, *k);
            ser_set(b, out)
        }
        SetK::Cup(a, b) => {
            out.push(T_CUP);
            ser_set(a, out) && ser_set(b, out)
        }
        SetK::Cap(a, b) => {
            out.push(T_CAP);
            ser_set(a, out) && ser_set(b, out)
        }
        SetK::Diff(a, b) => {
            out.push(T_DIFF);
            ser_set(a, out) && ser_set(b, out)
        }
        SetK::Union(ss) => {
            out.push(T_UNION);
            put_u(out, ss.len() as u64);
            all(ss, out)
        }
        SetK::Filter(_) => false,
    }
}
/// Appends one variable: the length of its encoding, then the encoding.
fn ser_var(v: &Value, out: &mut Vec<u8>, tmp: &mut Vec<u8>) -> bool {
    match v {
        // scalars: one length byte, written in place
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) => {
            let mark = out.len();
            out.push(0);
            ser_value(v, out);
            out[mark] = (out.len() - mark - 1) as u8;
            true
        }
        _ => {
            tmp.clear();
            if !ser_value(v, tmp) {
                return false;
            }
            put_u(out, tmp.len() as u64);
            out.extend_from_slice(tmp);
            true
        }
    }
}
/// Appends the variables of a state; false when one of them cannot be serialized.
fn ser_state(s: &StateRef, nvars: usize, out: &mut Vec<u8>) -> bool {
    let mut tmp = Vec::new();
    s.with(|vals| vals[..nvars].iter().all(|v| ser_var(v, out, &mut tmp)))
}
/// The same value by identity: the variable was not touched between a state and its successor.
#[inline]
fn same_rc(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Tuple(x), Value::Tuple(y)) => Rc::ptr_eq(x, y),
        (Value::Record(x), Value::Record(y)) => Rc::ptr_eq(x, y),
        (Value::Fcn(x), Value::Fcn(y)) => Rc::ptr_eq(x, y),
        (Value::Set(x), Value::Set(y)) => Rc::ptr_eq(x, y),
        _ => false,
    }
}
/// `ser_state` for a successor `t` of the state `s` whose encoding is `sb` (variable `i` at `spans[i]`):
/// the variables that `t` shares with `s` are copied instead of encoded again.
fn ser_successor(t: &StateRef, s: &StateRef, sb: &[u8], spans: &[(usize, usize)], out: &mut Vec<u8>, tmp: &mut Vec<u8>) -> bool {
    t.with(|tv| ser_row(tv, s, sb, spans, out, tmp))
}
/// `ser_successor` for a successor given as a row of variables.
fn ser_row(tv: &[Value], s: &StateRef, sb: &[u8], spans: &[(usize, usize)], out: &mut Vec<u8>, tmp: &mut Vec<u8>) -> bool {
    {
        s.with(|sv| {
            for i in 0..spans.len() {
                if same_rc(&tv[i], &sv[i]) {
                    out.extend_from_slice(&sb[spans[i].0..spans[i].1]);
                } else if !ser_var(&tv[i], out, tmp) {
                    return false;
                }
            }
            true
        })
    }
}
/// Where the variables are in the encoding of a state (each span includes the length prefix).
fn var_spans(b: &[u8], nvars: usize, spans: &mut Vec<(usize, usize)>) {
    spans.clear();
    let mut pos = 0;
    for _ in 0..nvars {
        let start = pos;
        let len = get_u(b, &mut pos) as usize;
        pos += len;
        spans.push((start, pos));
    }
}

#[derive(Default, Clone, Copy)]
struct Fx(u64);
impl StdHasher for Fx {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for c in bytes.chunks(8) {
            let mut w = [0u8; 8];
            w[..c.len()].copy_from_slice(c);
            self.write_u64(u64::from_le_bytes(w));
        }
    }
    #[inline]
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    #[inline]
    fn write_u32(&mut self, x: u32) {
        self.write_u64(x as u64);
    }
    #[inline]
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}
type FxBuild = BuildHasherDefault<Fx>;

/// Rebuilds values. Record field lists and function domains are shared between the values of one
/// thread, as they are between the values the evaluator itself builds.
#[derive(Default)]
pub struct De {
    names: HashMap<Box<[StrId]>, Rc<Vec<StrId>>, FxBuild>,
    doms: HashMap<Box<[u8]>, Rc<Vec<Value>>, FxBuild>,
    scratch: Vec<StrId>,
}
impl De {
    fn names(&mut self, b: &[u8], pos: &mut usize, n: usize) -> Rc<Vec<StrId>> {
        self.scratch.clear();
        for _ in 0..n {
            self.scratch.push(StrId(get_u(b, pos) as u32));
        }
        if let Some(r) = self.names.get(&self.scratch[..]) {
            return r.clone();
        }
        let r = Rc::new(self.scratch.clone());
        self.names.insert(self.scratch.clone().into_boxed_slice(), r.clone());
        r
    }
    fn values(&mut self, b: &[u8], pos: &mut usize, n: usize) -> Vec<Value> {
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(self.value(b, pos));
        }
        out
    }
    fn sets(&mut self, b: &[u8], pos: &mut usize, n: usize) -> Vec<Rc<SetV>> {
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(self.set(b, pos));
        }
        out
    }
    fn value(&mut self, b: &[u8], pos: &mut usize) -> Value {
        let tag = b[*pos];
        *pos += 1;
        match tag {
            T_FALSE => Value::Bool(false),
            T_TRUE => Value::Bool(true),
            T_INT => Value::Int(get_i(b, pos)),
            T_STR => Value::Str(StrId(get_u(b, pos) as u32)),
            T_MODEL => Value::Model(StrId(get_u(b, pos) as u32)),
            T_TUPLE => {
                let n = get_u(b, pos) as usize;
                if n == 0 {
                    return empty_tuple();
                }
                Value::Tuple(TupleV::rc(self.values(b, pos, n)))
            }
            T_RECORD => {
                let n = get_u(b, pos) as usize;
                let names = self.names(b, pos, n);
                Value::Record(Rc::new(RecordV::new(names, self.values(b, pos, n))))
            }
            T_FCN => {
                let n = get_u(b, pos) as usize;
                let len = get_u(b, pos) as usize;
                let key = &b[*pos..*pos + len];
                let dom = match self.doms.get(key) {
                    Some(d) => {
                        *pos += len;
                        d.clone()
                    }
                    None => {
                        let key: Box<[u8]> = key.into();
                        let d = Rc::new(self.values(b, pos, n));
                        if self.doms.len() >= 1 << 16 {
                            self.doms.clear();
                        }
                        self.doms.insert(key, d.clone());
                        d
                    }
                };
                Value::Fcn(Rc::new(FcnV::new(dom, self.values(b, pos, n))))
            }
            _ => {
                *pos -= 1;
                Value::Set(self.set(b, pos))
            }
        }
    }
    fn set(&mut self, b: &[u8], pos: &mut usize) -> Rc<SetV> {
        let tag = b[*pos];
        *pos += 1;
        let k = match tag {
            T_ENUM => {
                let n = get_u(b, pos) as usize;
                SetK::Enum(self.values(b, pos, n))
            }
            T_INTERVAL => {
                let lo = get_i(b, pos);
                SetK::Interval(lo, get_i(b, pos))
            }
            T_SUBSET => SetK::Subset(self.set(b, pos)),
            T_FCNSET => {
                let d = self.set(b, pos);
                SetK::FcnSet(d, self.set(b, pos))
            }
            T_RECSET => {
                let n = get_u(b, pos) as usize;
                let names = self.names(b, pos, n);
                SetK::RecSet(names, self.sets(b, pos, n))
            }
            T_CROSS => {
                let n = get_u(b, pos) as usize;
                SetK::Cross(self.sets(b, pos, n))
            }
            T_SEQ => SetK::Seq(self.set(b, pos)),
            T_INF => {
                let k = b[*pos];
                *pos += 1;
                SetK::Inf(match k {
                    0 => Inf::Nat,
                    1 => Inf::Int,
                    2 => Inf::Real,
                    _ => Inf::String,
                })
            }
            T_ANY => SetK::Any,
            T_KSUBSET => {
                let k = get_i(b, pos);
                SetK::KSubset(k, self.set(b, pos))
            }
            T_CUP | T_CAP | T_DIFF => {
                let x = self.set(b, pos);
                let y = self.set(b, pos);
                match tag {
                    T_CUP => SetK::Cup(x, y),
                    T_CAP => SetK::Cap(x, y),
                    _ => SetK::Diff(x, y),
                }
            }
            T_UNION => {
                let n = get_u(b, pos) as usize;
                SetK::Union(self.sets(b, pos, n))
            }
            t => panic!("corrupt serialized state (tag {})", t),
        };
        Rc::new(SetV::new(k))
    }
    pub fn state(&mut self, b: &[u8], nvars: usize) -> StateRef {
        let mut pos = 0;
        let mut vals = Vec::with_capacity(nvars);
        for _ in 0..nvars {
            // (a cache of whole variables keyed by their encoding was tried here: slower than decoding)
            let _len = get_u(b, &mut pos);
            vals.push(self.value(b, &mut pos));
        }
        debug_assert_eq!(pos, b.len());
        StateData::new(vals)
    }
}

/// Consecutive states in serialized form: state `base + i` is `bytes[offs[i]..offs[i + 1]]`.
pub struct Batch {
    base: usize,
    offs: Vec<usize>,
    bytes: Vec<u8>,
}
impl Batch {
    fn new(base: usize) -> Batch {
        Batch { base, offs: vec![0], bytes: Vec::new() }
    }
    fn len(&self) -> usize {
        self.offs.len() - 1
    }
    fn get(&self, i: usize) -> &[u8] {
        &self.bytes[self.offs[i]..self.offs[i + 1]]
    }
}

// ---------- the workers ----------
const CAND: u8 = 0; // not in the fingerprint set, first occurrence in this worker: carries the state
const DUP: u8 = 1; // seen earlier in this level by the same worker
const SEEN: u8 = 2; // in the fingerprint set (a state of an earlier level): `fp` holds its id

/// One successor that the merge has to know about.
struct Ent {
    fp: u64,
    act: u32,
    kind: u8,
    /// length of its serialized state in `ChunkOut::bytes` (0 = not sent)
    len: u32,
}
enum Event {
    /// a violation, an error or a deadlock: the sequential search reports it
    Check,
    /// the state cannot be expanded by a worker; the reason
    Fallback(String),
}
/// What a worker reports for the states `start .. start + done` of a level.
struct ChunkOut {
    start: usize,
    done: usize,
    /// what stopped the worker at state `start + done`
    event: Option<Event>,
    /// per state: generated successors, number of entries in `ent`
    src: Vec<(u64, u32)>,
    ent: Vec<Ent>,
    bytes: Vec<u8>,
}
struct Job {
    /// the states are the candidates for initial states, not a level
    init: bool,
    frontier: Arc<Batch>,
    lvl: u32,
    chunk: usize,
    next: AtomicUsize,
    /// smallest position at which a worker stopped; states behind it are not expanded
    stop: AtomicUsize,
    fps: Arc<RwLock<FpSet>>,
}
enum ToWorker {
    Level(Arc<Job>),
    Exit,
}
enum FromWorker {
    Ready(Result<(), String>),
    Chunk(ChunkOut),
    Done,
}
#[derive(Clone, Copy)]
struct Flags {
    check_deadlock: bool,
    /// the merge needs every edge of the state graph (`-dump`, liveness)
    record: bool,
    /// ... and the successor states themselves (liveness under VIEW or SYMMETRY)
    keep_states: bool,
}

/// The host of a worker's evaluator: nothing may be read from or written to the outside by a worker.
struct GuardHost;
const IO: &str = "an operator that prints or does input/output";
impl Host for GuardHost {
    fn read_file(&self, path: &str) -> Result<Vec<u8>, String> {
        worker_impure(IO);
        Err(path.to_string())
    }
    fn write_file(&self, path: &str, _: &[u8]) -> Result<(), String> {
        worker_impure(IO);
        Err(path.to_string())
    }
    fn append_file(&self, path: &str, _: &[u8]) -> Result<(), String> {
        worker_impure(IO);
        Err(path.to_string())
    }
    fn exists(&self, _: &str) -> bool {
        worker_impure(IO);
        false
    }
    fn env(&self) -> Vec<(String, String)> {
        worker_impure(IO);
        vec![]
    }
    fn exec(&self, _: &[String], _: Option<&[(String, String)]>) -> Result<(i32, String, String), String> {
        worker_impure(IO);
        Err("not available".into())
    }
    fn print(&self, _: &str) {
        worker_impure(IO);
    }
    fn now_ms(&self) -> f64 {
        worker_impure("the clock");
        0.0
    }
}

/// The recipe by which a worker thread builds its own copy of the model: the configuration text and
/// the module sources the main thread read.
pub fn model_factory(root_name: String, cfg_text: String, sources: Vec<(String, String)>) -> Arc<dyn Fn() -> R<Model> + Send + Sync> {
    let sources = Arc::new(sources);
    Arc::new(move || {
        let cfg = crate::cfg::parse_config(&cfg_text)?;
        let src = sources.clone();
        let resolve: crate::modules::SourceResolver = Box::new(move |name: &str| src.iter().find(|(n, _)| n == name).map(|(_, t)| t.clone()));
        build_model(&root_name, resolve, &cfg, Rc::new(GuardHost))
    })
}

const STACK: usize = 1 << 30;
const UNSENDABLE: &str = "a state holds a value that cannot be passed between workers (a set defined by a predicate, or an operator)";

fn worker_main(factory: Arc<dyn Fn() -> R<Model> + Send + Sync>, flags: Flags, rx: Receiver<ToWorker>, tx: Sender<FromWorker>) {
    set_stack_limit(STACK - (64 << 20));
    set_worker(true);
    let model = match factory() {
        Ok(m) => m,
        Err(_) => {
            let _ = tx.send(FromWorker::Ready(Err("a worker could not load the specification".into())));
            return;
        }
    };
    let ck = Checker::new(&model, crate::checker::CheckOptions { check_deadlock: flags.check_deadlock, record_graph: false, par: None });
    if let Some(what) = take_impure() {
        let _ = tx.send(FromWorker::Ready(Err(format!("loading the specification uses {}", what))));
        return;
    }
    if tx.send(FromWorker::Ready(Ok(()))).is_err() {
        return;
    }
    let mut de = De::default();
    let mut succs: Vec<StateRef> = vec![];
    let mut acts: Vec<u32> = vec![];
    let mut scratch = Scratch::default();
    let nvars = model.vars.len();
    while let Ok(ToWorker::Level(job)) = rx.recv() {
        // fingerprints this worker has met in this level
        let mut local = FpSet::with_capacity(1 << 10);
        {
            let fps = job.fps.read().unwrap_or_else(|e| e.into_inner());
            let n = job.frontier.len();
            loop {
                let start = job.next.fetch_add(1, Ordering::Relaxed).saturating_mul(job.chunk);
                if start >= n || start > job.stop.load(Ordering::Relaxed) {
                    break;
                }
                let end = (start + job.chunk).min(n);
                let mut out = ChunkOut { start, done: 0, event: None, src: Vec::with_capacity(end - start), ent: vec![], bytes: vec![] };
                for i in start..end {
                    if i > job.stop.load(Ordering::Relaxed) {
                        break;
                    }
                    let sb = job.frontier.get(i);
                    let s = de.state(sb, nvars);
                    let mark = (out.ent.len(), out.bytes.len());
                    let mut event = if job.init { expand_init(&ck, &s, &mut local, &mut out) } else { expand(&ck, &s, sb, job.lvl, &fps, &mut local, &mut out, &mut succs, &mut acts, flags, &mut scratch) };
                    // an order-dependent operator decides, whatever else happened to the evaluation
                    if let Some(what) = take_impure() {
                        event = Some(Event::Fallback(format!("the specification uses {}", what)));
                    }
                    if let Some(e) = event {
                        out.ent.truncate(mark.0);
                        out.bytes.truncate(mark.1);
                        ck.ev.extra_generated.set(0);
                        job.stop.fetch_min(i, Ordering::Relaxed);
                        out.event = Some(e);
                        break;
                    }
                    out.done += 1;
                }
                if tx.send(FromWorker::Chunk(out)).is_err() {
                    return;
                }
            }
        }
        drop(job);
        if tx.send(FromWorker::Done).is_err() {
            return;
        }
    }
    // the process is about to end or goes on without this thread: nothing here is worth tearing down
    std::mem::forget(ck);
    std::mem::forget(model);
}

/// Expands one state as the sequential loop does (same evaluations in the same order, same TLCGet("level")),
/// without its bookkeeping. Some(..) when the state has to go to the sequential search instead.
#[allow(clippy::too_many_arguments)]
fn expand(ck: &Checker, s: &StateRef, sb: &[u8], lvl: u32, fps: &FpSet, local: &mut FpSet, out: &mut ChunkOut, succs: &mut Vec<StateRef>, acts: &mut Vec<u32>, flags: Flags, scratch: &mut Scratch) -> Option<Event> {
    let m = ck.model;
    let ev = ck.ev;
    let level = &ev.stats.level;
    level.set(lvl as i64);
    succs.clear();
    acts.clear();
    if ck.is_flat() && !flags.record {
        // As the sequential loop in flat mode: the successors are rows of a buffer, their fingerprints
        // are the parent's with the changed variables replaced, and a state is built (for the
        // invariants) only for a successor that may be new. There are no constraints and no action
        // properties in this mode.
        let nv = ck.model.vars.len();
        scratch.rows.clear();
        if ck.successors_flat(s, &mut scratch.rows, acts).is_err() {
            return Some(Event::Check);
        }
        let extra = ev.extra_generated.replace(0);
        let first = out.ent.len();
        var_spans(sb, nv, &mut scratch.spans);
        if !acts.is_empty() && ck.parent_terms(s, &mut scratch.terms).is_err() {
            return Some(Event::Check);
        }
        for i in 0..acts.len() {
            let row = &scratch.rows[i * nv..(i + 1) * nv];
            level.set(lvl as i64 + 1);
            let fp = match ck.row_fingerprint(s, &scratch.terms, row) {
                Ok(fp) => fp,
                Err(_) => return Some(Event::Check),
            };
            let candidate = fps.get(fp).is_none() && local.put(fp, 0).is_none();
            if candidate {
                let mark = out.bytes.len();
                if !ser_row(row, s, sb, &scratch.spans, &mut out.bytes, &mut scratch.tmp) {
                    return Some(Event::Fallback(UNSENDABLE.into()));
                }
                out.ent.push(Ent { fp, act: acts[i], kind: CAND, len: (out.bytes.len() - mark) as u32 });
                if !m.invariants.is_empty() {
                    let t = StateData::new(row.to_vec());
                    if !matches!(ck.eval_invariants(&t), Ok(None)) {
                        return Some(Event::Check);
                    }
                }
            }
            level.set(lvl as i64);
        }
        if acts.is_empty() && flags.check_deadlock {
            return Some(Event::Check);
        }
        out.src.push((acts.len() as u64 + extra, (out.ent.len() - first) as u32));
        return None;
    }
    if ck.successors(s, succs, acts).is_err() {
        return Some(Event::Check);
    }
    let extra = ev.extra_generated.replace(0);
    let first = out.ent.len();
    var_spans(sb, ck.model.vars.len(), &mut scratch.spans);
    for i in 0..succs.len() {
        let t = &succs[i];
        let act = acts[i];
        let fp: R<Option<u64>> = (|| {
            level.set(lvl as i64 + 1);
            for c in &m.constraints {
                if !ck.eval_pred(c, t, None)? {
                    return Ok(None);
                }
            }
            level.set(lvl as i64);
            for c in &m.action_constraints {
                if !ck.eval_pred(c, s, Some(t))? {
                    level.set(lvl as i64 + 1);
                    return Ok(None);
                }
            }
            level.set(lvl as i64 + 1);
            Ok(Some(ck.fingerprint(t)?))
        })();
        let fp = match fp {
            Ok(fp) => fp,
            Err(_) => return Some(Event::Check),
        };
        let mut unseen = true;
        if let Some(fp) = fp {
            let (kind, word) = match fps.get(fp) {
                Some(id) => (SEEN, id as u64),
                None => match local.put(fp, 0) {
                    Some(_) => (DUP, fp),
                    None => (CAND, fp),
                },
            };
            unseen = kind == CAND;
            if kind == CAND || flags.record {
                let mark = out.bytes.len();
                if (kind == CAND || flags.keep_states) && !ser_successor(t, s, sb, &scratch.spans, &mut out.bytes, &mut scratch.tmp) {
                    return Some(Event::Fallback(UNSENDABLE.into()));
                }
                out.ent.push(Ent { fp: word, act, kind, len: (out.bytes.len() - mark) as u32 });
            }
        }
        if unseen && !matches!(ck.eval_invariants(t), Ok(None)) {
            return Some(Event::Check);
        }
        level.set(lvl as i64);
        for p in &m.implied_actions {
            if !matches!(ck.eval_pred(p, s, Some(t)), Ok(true)) {
                return Some(Event::Check);
            }
        }
    }
    if succs.is_empty() && flags.check_deadlock {
        return Some(Event::Check);
    }
    out.src.push((succs.len() as u64 + extra, (out.ent.len() - first) as u32));
    None
}

/// The same for a candidate initial state: constraints, fingerprint, invariants and implied initial
/// predicates, as in `Checker::compute_init`.
fn expand_init(ck: &Checker, s: &StateRef, local: &mut FpSet, out: &mut ChunkOut) -> Option<Event> {
    let m = ck.model;
    ck.ev.stats.level.set(1);
    let fp: R<Option<u64>> = (|| {
        for c in &m.constraints {
            if !ck.eval_pred(c, s, None)? {
                return Ok(None);
            }
        }
        Ok(Some(ck.fingerprint(s)?))
    })();
    let fp = match fp {
        Ok(fp) => fp,
        Err(_) => return Some(Event::Check),
    };
    let mut unseen = true;
    if let Some(fp) = fp {
        unseen = local.put(fp, 0).is_none();
        if unseen {
            // the merge takes the state itself from the level
            out.ent.push(Ent { fp, act: 0, kind: CAND, len: 0 });
        }
    }
    if unseen {
        for p in m.invariants.iter().chain(m.implied_inits.iter()) {
            if !matches!(ck.eval_pred(p, s, None), Ok(true)) {
                return Some(Event::Check);
            }
        }
    }
    out.src.push((1, (fp.is_some() && unseen) as u32));
    None
}

#[derive(Default)]
struct Scratch {
    spans: Vec<(usize, usize)>,
    tmp: Vec<u8>,
    /// flat mode: the variables of the successors of the state being expanded, and its fingerprint terms
    rows: Vec<Value>,
    terms: crate::checker::ParentTerms,
}

struct Engine {
    txs: Vec<Sender<ToWorker>>,
    rx: Receiver<FromWorker>,
    fps: Arc<RwLock<FpSet>>,
}
impl Engine {
    fn start(cfg: &ParConfig, flags: Flags) -> Result<Engine, String> {
        let (tx, rx) = channel::<FromWorker>();
        let mut txs = vec![];
        for i in 0..cfg.workers {
            let (wtx, wrx) = channel::<ToWorker>();
            let (factory, tx) = (cfg.factory.clone(), tx.clone());
            let spawned = std::thread::Builder::new().name(format!("worker-{}", i + 1)).stack_size(STACK).spawn(move || worker_main(factory, flags, wrx, tx));
            if spawned.is_err() {
                return Err("a worker thread could not be started".into());
            }
            txs.push(wtx);
        }
        drop(tx);
        let eng = Engine { txs, rx, fps: Arc::new(RwLock::new(FpSet::with_capacity(2))) };
        let mut failure = None;
        for _ in 0..cfg.workers {
            match eng.rx.recv() {
                Ok(FromWorker::Ready(Ok(()))) => {}
                Ok(FromWorker::Ready(Err(why))) => failure = Some(why),
                _ => failure = Some("a worker thread stopped unexpectedly".to_string()),
            }
        }
        match failure {
            Some(why) => Err(why), // dropping the engine tells the workers to leave
            None => Ok(eng),
        }
    }
    /// Has the workers expand a level; the reports sorted by position, and where they stopped.
    fn run(&mut self, init: bool, frontier: Arc<Batch>, lvl: u32, chunk: usize) -> (Vec<ChunkOut>, usize) {
        let job = Arc::new(Job { init, frontier, lvl, chunk, next: AtomicUsize::new(0), stop: AtomicUsize::new(usize::MAX), fps: self.fps.clone() });
        for tx in &self.txs {
            tx.send(ToWorker::Level(job.clone())).expect("a worker thread stopped unexpectedly");
        }
        let mut chunks = vec![];
        let mut done = 0;
        while done < self.txs.len() {
            match self.rx.recv().expect("a worker thread stopped unexpectedly") {
                FromWorker::Chunk(c) => chunks.push(c),
                FromWorker::Done => done += 1,
                FromWorker::Ready(_) => {}
            }
        }
        chunks.sort_by_key(|c| c.start);
        (chunks, job.stop.load(Ordering::Relaxed))
    }
}
impl Drop for Engine {
    fn drop(&mut self) {
        for tx in &self.txs {
            let _ = tx.send(ToWorker::Exit);
        }
    }
}

// ---------- the main thread ----------
/// The parallel side of a `Checker`.
pub struct Par {
    cfg: ParConfig,
    engine: Option<Engine>,
    /// the states found by parallel levels, by ascending first id
    store: Vec<Arc<Batch>>,
    /// the states the last parallel level found: the next level, already serialized
    next: Option<Arc<Batch>>,
    de: RefCell<De>,
    t0: f64,
    off: bool,
    /// how often a level went back to the sequential search because of an order-dependent operator
    strikes: u32,
    /// for EVERYSTATE_PAR_DEBUG: levels and states searched by the workers, and why they stopped
    stats: (u64, u64, Option<String>),
    /// milliseconds: before the first parallel level, in the workers, in the merge
    times: (f64, f64, f64),
}

/// Called once before the search loop.
pub fn prepare(ck: &mut Checker) {
    if let Some(cfg) = ck.opts.par.clone() {
        if cfg.workers > 1 {
            let t0 = ck.t_start;
            ck.par = Some(Box::new(Par { cfg, engine: None, store: vec![], next: None, de: RefCell::new(De::default()), t0, off: false, strikes: 0, stats: (0, 0, None), times: (0.0, 0.0, 0.0) }));
            ck.level_end = ck.head;
        }
    }
}

/// Called with the candidates for initial states, before any of them is looked at. Returns how many of
/// them (from the first) the workers have dealt with; the sequential code goes on with the rest.
pub fn init(ck: &mut Checker, found: &[StateRef], events: &mut dyn Events) -> usize {
    match ck.par.take() {
        Some(mut par) => {
            let done = par.init(ck, found, events);
            ck.par = Some(par);
            done
        }
        None => 0,
    }
}

/// Called at the first state of every level. True when the level (or its beginning, up to a state the
/// sequential search has to look at) was searched by the workers; `ck.head` has moved accordingly.
pub fn level(ck: &mut Checker, events: &mut dyn Events) -> bool {
    let mut par = match ck.par.take() {
        Some(p) => p,
        None => {
            ck.level_end = usize::MAX;
            return false;
        }
    };
    let r = par.level(ck, events);
    if par.off {
        ck.level_end = usize::MAX;
    }
    ck.par = Some(par);
    r
}

/// Called when the search is over: the workers leave, and the states are rebuilt when the caller will
/// read them all (`-dump`, liveness).
pub fn finish(ck: &mut Checker) {
    if let Some(mut par) = ck.par.take() {
        if std::env::var_os("EVERYSTATE_PAR_DEBUG").is_some() {
            // Linux: CPU time of this thread and of all threads, in ms (the workers are still alive)
            let cpu = |path: &std::path::Path| std::fs::read_to_string(path).ok().and_then(|t| t.split_whitespace().next().and_then(|x| x.parse::<f64>().ok())).unwrap_or(0.0) / 1e6;
            let main = cpu(std::path::Path::new("/proc/thread-self/schedstat"));
            let all: f64 = std::fs::read_dir("/proc/self/task").map(|d| d.flatten().map(|e| cpu(&e.path().join("schedstat"))).sum()).unwrap_or(0.0);
            eprintln!("par cpu: {:.0} ms main thread, {:.0} ms other threads", main, all - main);
            eprintln!("par: {} levels, {} of {} states expanded by workers, {} handed back{}", par.stats.0, par.stats.1, ck.head, par.strikes, par.stats.2.as_ref().map_or(String::new(), |w| format!("; stopped: {}", w)));
            eprintln!("par times: {:.0} ms before, {:.0} ms workers, {:.0} ms merge, {:.0} ms total", par.times.0, par.times.1, par.times.2, ck.ev.host.borrow().now_ms() - par.t0);
        }
        par.engine = None;
        if ck.opts.record_graph {
            par.materialize(ck, 0);
            par.store = vec![];
        }
        ck.par = Some(par);
    }
}

impl Par {
    /// State `i`, which the parallel search found.
    pub fn load(&self, i: usize, nvars: usize) -> StateRef {
        let k = self.store.partition_point(|b| b.base <= i) - 1;
        let b = &self.store[k];
        self.de.borrow_mut().state(b.get(i - b.base), nvars)
    }
    /// Rebuilds the states from `from` on that exist in serialized form only.
    fn materialize(&mut self, ck: &mut Checker, from: usize) {
        for i in from..ck.states.len() {
            if Rc::ptr_eq(&ck.states[i], &ck.empty) {
                ck.states[i] = self.load(i, ck.model.vars.len());
            }
        }
    }
    /// From here on the search is sequential.
    fn give_up(&mut self, ck: &mut Checker, events: &mut dyn Events, why: &str) {
        self.off = true;
        self.engine = None;
        self.next = None;
        self.materialize(ck, ck.head);
        self.stats.2 = Some(why.to_string());
        events.note(&format!("The search continues with 1 worker instead of {}: {}.", self.cfg.workers, why));
    }

    /// A worker met a state that only the sequential search may expand (an operator whose effect depends
    /// on the order of exploration, a value that cannot be passed on). The sequential search finishes
    /// this level from that state on, which keeps every such effect in its sequential order; the next
    /// level goes to the workers again. They are replaced, because the abandoned evaluation may have left
    /// something behind in their evaluators. The third time is the last.
    fn strike(&mut self, ck: &mut Checker, events: &mut dyn Events, why: &str) {
        self.strikes += 1;
        if self.strikes >= 3 {
            return self.give_up(ck, events, why);
        }
        self.engine = None;
        self.next = None;
        self.materialize(ck, ck.head);
    }

    /// Whether `n` states are worth handing to the workers; starts them when they are.
    fn ready(&mut self, ck: &mut Checker, events: &mut dyn Events, n: usize) -> bool {
        if !self.off && crate::eval::WORKERS.load(Ordering::Relaxed) < 2 {
            self.give_up(ck, events, "the specification reads TLCGet(\"config\")");
        }
        if self.off || n < self.cfg.min_frontier || !(self.cfg.eager || ck.ev.host.borrow().now_ms() - self.t0 >= 50.0) {
            return false;
        }
        if self.engine.is_none() {
            let flags = Flags { check_deadlock: ck.opts.check_deadlock, record: ck.opts.record_graph, keep_states: ck.succ_state.is_some() };
            match Engine::start(&self.cfg, flags) {
                Ok(e) => self.engine = Some(e),
                Err(why) => {
                    self.give_up(ck, events, &why);
                    return false;
                }
            }
        }
        true
    }
    fn chunk(&self, n: usize) -> usize {
        if self.cfg.chunk > 0 { self.cfg.chunk } else { (n / (self.cfg.workers * 8)).clamp(1, 256) }
    }

    fn init(&mut self, ck: &mut Checker, cands: &[StateRef], events: &mut dyn Events) -> usize {
        let n = cands.len();
        let nvars = ck.model.vars.len();
        if !self.ready(ck, events, n) {
            return 0;
        }
        let mut f = Batch::new(0);
        for s in cands {
            if !ser_state(s, nvars, &mut f.bytes) {
                self.give_up(ck, events, UNSENDABLE);
                return 0;
            }
            f.offs.push(f.bytes.len());
        }
        let frontier = Arc::new(f);
        let t1 = ck.ev.host.borrow().now_ms();
        if self.stats.0 == 0 && self.times.0 == 0.0 {
            self.times.0 = t1 - self.t0;
        }
        let chunk = self.chunk(n);
        let eng = self.engine.as_mut().unwrap();
        std::mem::swap(&mut ck.fps, &mut *eng.fps.write().unwrap_or_else(|e| e.into_inner()));
        let (chunks, stop) = eng.run(true, frontier.clone(), 1, chunk);
        let eng = self.engine.as_mut().unwrap();
        std::mem::swap(&mut ck.fps, &mut *eng.fps.write().unwrap_or_else(|e| e.into_inner()));
        let t2 = ck.ev.host.borrow().now_ms();
        self.times.1 += t2 - t1;
        let p = stop.min(n);
        let record = ck.opts.record_graph;
        let mut found = Batch::new(ck.states.len());
        let mut pos = 0;
        let mut event: Option<Event> = None;
        for c in chunks {
            if c.start + c.done == p && c.event.is_some() {
                event = c.event;
            }
            if c.start >= p {
                continue;
            }
            assert_eq!(c.start, pos, "parallel search: a part of the initial states is missing");
            let upto = c.done.min(p - c.start);
            let mut ei = 0;
            for k in 0..upto {
                ck.generated += 1;
                ck.init_generated += 1;
                if c.src[k].1 == 0 {
                    continue;
                }
                let e = &c.ent[ei];
                ei += 1;
                let nid = ck.states.len() as u32;
                if ck.fps.put(e.fp, nid).is_none() {
                    ck.states.push(ck.empty.clone());
                    ck.parent.push(NO_PARENT);
                    ck.level.push(1);
                    ck.act.push(-1);
                    ck.inits.push(nid);
                    if record {
                        ck.succ.push(vec![]);
                        ck.succ_act.push(vec![]);
                        if let Some(ss) = &mut ck.succ_state {
                            ss.push(vec![]);
                        }
                    }
                    ck.depth = ck.depth.max(1);
                    ck.init_distinct += 1;
                    found.bytes.extend_from_slice(frontier.get(c.start + k));
                    found.offs.push(found.bytes.len());
                }
            }
            pos += upto;
        }
        assert_eq!(pos, p, "parallel search: a part of the initial states is missing");
        self.stats.1 += p as u64;
        self.times.2 += ck.ev.host.borrow().now_ms() - t2;
        if found.len() > 0 {
            let found = Arc::new(found);
            self.store.push(found.clone());
            if p == n {
                self.next = Some(found);
            }
        }
        if p < n {
            match event {
                Some(Event::Fallback(why)) => self.strike(ck, events, &why),
                _ => {
                    self.off = true;
                    self.engine = None;
                    self.next = None;
                    self.materialize(ck, 0);
                    self.stats.2 = Some("violation or error".into());
                }
            }
        }
        p
    }

    fn level(&mut self, ck: &mut Checker, events: &mut dyn Events) -> bool {
        let (a, b) = (ck.head, ck.states.len());
        let n = b - a;
        let nvars = ck.model.vars.len();
        if !self.ready(ck, events, n) {
            // this level is searched sequentially
            self.next = None;
            self.materialize(ck, a);
            return false;
        }
        let frontier = match self.next.take() {
            Some(f) if f.base == a && f.len() == n => f,
            _ => {
                let mut f = Batch::new(a);
                for i in a..b {
                    if !ser_state(&ck.states[i], nvars, &mut f.bytes) {
                        self.give_up(ck, events, UNSENDABLE);
                        return false;
                    }
                    f.offs.push(f.bytes.len());
                }
                Arc::new(f)
            }
        };
        let lvl = ck.level[a];
        let chunk = self.chunk(n);
        let t1 = ck.ev.host.borrow().now_ms();
        if self.stats.0 == 0 && self.times.0 == 0.0 {
            self.times.0 = t1 - self.t0;
        }
        let eng = self.engine.as_mut().unwrap();
        // the workers read the fingerprint set while they run; nobody writes
        std::mem::swap(&mut ck.fps, &mut *eng.fps.write().unwrap_or_else(|e| e.into_inner()));
        let (chunks, stop) = eng.run(false, frontier, lvl, chunk);
        let eng = self.engine.as_mut().unwrap();
        std::mem::swap(&mut ck.fps, &mut *eng.fps.write().unwrap_or_else(|e| e.into_inner()));

        let t2 = ck.ev.host.borrow().now_ms();
        self.times.1 += t2 - t1;
        // merge, in state order, everything before the first state a worker stopped at
        let p = stop.min(n);
        let record = ck.opts.record_graph;
        let mut found = Batch::new(b);
        let mut pos = 0;
        let mut event: Option<Event> = None;
        for c in chunks {
            if c.start + c.done == p && c.event.is_some() {
                event = c.event;
            }
            if c.start >= p {
                continue;
            }
            assert_eq!(c.start, pos, "parallel search: a part of the level is missing");
            let upto = c.done.min(p - c.start);
            let (mut ei, mut boff) = (0, 0);
            for k in 0..upto {
                let sid = a + c.start + k;
                let (generated, entries) = c.src[k];
                ck.generated += generated;
                let mut fresh = 0u32;
                for _ in 0..entries {
                    let e = &c.ent[ei];
                    ei += 1;
                    let bytes = &c.bytes[boff..boff + e.len as usize];
                    boff += e.len as usize;
                    let id = match e.kind {
                        CAND => {
                            let nid = ck.states.len() as u32;
                            match ck.fps.put(e.fp, nid) {
                                None => {
                                    ck.states.push(ck.empty.clone());
                                    ck.parent.push(sid as u32);
                                    ck.level.push(lvl + 1);
                                    ck.act.push(e.act as i32);
                                    if record {
                                        ck.succ.push(vec![]);
                                        ck.succ_act.push(vec![]);
                                        if let Some(ss) = &mut ck.succ_state {
                                            ss.push(vec![]);
                                        }
                                    }
                                    found.bytes.extend_from_slice(bytes);
                                    found.offs.push(found.bytes.len());
                                    fresh += 1;
                                    nid
                                }
                                Some(ex) => ex,
                            }
                        }
                        DUP => ck.fps.get(e.fp).expect("parallel search: a duplicate without its original"),
                        _ => e.fp as u32,
                    };
                    if record {
                        ck.succ[sid].push(id);
                        ck.succ_act[sid].push(e.act);
                        if let Some(ss) = &mut ck.succ_state {
                            ss[sid].push(self.de.borrow_mut().state(bytes, nvars));
                        }
                    }
                }
                ck.outdeg.push(fresh);
            }
            pos += upto;
        }
        assert_eq!(pos, p, "parallel search: a part of the level is missing");
        debug_assert!(NO_PARENT as usize > ck.states.len());
        ck.head = a + p;
        ck.cur_level = lvl;
        self.stats.0 += 1;
        self.stats.1 += p as u64;
        self.times.2 += ck.ev.host.borrow().now_ms() - t2;
        let complete = p == n;
        if found.len() > 0 {
            ck.depth = ck.depth.max(lvl + 1);
            let found = Arc::new(found);
            self.store.push(found.clone());
            if complete {
                self.next = Some(found);
            }
        }
        if !complete {
            match event {
                Some(Event::Fallback(why)) => self.strike(ck, events, &why),
                _ => {
                    // the sequential search re-expands state `head` and reports what the worker met
                    self.off = true;
                    self.engine = None;
                    self.next = None;
                    self.materialize(ck, ck.head);
                    self.stats.2 = Some("violation or error".into());
                }
            }
            return true;
        }
        let now = ck.ev.host.borrow().now_ms();
        if now - ck.last_progress > 60000.0 {
            ck.last_progress = now;
            events.progress(ck.depth, ck.generated, ck.states.len() as u64, (ck.states.len() - ck.head) as u64);
        }
        true
    }
}
