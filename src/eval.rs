//! Expression evaluator and action (next-state / initial-state) enumerator. Port of eval.ts.
use crate::ast::*;
use crate::intern::*;
use crate::modules::{BFn, Builtin, Decl, Def};
use crate::value::*;
use std::cell::{Cell, RefCell, UnsafeCell};
use std::collections::HashMap;
use std::rc::Rc;

// ---------- states ----------
thread_local! {
    static NEXT_STATE_ID: Cell<u64> = const { Cell::new(2) };
    static EV: Cell<Option<&'static Evaluator>> = const { Cell::new(None) };
    static STACK_BASE: Cell<usize> = const { Cell::new(0) };
    static STACK_LIMIT: Cell<usize> = const { Cell::new(usize::MAX) };
}
const ANY: u64 = 1;

/// A (possibly partial) assignment of values to variables. `Undef` marks an unassigned variable.
/// Interior mutability is confined to `get`/`set`, which never hand out references.
pub struct StateData {
    pub id: u64,
    vals: UnsafeCell<Vec<Value>>,
}
pub type StateRef = Rc<StateData>;
impl StateData {
    pub fn new(vals: Vec<Value>) -> StateRef {
        let id = NEXT_STATE_ID.with(|c| {
            let v = c.get();
            c.set(v + 1);
            v
        });
        Rc::new(StateData { id, vals: UnsafeCell::new(vals) })
    }
    pub fn blank(n: usize) -> StateRef {
        StateData::new(vec![Value::Undef; n])
    }
    #[inline]
    pub fn get(&self, i: usize) -> Value {
        // SAFETY: single-threaded; the reference does not outlive this call and `clone` cannot re-enter.
        let v = unsafe { &*self.vals.get() };
        match v.get(i) {
            Some(x) => x.clone(),
            None => Value::Undef,
        }
    }
    #[inline]
    pub fn is_undef(&self, i: usize) -> bool {
        let v = unsafe { &*self.vals.get() };
        !matches!(v.get(i), Some(x) if !matches!(x, Value::Undef))
    }
    #[inline]
    pub fn set(&self, i: usize, val: Value) {
        let old;
        {
            // SAFETY: as above; the old value is dropped after the borrow ends.
            let v = unsafe { &mut *self.vals.get() };
            if i >= v.len() {
                v.resize(i + 1, Value::Undef);
            }
            old = std::mem::replace(&mut v[i], val);
        }
        drop(old);
    }
    /// Every listed variable is unassigned here and assigned in `src`.
    #[inline]
    pub fn can_fill(&self, src: &StateData, idxs: &[u32]) -> bool {
        // SAFETY: as in `get`: shared reads that do not outlive this call.
        let (d, s) = unsafe { (&*self.vals.get(), &*src.vals.get()) };
        idxs.iter().all(|&i| {
            let i = i as usize;
            i < d.len() && i < s.len() && matches!(d[i], Value::Undef) && !matches!(s[i], Value::Undef)
        })
    }
    /// Copies the listed variables from `src` (after `can_fill`: the slots written are unassigned, so no
    /// value is dropped while the vector is borrowed, and `src` is another state).
    #[inline]
    pub fn fill(&self, src: &StateData, idxs: &[u32]) {
        debug_assert!(!std::ptr::eq(self, src));
        // SAFETY: single-threaded; `self` and `src` are different states, `clone` cannot re-enter.
        let (d, s) = unsafe { (&mut *self.vals.get(), &*src.vals.get()) };
        for &i in idxs {
            d[i as usize] = s[i as usize].clone();
        }
    }
    /// All of the first `n` variables are assigned.
    #[inline]
    pub fn all_defined(&self, n: usize) -> bool {
        let v = unsafe { &*self.vals.get() };
        v.len() >= n && v[..n].iter().all(|x| !matches!(x, Value::Undef))
    }
    /// Resets variable `i` to unassigned.
    #[inline]
    pub fn clear(&self, i: usize) {
        let old;
        {
            // SAFETY: as in `set`.
            let v = unsafe { &mut *self.vals.get() };
            old = std::mem::replace(&mut v[i], Value::Undef);
        }
        drop(old);
    }
    pub fn snapshot(&self, n: usize) -> Vec<Value> {
        let v = unsafe { &*self.vals.get() };
        v[..n].to_vec()
    }
    #[inline]
    pub fn with<T>(&self, f: impl FnOnce(&[Value]) -> T) -> T {
        f(unsafe { &*self.vals.get() })
    }
}

// ---------- contexts ----------
pub type C = Option<Rc<Ctx>>;
pub enum Bind {
    Val(Value),
    /// zero-argument LET definition: evaluated in the context of its LET group
    LetLazy { body: N, v: RefCell<Value>, st: Cell<u64>, d: &'static DefNode },
    LetOp(&'static DefNode),
    LetInst(&'static Def),
}
pub struct Ctx {
    pub name: Name,
    pub val: Bind,
    pub next: C,
    /// head of the enclosing instance environment (substitutions), or None at the root
    pub base: C,
    pub env: bool,      // this node belongs to an instance environment
    pub let_head: bool, // last binding of a LET group
}

#[inline]
pub fn base_of(ctx: &C) -> C {
    match ctx {
        None => None,
        Some(c) => {
            if c.env {
                Some(c.clone())
            } else {
                c.base.clone()
            }
        }
    }
}
#[inline]
pub fn cons(name: Name, val: Value, next: &C) -> C {
    Some(Rc::new(Ctx { name, val: Bind::Val(val), base: base_of(next), next: next.clone(), env: false, let_head: false }))
}

/// A delayed expression (operator argument, instance substitution).
pub struct Lazy {
    pub e: N,
    pub ctx: C,
    v: RefCell<Value>,
    st: Cell<u64>, // state the cached value is valid for; ANY = constant
}
impl Lazy {
    pub fn new(e: N, ctx: C) -> Value {
        Value::Thunk(Rc::new(Lazy { e, ctx, v: RefCell::new(Value::Undef), st: Cell::new(0) }))
    }
}

pub struct Closure {
    pub params: &'static [Param],
    pub body: N,
    pub ctx: C,
    pub name: Name,
}
pub struct DefRef {
    pub def: &'static Def,
    pub base: C,
}

/// A lazily evaluated function (recursive function definitions, functions over non-enumerable domains).
pub struct LazyFcn {
    pub node: N,
    pub ctx: C, // without the binding of the function's own name (added per application)
    memo: Rc<RefCell<HashMap<u64, Vec<(Value, Value)>>>>,
    forced: RefCell<Option<Value>>,
    /// [f EXCEPT ![k] = v] on a function that is not enumerated: later entries win
    over: Vec<(Value, Value)>,
    /// the evaluated domain sets, one per bound (TLC evaluates them when it creates the function value)
    doms: RefCell<Option<Rc<Vec<Rc<SetV>>>>>,
}

struct FnParts {
    bounds: &'static [Bound],
    body: N,
    recname: Option<Name>,
}
fn fn_parts(n: N) -> FnParts {
    match &n.e {
        E::FnDef { bounds, body, recname, .. } => FnParts { bounds, body, recname: *recname },
        _ => unreachable!(),
    }
}

impl LazyFcn {
    fn self_ctx(self: &Rc<Self>) -> C {
        match fn_parts(self.node).recname {
            Some(rn) => cons(rn, Value::LazyFcn(self.clone()), &self.ctx),
            None => self.ctx.clone(),
        }
    }
    pub fn body(&self) -> N {
        fn_parts(self.node).body
    }
    pub fn bind(self: &Rc<Self>, ev: &Evaluator, arg: &Value) -> R<C> {
        let p = fn_parts(self.node);
        let bounds = p.bounds;
        let sc = self.self_ctx();
        let mut c = sc.clone();
        let not_in = || -> R<C> { eval_err(format!("Attempted to apply function to argument {}, which is not in the domain of the function.", fmt(arg))) };
        let cached = self.doms.borrow().clone();
        let doms = match cached {
            Some(d) => d,
            None => {
                let mut d = Vec::with_capacity(bounds.len());
                for b in bounds {
                    d.push(ev.eval_set(b.set.as_ref().unwrap(), &sc)?);
                }
                let d = Rc::new(d);
                // a lazy set keeps the context it was built in, which for a recursive function holds the
                // function itself: do not close that cycle
                if p.recname.is_none() || !d.iter().any(|x| captures_ctx(&Value::Set(x.clone()))) {
                    *self.doms.borrow_mut() = Some(d.clone());
                }
                d
            }
        };
        let one = bounds.len() == 1 && (bounds[0].tuple.is_some() || bounds[0].names.as_ref().unwrap().len() == 1);
        if one {
            let b = &bounds[0];
            let s = &doms[0];
            if !s.contains(arg)? {
                return eval_err(format!("In applying the function\n{},\nthe first argument is:\n{}\nwhich is not in its domain.\n", self.show(ev), crate::pprint::ppr(&fmt(arg))));
            }
            c = match &b.tuple {
                Some(t) => ev.bind_tuple(t, arg, &c)?,
                None => cons(b.names.as_ref().unwrap()[0], arg.clone(), &c),
            };
        } else {
            let t = match arg {
                Value::Tuple(t) => t,
                _ => return not_in(),
            };
            let mut i = 0;
            for (bi, b) in bounds.iter().enumerate() {
                let s = &doms[bi];
                let cnt = if b.tuple.is_some() { 1 } else { b.names.as_ref().unwrap().len() };
                for j in 0..cnt {
                    let a = match t.get(i) {
                        Some(a) => a,
                        None => return not_in(),
                    };
                    i += 1;
                    if !s.contains(a)? {
                        return not_in();
                    }
                    c = match &b.tuple {
                        Some(tp) => ev.bind_tuple(tp, a, &c)?,
                        None => cons(b.names.as_ref().unwrap()[j], a.clone(), &c),
                    };
                }
            }
            if i != t.len() {
                return not_in();
            }
        }
        Ok(c)
    }
    pub fn new(node: N, ctx: C) -> Rc<LazyFcn> {
        Rc::new(LazyFcn { node, ctx, memo: Rc::new(RefCell::new(HashMap::new())), forced: RefCell::new(None), over: Vec::new(), doms: RefCell::new(None) })
    }
    fn is_rec(&self) -> bool {
        matches!(&self.node.e, E::FnDef { is_rec, .. } if is_rec.get())
    }
    pub fn show(self: &Rc<Self>, ev: &Evaluator) -> String {
        match self.force(ev) {
            Ok(Value::LazyFcn(_)) => "<lazy function>".to_string(),
            Ok(f) => crate::pprint::ppr(&fmt(&f)),
            Err(e) if matches!(*e, Fail::Tla(_)) => "<lazy function>".to_string(),
            Err(_) => "<lazy function>".to_string(),
        }
    }
    pub fn with_override(self: &Rc<Self>, key: Value, val: Value) -> Rc<LazyFcn> {
        let mut over = self.over.clone();
        over.push((key, val));
        Rc::new(LazyFcn { node: self.node, ctx: self.ctx.clone(), memo: self.memo.clone(), forced: RefCell::new(None), over, doms: RefCell::new(self.doms.borrow().clone()) })
    }
    /// `lazy`: the caller keeps a function-valued result unevaluated (it is applied right away)
    pub fn apply(self: &Rc<Self>, ev: &Evaluator, arg: &Value, lazy: bool) -> R<Value> {
        for (k, v) in self.over.iter().rev() {
            if val_eq(k, arg)? {
                return Ok(v.clone());
            }
        }
        // The memo is what makes recursive function definitions (fib[n]) linear; a function that is not
        // recursive is evaluated at each application, as in TLC.
        let key = if self.is_rec() {
            let mut h = Hasher::new();
            if h.value(arg).is_ok() { Some(h.finish()) } else { None }
        } else {
            None
        };
        if let Some(k) = key {
            if let Some(bucket) = self.memo.borrow().get(&k) {
                for (a, v) in bucket {
                    if matches!(val_eq(a, arg), Ok(true)) {
                        return Ok(v.clone());
                    }
                }
            }
        }
        check_stack()?;
        let c = self.bind(ev, arg)?;
        let (s0, p0) = (ev.st_touch.get(), ev.pr_touch.get());
        // like TLC, the body of a recursive function is evaluated in keep-lazy mode
        let v = if lazy || self.is_rec() { ev.eval_lazy(self.body(), &c)? } else { ev.eval(self.body(), &c)? };
        if let Some(k) = key {
            if ev.st_touch.get() == s0 && ev.pr_touch.get() == p0 {
                self.memo.borrow_mut().entry(k).or_default().push((arg.clone(), v.clone()));
            }
        }
        Ok(v)
    }
    pub fn domain(self: &Rc<Self>, ev: &Evaluator) -> R<Rc<SetV>> {
        let p = fn_parts(self.node);
        let sc = self.self_ctx();
        let mut sets: Vec<Rc<SetV>> = vec![];
        for b in p.bounds {
            let s = ev.eval_set(b.set.as_ref().unwrap(), &sc)?;
            let cnt = if b.tuple.is_some() { 1 } else { b.names.as_ref().unwrap().len() };
            for _ in 0..cnt {
                sets.push(s.clone());
            }
        }
        Ok(if sets.len() == 1 { sets.pop().unwrap() } else { Rc::new(SetV::new(SetK::Cross(sets))) })
    }
    /// The enumerated function, or the lazy function itself when its domain cannot be enumerated.
    pub fn force(self: &Rc<Self>, ev: &Evaluator) -> R<Value> {
        if let Some(f) = self.forced.borrow().as_ref() {
            return Ok(f.clone());
        }
        let (s0, p0) = (ev.st_touch.get(), ev.pr_touch.get());
        let d = self.domain(ev)?;
        if !d.enumerable() {
            return Ok(Value::LazyFcn(self.clone())); // stays lazy: only application and EXCEPT are possible
        }
        let dom = d.elems()?;
        let mut vals = Vec::with_capacity(dom.len());
        for x in dom {
            let v = self.apply(ev, x, false)?;
            vals.push(match &v {
                Value::LazyFcn(f) => f.force(ev)?,
                _ => v,
            });
        }
        let f = make_fcn(dom, vals);
        if ev.st_touch.get() == s0 && ev.pr_touch.get() == p0 {
            *self.forced.borrow_mut() = Some(f.clone());
        }
        Ok(f)
    }
}

pub fn set_stack_limit(bytes: usize) {
    let x = 0u8;
    STACK_BASE.with(|c| c.set(&x as *const u8 as usize));
    STACK_LIMIT.with(|c| c.set(bytes));
}
#[inline]
pub fn check_stack() -> R<()> {
    let x = 0u8;
    let here = &x as *const u8 as usize;
    let used = STACK_BASE.with(|c| c.get()).wrapping_sub(here);
    if used > STACK_LIMIT.with(|c| c.get()) {
        return err("stack", "Stack overflow while evaluating the specification (recursion too deep). Re-run with a larger stack.".into());
    }
    Ok(())
}

fn captures_ctx(v: &Value) -> bool {
    fn set(s: &SetV) -> bool {
        match &s.k {
            SetK::Filter(_) => true,
            SetK::Cup(a, b) | SetK::Cap(a, b) | SetK::Diff(a, b) | SetK::FcnSet(a, b) => set(a) || set(b),
            SetK::Subset(a) | SetK::Seq(a) | SetK::KSubset(_, a) => set(a),
            SetK::RecSet(_, ss) | SetK::Cross(ss) | SetK::Union(ss) => ss.iter().any(|x| set(x)),
            _ => false,
        }
    }
    match v {
        Value::Closure(_) | Value::LazyFcn(_) | Value::DefRef(_) => true,
        Value::Set(s) => set(s),
        _ => false,
    }
}

/// Action composition (\cdot) is off by default, as in TLC; `-cdot` or the Java property
/// `-Dtlc2.tool.impl.Tool.cdot=true` (Java shim) switches it on.
pub static CDOT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// The number of workers of the run, as TLCGet("config").worker reports it.
pub static WORKERS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(1);
pub fn cdot_enabled() -> bool {
    CDOT.load(std::sync::atomic::Ordering::Relaxed)
}
const NO_CDOT: &str = "The current version of TLC does not support action composition.  An incomplete implementation can be enabled via the tlc2.tool.impl.Tool.cdot=true java property.";

pub fn ev() -> &'static Evaluator {
    EV.with(|e| e.get()).expect("evaluator not initialised")
}

enum Looked {
    Val(Value),
    LetLazy(Rc<Ctx>, Rc<Ctx>),
    LetOp(&'static DefNode, Rc<Ctx>),
    LetInst(&'static Def, Rc<Ctx>),
}

pub type Expansion = Option<(N, C)>;

/// Counters the checker exposes to TLCGet.
#[derive(Default)]
pub struct Stats {
    pub level: Cell<i64>,
    pub distinct: Cell<i64>,
    pub generated: Cell<i64>,
    pub queue: Cell<i64>,
    pub diameter: Cell<i64>,
    pub check_deadlock: Cell<bool>,
    pub stop_requested: Cell<bool>,
    pub active: Cell<bool>,
    /// simulation mode: (trace depth, number of traces asked for or -1, seed, aril)
    pub sim: Cell<Option<(i64, i64, i64, i64)>>,
    /// simulation mode: number of the behaviour being generated
    pub traces: Cell<i64>,
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum RegKey {
    Int(i64),
    Str(StrId),
}

pub struct Evaluator {
    pub nvars: Cell<usize>,
    pub var_names: RefCell<Vec<Name>>,
    pub cur: RefCell<StateRef>,         // current state (unprimed variables)
    pub nxt: RefCell<Option<StateRef>>, // next state (primed variables); may be partial during enumeration
    pub init_mode: Cell<bool>,          // enumerating initial states: `cur` is partial and mutable
    pub prime_depth: Cell<u32>,
    pub st_touch: Cell<u64>,
    pub pr_touch: Cell<u64>,
    pub call_depth: Cell<u32>,
    pub n_assigned: Cell<i64>, // number of target variables assigned during enumeration
    pub in_enabled: Cell<u32>,
    pub extra_generated: Cell<u64>, // intermediate states of action compositions (TLC counts them as generated)
    scratch: RefCell<Vec<(*const Decl, usize)>>, // ENABLED: primed variables of instantiated modules are existentially bound
    pub stats: Stats,
    pub registers: RefCell<HashMap<RegKey, Value>>,
    pub tlc_cache: RefCell<HashMap<(usize, String), Value>>,
    pub host: RefCell<crate::host::HostRef>,
    /// while set, `eval` records the chain of expressions being evaluated (for TLC's message 2103)
    pub tracing: Cell<bool>,
    /// `tracing`, or the read tracker of stepstats.rs is on: `eval` then takes its instrumented path. The
    /// one flag ordinary evaluation tests.
    pub hooked: Cell<bool>,
    pub trace_stack: RefCell<Vec<N>>,
    /// lazily built records for TLCGet("spec")
    pub spec_info: RefCell<Option<Box<dyn Fn() -> R<Value>>>>,
    pub rng: Cell<u64>,
    /// EVERYSTATE_CACHE_STATS: the read tracker of the step-cache estimate (see stepstats.rs)
    pub steps: crate::stepstats::StepStats,
    pub(crate) at: Name,
    lambda: Name,
    enabled_mark: Name,
}

/// The index of the variable an expression names directly: a declared variable used outside any instance
/// environment (where a substitution could stand for it). None for everything else.
#[inline]
pub(crate) fn plain_var(e: N, ctx: &C) -> Option<i64> {
    if let E::App { args, sel, r, .. } = &e.e {
        if let Res::Decl(d) = r.get() {
            if d.is_var && d.idx.get() >= 0 && args.is_empty() && sel.is_none() && ctx.as_ref().map_or(true, |c| !c.env && c.base.is_none()) {
                return Some(d.idx.get() as i64);
            }
        }
    }
    None
}

fn undefined_ident<T>(name: Name) -> R<T> {
    eval_err(format!("In evaluation, the identifier {} is either undefined or not an operator.", name))
}

impl Evaluator {
    pub fn create() -> &'static Evaluator {
        let e: &'static Evaluator = Box::leak(Box::new(Evaluator {
            nvars: Cell::new(0),
            var_names: RefCell::new(vec![]),
            cur: RefCell::new(StateData::blank(0)),
            nxt: RefCell::new(None),
            init_mode: Cell::new(false),
            prime_depth: Cell::new(0),
            st_touch: Cell::new(0),
            pr_touch: Cell::new(0),
            call_depth: Cell::new(0),
            n_assigned: Cell::new(0),
            in_enabled: Cell::new(0),
            extra_generated: Cell::new(0),
            scratch: RefCell::new(vec![]),
            stats: Stats::default(),
            registers: RefCell::new(HashMap::new()),
            tlc_cache: RefCell::new(HashMap::new()),
            host: RefCell::new(Rc::new(crate::host::NullHost)),
            tracing: Cell::new(false),
            hooked: Cell::new(false),
            trace_stack: RefCell::new(Vec::new()),
            spec_info: RefCell::new(None),
            rng: Cell::new(0x9E3779B97F4A7C15),
            steps: crate::stepstats::StepStats::new(),
            at: name("@"),
            lambda: name("LAMBDA"),
            enabled_mark: name("\u{0}enabled"),
        }));
        EV.with(|c| c.set(Some(e)));
        e
    }

    pub fn set_tracing(&self, on: bool) {
        self.tracing.set(on);
        self.hooked.set(on || self.steps.on.get());
    }
    pub(crate) fn set_steps_on(&self, on: bool) {
        self.steps.on.set(on);
        self.hooked.set(on || self.tracing.get());
    }
    pub fn fail<T>(&self, msg: String, n: N) -> R<T> {
        Err(Box::new(Fail::Tla(TlaError { msg, loc: Some(n.loc), module: n.module_str(), kind: "eval" })))
    }
    fn at_node<T>(&self, r: R<T>, n: N) -> R<T> {
        match r {
            Err(mut e) => {
                if let Fail::Tla(t) = &mut *e {
                    if t.loc.is_none() {
                        t.loc = Some(n.loc);
                        t.module = n.module_str();
                    }
                }
                Err(e)
            }
            ok => ok,
        }
    }

    pub fn set_state(&self, cur: &StateRef, nxt: Option<&StateRef>) {
        *self.cur.borrow_mut() = cur.clone();
        *self.nxt.borrow_mut() = nxt.cloned();
    }
    #[inline]
    fn cur_id(&self) -> u64 {
        self.cur.borrow().id
    }

    // ---------- context helpers ----------
    fn lookup(&self, ctx: &C, name: Name) -> R<Looked> {
        let mut head: Option<&Rc<Ctx>> = None;
        let mut c = ctx.as_ref();
        while let Some(n) = c {
            if n.let_head {
                head = Some(n);
            }
            if n.name == name {
                return Ok(match &n.val {
                    Bind::Val(v) => Looked::Val(v.clone()),
                    Bind::LetLazy { .. } => Looked::LetLazy(n.clone(), head.unwrap().clone()),
                    Bind::LetOp(d) => Looked::LetOp(d, head.unwrap().clone()),
                    Bind::LetInst(d) => Looked::LetInst(d, head.unwrap().clone()),
                });
            }
            c = n.next.as_ref();
        }
        eval_err(format!("Internal error: unbound local identifier {}", name))
    }
    /// The binding of a local name as a value (LET definitions become thunks / closures).
    pub fn lookup_value(&self, ctx: &C, name: Name, n: Option<N>) -> R<Value> {
        Ok(match self.lookup(ctx, name)? {
            Looked::Val(v) => v,
            Looked::LetLazy(node, head) => match n {
                Some(n) => Lazy::new(n, ctx.clone()),
                None => match &node.val {
                    Bind::LetLazy { body, .. } => Lazy::new(body, Some(head)),
                    _ => unreachable!(),
                },
            },
            Looked::LetOp(d, head) => Value::Closure(Rc::new(Closure { params: &d.params, body: &d.body, ctx: Some(head), name: d.name })),
            Looked::LetInst(d, head) => Value::DefRef(Rc::new(DefRef { def: d, base: Some(head) })),
        })
    }
    pub fn env_lookup(&self, base: &C, name: Name) -> Option<Value> {
        let mut c = base.as_ref();
        while let Some(n) = c {
            if n.name == name {
                return match &n.val {
                    Bind::Val(v) => Some(v.clone()),
                    _ => None,
                };
            }
            c = n.next.as_ref();
        }
        None
    }
    pub fn bind_tuple(&self, names: &[Name], v: &Value, ctx: &C) -> R<C> {
        match v {
            Value::Tuple(t) if t.len() == names.len() => {
                let mut c = ctx.clone();
                for i in 0..names.len() {
                    c = cons(names[i], t[i].clone(), &c);
                }
                Ok(c)
            }
            _ => eval_err(format!(
                "Attempted to match the tuple pattern <<{}>> against the value {}",
                names.iter().map(|n| n.to_string()).collect::<Vec<_>>().join(", "),
                fmt(v)
            )),
        }
    }

    fn force_cell(&self, e: N, ctx: &C, v: &RefCell<Value>, st: &Cell<u64>, lazy: bool) -> R<Value> {
        let s = st.get();
        if s != 0 {
            if s == ANY {
                return Ok(v.borrow().clone());
            }
            if s == self.cur_id() && !self.init_mode.get() && self.prime_depth.get() == 0 {
                self.st_touch.set(self.st_touch.get() + 1);
                if self.steps.on.get() {
                    // computed from the state before this unit began: it stands for the reads it made
                    self.steps.elem(usize::MAX >> 8, Ok(e as *const Node as usize as u64), value_word(&v.borrow()));
                }
                return Ok(v.borrow().clone());
            }
        }
        let (s0, p0) = (self.st_touch.get(), self.pr_touch.get());
        let val = if lazy { self.eval_lazy(e, ctx)? } else { self.eval(e, ctx)? };
        if self.pr_touch.get() == p0 {
            if self.st_touch.get() == s0 {
                *v.borrow_mut() = val.clone();
                st.set(ANY);
            } else if !self.init_mode.get() && self.prime_depth.get() == 0 {
                *v.borrow_mut() = val.clone();
                st.set(self.cur_id());
            }
        }
        Ok(val)
    }
    #[inline]
    pub fn force(&self, lz: &Lazy) -> R<Value> {
        self.force_cell(lz.e, &lz.ctx, &lz.v, &lz.st, false)
    }
    pub fn force_lazy(&self, lz: &Lazy) -> R<Value> {
        self.force_cell(lz.e, &lz.ctx, &lz.v, &lz.st, true)
    }
    fn force_let(&self, node: &Rc<Ctx>, head: Rc<Ctx>, lazy: bool) -> R<Value> {
        match &node.val {
            Bind::LetLazy { body, v, st, d } => {
                let val = self.force_cell(body, &Some(head), v, st, lazy)?;
                // A closed constant (no state, no free local, no side effect) has one value: keep it on the
                // definition, so that later evaluations of the LET bind it directly.
                if st.get() == ANY && node.base.is_none() && !node.env && d.cval.borrow().is_none() && crate::modules::let_closed(d) {
                    if !captures_ctx(&val) {
                        *d.cval.borrow_mut() = Some(val.clone());
                    } else if let Value::Set(fs) = &val {
                        // a small filtered set: keep its elements rather than the lazy filter (which holds the context)
                        if let SetK::Filter(f) = &fs.k {
                            if f.s.enumerable() && matches!(f.s.size(), Ok(n) if n <= 1024) {
                                if let Ok(e) = fs.elems() {
                                    *d.cval.borrow_mut() = Some(SetV::of(e.to_vec()));
                                }
                            }
                        }
                    }
                }
                // A value that captures its context (lazy set, closure, lazy function) must not be cached in a
                // cell of that very context: the reference cycle would never be freed.
                if captures_ctx(&val) && st.get() != 0 {
                    st.set(0);
                    *v.borrow_mut() = Value::Undef;
                }
                Ok(val)
            }
            _ => unreachable!(),
        }
    }

    /// Turn an argument expression into a thunk / value / operator.
    pub fn mk_arg(&self, n: N, ctx: &C) -> R<Value> {
        match &n.e {
            E::Num(v) => return Ok(Value::Int(*v)),
            E::Str(..) => return self.eval(n, ctx),
            E::Bool(b) => return Ok(Value::Bool(*b)),
            E::Lambda { params, body } => return Ok(Value::Closure(Rc::new(Closure { params, body, ctx: ctx.clone(), name: self.lambda }))),
            E::Dot { e, field } => {
                // m.f where m is a local name bound to a record that has the field: the value is at hand,
                // no thunk is needed (anything else, including a missing field, stays delayed)
                if let E::App { name, args, sel, r, .. } = &e.e {
                    if args.is_empty() && sel.is_none() && matches!(r.get(), Res::Local) {
                        let mut c = ctx.as_ref();
                        while let Some(node) = c {
                            if node.name == *name {
                                if let Bind::Val(Value::Record(rec)) = &node.val {
                                    if let Some(v) = rec.get(*field) {
                                        return Ok(v.clone());
                                    }
                                }
                                break;
                            }
                            c = node.next.as_ref();
                        }
                    }
                }
            }
            E::App { name, args, sel, r, .. } if args.is_empty() && sel.is_none() => match r.get() {
                Res::Local => return self.lookup_value(ctx, *name, Some(n)),
                Res::Def(d) => {
                    let d = d.resolved();
                    if !d.params.is_empty() {
                        return Ok(Value::DefRef(Rc::new(DefRef { def: d, base: base_of(ctx) })));
                    }
                }
                Res::Decl(d) if !d.is_var => {
                    let base = base_of(ctx);
                    if base.is_some() {
                        if let Some(b) = self.env_lookup(&base, *name) {
                            return Ok(b);
                        }
                    }
                    if let Some(s) = d.subst.get() {
                        return Ok(if !s.params.is_empty() { Value::DefRef(Rc::new(DefRef { def: s, base: None })) } else { Lazy::new(n, ctx.clone()) });
                    }
                    if let Some(v) = d.value.borrow().as_ref() {
                        return Ok(v.clone());
                    }
                }
                _ => {}
            },
            _ => {}
        }
        Ok(Lazy::new(n, ctx.clone()))
    }
    fn mk_args(&self, args: &'static [Node], ctx: &C) -> R<Vec<Value>> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            out.push(self.mk_arg(a, ctx)?);
        }
        Ok(out)
    }

    #[inline]
    pub fn unthunk(&self, t: &Value) -> R<Value> {
        match t {
            Value::Thunk(lz) => {
                let v = self.force(lz)?;
                match &v {
                    Value::LazyFcn(f) => f.force(self),
                    _ => Ok(v),
                }
            }
            v => Ok(v.clone()),
        }
    }

    fn build_env(&self, def: &'static Def, thunks: &[Value], caller_base: &C) -> C {
        let inst = def.inst.as_ref().unwrap();
        if inst.nparams == 0 && caller_base.is_none() {
            if let Some(c) = inst.env_cache.borrow().as_ref() {
                return c.clone();
            }
        }
        let mut pc = caller_base.clone();
        for i in 0..inst.nparams {
            pc = cons(def.params[i].name, thunks[i].clone(), &pc);
        }
        let mut head: C = None;
        for s in inst.substs.iter() {
            // substitution expressions that fail to resolve surface when they are forced
            let v = self.mk_arg(s.e, &pc).unwrap_or_else(|_| Lazy::new(s.e, pc.clone()));
            head = Some(Rc::new(Ctx { name: s.name, val: Bind::Val(v), next: head, base: None, env: true, let_head: false }));
        }
        if inst.nparams == 0 && caller_base.is_none() {
            *inst.env_cache.borrow_mut() = Some(head.clone());
        }
        head
    }

    /// Expand a definition application into (body, context) without evaluating it.
    pub fn expand_def(&self, def: &'static Def, thunks: &[Value], base: &C) -> R<Expansion> {
        self.expand_def_via(def, thunks, base, false)
    }
    fn expand_def_via(&self, def: &'static Def, thunks: &[Value], base: &C, via_instance: bool) -> R<Expansion> {
        // A config override (Op <- Other) replaces references to Op itself; an instantiated copy (I!Op) keeps the
        // original body, as in TLC where the override is attached to the definition node, not to its body.
        let def = match def.over.get() {
            Some(o) if !(via_instance && o.builtin.get().is_none()) => o,
            _ => def,
        };
        if def.builtin.get().is_some() {
            return Ok(None);
        }
        if let Some(inst) = &def.inst {
            if thunks.len() < inst.nparams {
                return eval_err(format!("The operator {} expects {} arguments but was given {}.", def.name, def.params.len(), thunks.len()));
            }
            let env = self.build_env(def, thunks, base);
            return self.expand_def_via(inst.orig, &thunks[inst.nparams..], &env, true);
        }
        let ps = &def.params;
        if ps.len() != thunks.len() {
            return eval_err(format!("The operator {} expects {} arguments but was given {}.", def.name, ps.len(), thunks.len()));
        }
        let mut c = base.clone();
        for i in 0..ps.len() {
            c = cons(ps[i].name, thunks[i].clone(), &c);
        }
        Ok(Some((def.body.get().unwrap(), c)))
    }

    /// Expand an `app` node one step: the body/context it denotes, or None if it is a plain value or builtin.
    pub fn expand_app(&self, n: N, ctx: &C) -> R<Expansion> {
        check_stack()?;
        let (name, args, sel, r) = match &n.e {
            E::App { name, args, sel, r, .. } => (*name, args, sel, r.get()),
            _ => return Ok(None),
        };
        let mut res: Expansion = None;
        match r {
            Res::Local => match self.lookup(ctx, name)? {
                Looked::Val(Value::Thunk(lz)) => res = Some((lz.e, lz.ctx.clone())),
                Looked::Val(b @ (Value::Closure(_) | Value::DefRef(_))) => res = self.expand_op(&b, &self.mk_args(args, ctx)?)?,
                Looked::Val(_) => {}
                Looked::LetLazy(node, head) => {
                    if let Bind::LetLazy { body, .. } = &node.val {
                        res = Some((body, Some(head)));
                    }
                }
                Looked::LetOp(d, head) => {
                    let b = Value::Closure(Rc::new(Closure { params: &d.params, body: &d.body, ctx: Some(head), name: d.name }));
                    res = self.expand_op(&b, &self.mk_args(args, ctx)?)?;
                }
                Looked::LetInst(d, head) => {
                    let b = Value::DefRef(Rc::new(DefRef { def: d, base: Some(head) }));
                    res = self.expand_op(&b, &self.mk_args(args, ctx)?)?;
                }
            },
            Res::Def(d) => {
                let dd = d.over.get().unwrap_or(d);
                if dd.builtin.get().is_some() && sel.is_none() {
                    // a builtin operator has no body to expand: do not build thunks for its arguments
                    return Ok(None);
                }
                if dd.inst.is_none() && dd.params.len() == args.len() {
                    // bind the parameters directly, without an intermediate argument vector
                    let mut c = base_of(ctx);
                    for (p, a) in dd.params.iter().zip(args.iter()) {
                        c = cons(p.name, self.mk_arg(a, ctx)?, &c);
                    }
                    res = Some((dd.body.get().unwrap(), c));
                } else {
                    res = self.expand_def(d, &self.mk_args(args, ctx)?, &base_of(ctx))?;
                }
            }
            Res::Decl(d) => {
                let base = base_of(ctx);
                let b = if base.is_some() { self.env_lookup(&base, name) } else { None };
                match b {
                    Some(Value::Thunk(lz)) => res = Some((lz.e, lz.ctx.clone())),
                    Some(b @ (Value::Closure(_) | Value::DefRef(_))) => res = self.expand_op(&b, &self.mk_args(args, ctx)?)?,
                    Some(_) => {}
                    None => {
                        if !d.is_var {
                            if let Some(s) = d.subst.get() {
                                res = self.expand_def(s, &self.mk_args(args, ctx)?, &None)?;
                            }
                        }
                    }
                }
            }
            Res::None => return self.fail(format!("Internal error: unresolved identifier {}", name), n),
        }
        if let (Some(x), Some(sel)) = (&res, sel) {
            res = Some(self.select(x.clone(), sel, n)?);
        }
        Ok(res)
    }

    pub fn expand_op(&self, op: &Value, thunks: &[Value]) -> R<Expansion> {
        match op {
            Value::DefRef(d) => self.expand_def(d.def, thunks, &d.base),
            Value::Closure(c) => {
                if c.params.len() != thunks.len() {
                    return eval_err(format!("The operator {} expects {} arguments but was given {}.", c.name, c.params.len(), thunks.len()));
                }
                let mut ctx = c.ctx.clone();
                for i in 0..c.params.len() {
                    ctx = cons(c.params[i].name, thunks[i].clone(), &ctx);
                }
                Ok(Some((c.body, ctx)))
            }
            _ => Ok(None),
        }
    }

    // Subexpression selectors: Op!1, Op!<<, Op!>> ...
    fn select(&self, res: (N, C), sel: &'static [Sel], n: N) -> R<(N, C)> {
        let mut body = res.0;
        for s in sel {
            let i: i64 = match s {
                Sel::Sym(x) if &**x == ":" => continue,
                Sel::Sym(x) if &**x == "<<" => 0,
                Sel::Sym(x) if &**x == ">>" => 1,
                Sel::Num(k) => k - 1,
                _ => -1,
            };
            let kid: Option<N> = match &body.e {
                E::Op(_, a) => a.get(i.max(0) as usize).filter(|_| i >= 0),
                E::App { args, .. } | E::FnApp { args, .. } => args.get(i.max(0) as usize).filter(|_| i >= 0),
                E::Quant { body: b, .. } | E::Choose { body: b, .. } | E::Lambda { body: b, .. } | E::Let { body: b, .. } | E::FnDef { body: b, .. } | E::TQuant { body: b, .. } => {
                    if i == 0 {
                        Some(&**b)
                    } else {
                        None
                    }
                }
                _ => None,
            };
            match kid {
                Some(k) => body = k,
                None => return self.fail("Unsupported subexpression selector".to_string(), n),
            }
        }
        Ok((body, res.1))
    }

    pub fn call_builtin(&self, bi: &'static Builtin, args: &[Value]) -> R<Value> {
        match &bi.f {
            BFn::Native(f) => f(self, args),
            BFn::Const(v) => Ok(v.clone()),
            BFn::Table(rows, nm) => {
                'rows: for (ra, rv) in rows.borrow().iter() {
                    for (i, x) in ra.iter().enumerate() {
                        if !val_eq(x, &args[i])? {
                            continue 'rows;
                        }
                    }
                    return Ok(rv.clone());
                }
                eval_err(format!(
                    "Attempted to apply the operator {} to arguments ({}) for which the configuration file gives no value.",
                    nm,
                    args.iter().map(fmt).collect::<Vec<_>>().join(", ")
                ))
            }
        }
    }

    pub fn apply_op(&self, op: &Value, args: &[Value]) -> R<Value> {
        match op {
            Value::DefRef(dr) => {
                let d = dr.def.resolved();
                if let Some(bi) = d.builtin.get() {
                    if bi.lazy {
                        return self.call_builtin(bi, args);
                    }
                    let mut a = Vec::with_capacity(args.len());
                    for x in args {
                        a.push(self.unthunk(x)?);
                    }
                    return self.call_builtin(bi, &a);
                }
            }
            Value::Closure(_) => {}
            _ => return eval_err(format!("Attempted to apply a non-operator value {} as an operator.", fmt(op))),
        }
        match self.expand_op(op, args)? {
            Some((body, ctx)) => {
                check_stack()?;
                self.eval(body, &ctx)
            }
            None => {
                // instance of a builtin operator (e.g. LET T == INSTANCE TLC IN T!PrintT(x))
                let mut d = match op {
                    Value::DefRef(dr) => dr.def.resolved(),
                    _ => unreachable!(),
                };
                let mut args = args;
                while let Some(inst) = &d.inst {
                    args = &args[inst.nparams.min(args.len())..];
                    d = inst.orig.resolved();
                }
                let bi = d.builtin.get().unwrap();
                if bi.lazy {
                    return self.call_builtin(bi, args);
                }
                let mut a = Vec::with_capacity(args.len());
                for (i, x) in args.iter().enumerate() {
                    a.push(if bi.ops & (1 << i) != 0 { x.clone() } else { self.unthunk(x)? });
                }
                self.call_builtin(bi, &a)
            }
        }
    }

    fn apply_def(&self, def: &'static Def, n: N, args: &'static [Node], ctx: &C) -> R<Value> {
        let def = def.resolved();
        if let Some(bi) = def.builtin.get() {
            let na = args.len();
            if bi.arith != 0 && na == 2 {
                // integer arithmetic and comparison without the argument buffer and the indirect call
                let x = self.eval(&args[0], ctx)?;
                let y = self.eval(&args[1], ctx)?;
                if let (Value::Int(a), Value::Int(b)) = (&x, &y) {
                    let (a, b) = (*a, *b);
                    match bi.arith {
                        1 | 2 => {
                            let r = if bi.arith == 1 { a.checked_add(b) } else { a.checked_sub(b) };
                            if let Some(r) = r {
                                if (-2147483648..=2147483647).contains(&r) {
                                    return Ok(Value::Int(r));
                                }
                            }
                        }
                        3 => return Ok(Value::Bool(a < b)),
                        4 => return Ok(Value::Bool(a > b)),
                        5 => return Ok(Value::Bool(a <= b)),
                        _ => return Ok(Value::Bool(a >= b)),
                    }
                }
                return self.call_builtin(bi, &[x, y]);
            }
            let mut buf: [Value; 3] = [Value::Undef, Value::Undef, Value::Undef];
            let mut big: Vec<Value>;
            let slots: &mut [Value] = if na <= 3 {
                &mut buf[..na]
            } else {
                big = vec![Value::Undef; na];
                &mut big[..]
            };
            if bi.lazy {
                for i in 0..na {
                    slots[i] = self.mk_arg(&args[i], ctx)?;
                }
            } else if bi.ops != 0 {
                for i in 0..na {
                    slots[i] = if bi.ops & (1 << i) != 0 { self.mk_arg(&args[i], ctx)? } else { self.eval(&args[i], ctx)? };
                }
            } else {
                for i in 0..na {
                    slots[i] = self.eval(&args[i], ctx)?;
                }
            }
            return self.call_builtin(bi, slots);
        }
        let base = base_of(ctx);
        if def.params.is_empty() && def.inst.is_none() {
            let body = def.body.get().unwrap();
            if base.is_none() {
                if let Some(v) = def.cache.borrow().as_ref() {
                    return Ok(v.clone());
                }
                check_stack()?;
                let (s0, p0) = (self.st_touch.get(), self.pr_touch.get());
                let v = self.eval(body, &None)?;
                // A lazy set can capture the state before its predicate reads any variables.
                if self.st_touch.get() == s0 && self.pr_touch.get() == p0 && crate::modules::def_level(def) == 0 {
                    *def.cache.borrow_mut() = Some(v.clone());
                }
                return Ok(v);
            }
            check_stack()?;
            return self.eval(body, &base);
        }
        let expanded = if def.inst.is_none() {
            // common case: bind the parameters directly, without an intermediate argument vector
            let ps = &def.params;
            if ps.len() != args.len() {
                return eval_err(format!("The operator {} expects {} arguments but was given {}.", def.name, ps.len(), args.len()));
            }
            let mut c = base;
            for i in 0..ps.len() {
                c = cons(ps[i].name, self.mk_arg(&args[i], ctx)?, &c);
            }
            Some((def.body.get().unwrap(), c))
        } else {
            let thunks = self.mk_args(args, ctx)?;
            self.expand_def(def, &thunks, &base)?
        };
        let (body, c) = match expanded {
            Some(x) => x,
            None => {
                // instance of a builtin operator
                let mut d = def;
                while let Some(inst) = &d.inst {
                    d = inst.orig;
                }
                return self.apply_def(d, n, args, ctx);
            }
        };
        let cd = self.call_depth.get() + 1;
        self.call_depth.set(cd);
        if cd > 6000 {
            self.call_depth.set(0);
            return self.fail(format!("Evaluation of {} exceeded the maximum recursion depth; the definition is probably non-terminating.", def.name), n);
        }
        if cd & 63 == 0 {
            check_stack()?;
        }
        let v = self.eval(body, &c)?;
        self.call_depth.set(self.call_depth.get().wrapping_sub(1));
        Ok(v)
    }

    #[inline]
    pub fn eval_app(&self, n: N, ctx: &C) -> R<Value> {
        let (name, args, sel, r) = match &n.e {
            E::App { name, args, sel, r, .. } => (*name, &args[..], sel, r.get()),
            _ => unreachable!(),
        };
        if sel.is_some() {
            return match self.expand_app(n, ctx)? {
                Some((b, c)) => self.eval(b, &c),
                None => self.fail("Unsupported subexpression selector".into(), n),
            };
        }
        match r {
            Res::Local => {
                let b = match self.lookup(ctx, name)? {
                    Looked::Val(v) => v,
                    Looked::LetLazy(node, head) => return self.force_let(&node, head, false),
                    Looked::LetOp(d, head) => {
                        if args.is_empty() && !d.params.is_empty() {
                            return Ok(Value::Closure(Rc::new(Closure { params: &d.params, body: &d.body, ctx: Some(head), name: d.name })));
                        }
                        if d.params.len() != args.len() {
                            return eval_err(format!("The operator {} expects {} arguments but was given {}.", d.name, d.params.len(), args.len()));
                        }
                        let mut c: C = Some(head);
                        for i in 0..args.len() {
                            c = cons(d.params[i].name, self.mk_arg(&args[i], ctx)?, &c);
                        }
                        check_stack()?;
                        return self.eval(&d.body, &c);
                    }
                    Looked::LetInst(d, head) => Value::DefRef(Rc::new(DefRef { def: d, base: Some(head) })),
                };
                match &b {
                    Value::Thunk(lz) => self.force(lz),
                    Value::Closure(c) => {
                        if args.is_empty() && !c.params.is_empty() {
                            return Ok(b);
                        }
                        self.apply_op(&b, &self.mk_args(args, ctx)?)
                    }
                    Value::DefRef(d) => {
                        if args.is_empty() && !d.def.resolved().params.is_empty() {
                            return Ok(b);
                        }
                        self.apply_op(&b, &self.mk_args(args, ctx)?)
                    }
                    _ => Ok(b),
                }
            }
            Res::Def(d) => self.apply_def(d, n, args, ctx),
            Res::Decl(d) => {
                if let Some(c) = ctx {
                    if c.env || c.base.is_some() {
                        let base = base_of(ctx);
                        if let Some(b) = self.env_lookup(&base, name) {
                            if self.in_enabled.get() > 0 && self.prime_depth.get() > 0 && d.is_var && matches!(b, Value::Thunk(_)) {
                                let idx = self.as_var(n, ctx)?;
                                if idx >= 0 {
                                    let v = self.cur.borrow().get(idx as usize);
                                    self.pr_touch.set(self.pr_touch.get() + 1);
                                    if self.steps.on.get() {
                                        self.steps.var(idx as usize, &v, true);
                                    }
                                    if matches!(v, Value::Undef) {
                                        return self.at_node(undefined_ident(d.name), n);
                                    }
                                    return Ok(v);
                                }
                            }
                            return match &b {
                                Value::Thunk(lz) => self.force(lz),
                                Value::Closure(_) | Value::DefRef(_) => self.apply_op(&b, &self.mk_args(args, ctx)?),
                                _ => Ok(b),
                            };
                        }
                    }
                }
                if d.is_var {
                    let idx = d.idx.get();
                    let v = if idx >= 0 { self.cur.borrow().get(idx as usize) } else { Value::Undef };
                    if self.prime_depth.get() > 0 {
                        self.pr_touch.set(self.pr_touch.get() + 1);
                    } else {
                        self.st_touch.set(self.st_touch.get() + 1);
                    }
                    if matches!(v, Value::Undef) {
                        return self.at_node(undefined_ident(d.name), n);
                    }
                    if self.steps.on.get() {
                        self.steps.var(idx.max(0) as usize, &v, self.prime_depth.get() > 0);
                    }
                    return Ok(v);
                }
                // constant
                if let Some(s) = d.subst.get() {
                    if s.params.is_empty() && args.is_empty() {
                        return self.apply_def(s, n, args, &None);
                    }
                    return match self.expand_def(s, &self.mk_args(args, ctx)?, &None)? {
                        None => self.apply_def(s, n, args, ctx),
                        Some((b, c)) => self.eval(b, &c),
                    };
                }
                if let Some(v) = d.value.borrow().as_ref() {
                    return Ok(v.clone());
                }
                self.fail(format!("The constant parameter {} is not assigned a value by the configuration file.", d.name), n)
            }
            Res::None => self.fail(format!("Internal error: unresolved identifier {}", name), n),
        }
    }

    // ---------- evaluation ----------
    #[inline]
    pub fn eval_bool(&self, n: N, ctx: &C) -> R<bool> {
        match self.eval(n, ctx)? {
            Value::Bool(b) => Ok(b),
            v => self.fail(format!("Attempted to evaluate an expression as a boolean, but it was the non-boolean value:\n{}", fmt(&v)), n),
        }
    }
    pub fn eval_set(&self, n: N, ctx: &C) -> R<Rc<SetV>> {
        match self.eval(n, ctx)? {
            Value::Set(s) => Ok(s),
            v => self.fail(format!("Attempted to use the non-set value:\n{}\nas a set.", fmt(&v)), n),
        }
    }
    fn elems_at<'a>(&self, s: &'a SetV, n: N) -> R<&'a [Value]> {
        self.at_node(s.elems(), n)
    }

    /// Iterate over all bindings of a list of bounds; f returns true to stop. Returns true if stopped.
    pub fn for_bindings(&self, bounds: &'static [Bound], ctx: &C, f: &mut dyn FnMut(&C) -> R<bool>) -> R<bool> {
        if bounds.len() == 1 {
            let b = &bounds[0];
            let set = match &b.set {
                Some(s) => s,
                None => return eval_err("TLC cannot handle unbounded quantification.".into()),
            };
            let s = self.eval_set(set, ctx)?;
            if let (SetK::Interval(lo, hi), Some(names)) = (&s.k, &b.names) {
                if names.len() == 1 {
                    // an integer interval is walked without materializing its elements
                    let nm = names[0];
                    for i in *lo..=*hi {
                        if f(&cons(nm, Value::Int(i), ctx))? {
                            return Ok(true);
                        }
                    }
                    return Ok(false);
                }
            }
            let es = self.elems_at(&s, set)?;
            if let Some(t) = &b.tuple {
                for x in es {
                    if f(&self.bind_tuple(t, x, ctx)?)? {
                        return Ok(true);
                    }
                }
                return Ok(false);
            }
            let names = b.names.as_ref().unwrap();
            if names.len() == 1 {
                let nm = names[0];
                for x in es {
                    if f(&cons(nm, x.clone(), ctx))? {
                        return Ok(true);
                    }
                }
                return Ok(false);
            }
        }
        let mut sets: Vec<Rc<SetV>> = Vec::with_capacity(bounds.len());
        for b in bounds {
            let set = match &b.set {
                Some(s) => s,
                None => return eval_err("TLC cannot handle unbounded quantification.".into()),
            };
            let s = self.eval_set(set, ctx)?;
            self.elems_at(&s, set)?;
            sets.push(s);
        }
        // TLC varies the FIRST bound variable fastest, so the last one is the outermost loop.
        struct Flat<'a> {
            name: Option<Name>,
            tuple: Option<&'static [Name]>,
            es: &'a [Value],
        }
        let mut flat: Vec<Flat> = vec![];
        for (i, b) in bounds.iter().enumerate() {
            let es = sets[i].elems()?;
            if let Some(t) = &b.tuple {
                flat.push(Flat { name: None, tuple: Some(t), es });
            } else {
                for nm in b.names.as_ref().unwrap() {
                    flat.push(Flat { name: Some(*nm), tuple: None, es });
                }
            }
        }
        fn rec(ev: &Evaluator, flat: &[Flat], i: isize, c: &C, f: &mut dyn FnMut(&C) -> R<bool>) -> R<bool> {
            if i < 0 {
                return f(c);
            }
            let b = &flat[i as usize];
            for v in b.es {
                let c2 = match b.tuple {
                    Some(t) => ev.bind_tuple(t, v, c)?,
                    None => cons(b.name.unwrap(), v.clone(), c),
                };
                if rec(ev, flat, i - 1, &c2, f)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        rec(self, &flat, flat.len() as isize - 1, ctx, f)
    }

    pub fn bind_let(&self, defs: &'static [LetDef], ctx: &C) -> C {
        let mut total = 0;
        for d in defs {
            total += match d {
                LetDef::Def(_) => 1,
                LetDef::Inst(i) => i.inst_defs.get().map_or(0, |v| v.len()),
            };
        }
        let mut c = ctx.clone();
        let base = base_of(ctx);
        let mut k = 0;
        let mut push = |name: Name, val: Bind, c: &mut C| {
            k += 1;
            *c = Some(Rc::new(Ctx { name, val, next: c.take(), base: base.clone(), env: false, let_head: k == total }));
        };
        for d in defs {
            match d {
                LetDef::Inst(i) => {
                    if let Some(ds) = i.inst_defs.get() {
                        for def in ds {
                            push(def.name, Bind::LetInst(def), &mut c);
                        }
                    }
                }
                LetDef::Def(d) => {
                    let b = if d.params.is_empty() {
                        // a closed constant definition that has been evaluated before
                        let known = if d.closed.get() == 1 && base.is_none() { d.cval.borrow().clone() } else { None };
                        match known {
                            Some(v) => Bind::Val(v),
                            None => Bind::LetLazy { body: &d.body, v: RefCell::new(Value::Undef), st: Cell::new(0), d },
                        }
                    } else {
                        Bind::LetOp(d)
                    };
                    push(d.name, b, &mut c);
                }
            }
        }
        c
    }

    pub(crate) fn str_node(&self, s: &Rc<str>, id: &Cell<Option<StrId>>) -> StrId {
        match id.get() {
            Some(i) => i,
            None => {
                let i = str_id(s);
                id.set(Some(i));
                i
            }
        }
    }

    #[inline(never)]
    pub fn eval(&self, n: N, ctx: &C) -> R<Value> {
        if self.hooked.get() {
            return self.eval_hooked(n, ctx);
        }
        self.eval_inner(n, ctx)
    }
    #[cold]
    #[inline(never)]
    fn eval_hooked(&self, n: N, ctx: &C) -> R<Value> {
        if self.tracing.get() {
            return self.eval_traced(n, ctx);
        }
        self.eval_steps(n, ctx)
    }
    #[cold]
    #[inline(never)]
    fn eval_traced(&self, n: N, ctx: &C) -> R<Value> {
        self.trace_stack.borrow_mut().push(n);
        let r = self.eval_inner(n, ctx);
        if r.is_ok() {
            self.trace_stack.borrow_mut().pop();
        }
        r
    }
    #[inline(always)]
    pub(crate) fn eval_inner(&self, n: N, ctx: &C) -> R<Value> {
        match &n.e {
            E::App { r, name, sel, .. } => {
                // The most frequent leaves, without the general application path: a state variable or a
                // constant outside any instance context, and a local identifier bound to a plain value.
                match r.get() {
                    Res::Decl(d) => {
                        if ctx.as_ref().map_or(true, |c| !c.env && c.base.is_none()) {
                            if d.is_var {
                                let idx = d.idx.get();
                                if idx >= 0 {
                                    let v = self.cur.borrow().get(idx as usize);
                                    if !matches!(v, Value::Undef) {
                                        if self.prime_depth.get() > 0 {
                                            self.pr_touch.set(self.pr_touch.get() + 1);
                                        } else {
                                            self.st_touch.set(self.st_touch.get() + 1);
                                        }
                                        return Ok(v);
                                    }
                                }
                            } else if d.subst.get().is_none() {
                                if let Some(v) = d.value.borrow().as_ref() {
                                    return Ok(v.clone());
                                }
                            }
                        }
                    }
                    Res::Local => {
                        let mut c = ctx.as_ref();
                        while let Some(node) = c {
                            if node.name == *name {
                                if let Bind::Val(v) = &node.val {
                                    if matches!(v, Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) | Value::Tuple(_) | Value::Record(_) | Value::Fcn(_) | Value::Set(_)) {
                                        return Ok(v.clone());
                                    }
                                    if let (Value::Thunk(lz), None) = (v, sel) {
                                        // a delayed argument: force it here (as eval_app would after a second lookup)
                                        let v = self.force(lz)?;
                                        return match &v {
                                            Value::LazyFcn(f) => f.force(self),
                                            _ => Ok(v),
                                        };
                                    }
                                }
                                break;
                            }
                            c = node.next.as_ref();
                        }
                    }
                    _ => {}
                }
                self.eval_app_forced(n, ctx)
            }
            E::Op(k, a) => self.eval_op_fast(n, *k, a, ctx),
            E::Num(v) => Ok(Value::Int(*v)),
            E::Bool(b) => Ok(Value::Bool(*b)),
            E::Str(s, id) => Ok(Value::Str(self.str_node(s, id))),
            _ => self.eval_slow(n, ctx),
        }
    }

    #[inline(never)]
    fn eval_app_forced(&self, n: N, ctx: &C) -> R<Value> {
        let v = match &n.e {
            // an application of a definition (user-defined or builtin): no need to look at the other cases
            E::App { args, sel: None, r, .. } => match r.get() {
                Res::Def(d) => self.apply_def(d, n, args, ctx)?,
                _ => self.eval_app(n, ctx)?,
            },
            _ => self.eval_app(n, ctx)?,
        };
        if let Value::LazyFcn(f) = &v {
            return f.force(self);
        }
        Ok(v)
    }

    #[inline(never)]
    fn eval_op_fast(&self, n: N, k: K, a: &'static [Node], ctx: &C) -> R<Value> {
        match k {
            K::And => {
                for x in a {
                    if !self.eval_bool(x, ctx)? {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            }
            K::Or => {
                for x in a {
                    if self.eval_bool(x, ctx)? {
                        return Ok(Value::Bool(true));
                    }
                }
                Ok(Value::Bool(false))
            }
            K::Not => Ok(Value::Bool(!self.eval_bool(&a[0], ctx)?)),
            K::Eq | K::Ne => {
                // S = {} on an enumerated set: no empty set is built
                if let E::Op(K::SetEnum, e) = &a[1].e {
                    if e.is_empty() {
                        let x = self.eval(&a[0], ctx)?;
                        let eq = match &x {
                            Value::Set(s) if matches!(s.k, SetK::Enum(_)) => match &s.k {
                                SetK::Enum(el) => el.is_empty(),
                                _ => unreachable!(),
                            },
                            _ => val_eq(&x, &Value::Set(empty_set()))?,
                        };
                        return Ok(Value::Bool(eq == (k == K::Eq)));
                    }
                }
                let (x, y) = (self.eval(&a[0], ctx)?, self.eval(&a[1], ctx)?);
                let eq = match scalar_cmp(&x, &y) {
                    Some(c) => c == std::cmp::Ordering::Equal,
                    None => val_eq(&x, &y)?,
                };
                Ok(Value::Bool(eq == (k == K::Eq)))
            }
            K::If => {
                if self.eval_bool(&a[0], ctx)? {
                    self.eval(&a[1], ctx)
                } else {
                    self.eval(&a[2], ctx)
                }
            }
            _ => self.eval_op(n, k, a, ctx),
        }
    }

    #[inline(never)]
    fn eval_slow(&self, n: N, ctx: &C) -> R<Value> {
        match &n.e {
            E::Num(v) => Ok(Value::Int(*v)),
            E::Str(s, id) => Ok(Value::Str(self.str_node(s, id))),
            E::Bool(b) => Ok(Value::Bool(*b)),
            E::App { .. } => {
                let v = self.eval_app(n, ctx)?;
                if let Value::LazyFcn(f) = &v {
                    return f.force(self);
                }
                Ok(v)
            }
            E::Op(k, a) => self.eval_op(n, *k, a, ctx),
            E::Case { arms, other } => {
                for (c, e) in arms {
                    if self.eval_bool(c, ctx)? {
                        return self.eval(e, ctx);
                    }
                }
                if let Some(o) = other {
                    return self.eval(o, ctx);
                }
                self.fail("Attempted to evaluate a CASE expression in which none of the conditions were true.".into(), n)
            }
            E::Let { defs, body } => self.eval(body, &self.bind_let(defs, ctx)),
            E::Quant { forall, bounds, body } => {
                let body: N = body;
                if *forall {
                    Ok(Value::Bool(!self.for_bindings(bounds, ctx, &mut |c| Ok(!self.eval_bool(body, c)?))?))
                } else {
                    Ok(Value::Bool(self.for_bindings(bounds, ctx, &mut |c| self.eval_bool(body, c))?))
                }
            }
            E::Choose { bound, body } => {
                let set = match &bound.set {
                    Some(s) => s,
                    None => return self.fail("TLC attempted to evaluate an unbounded CHOOSE.\nMake sure that the expression is of form CHOOSE x \\in S: P(x).".into(), n),
                };
                let s = self.eval_set(set, ctx)?;
                let es = self.elems_at(&s, set)?;
                // CHOOSE x \in S : TRUE, the usual way to pick an element: no binding needed
                if matches!(body.e, E::Bool(true)) && bound.tuple.is_none() {
                    if let Some(x) = es.first() {
                        return Ok(x.clone());
                    }
                }
                for x in es {
                    let c = match &bound.tuple {
                        Some(t) => self.bind_tuple(t, x, ctx)?,
                        None => cons(bound.names.as_ref().unwrap()[0], x.clone(), ctx),
                    };
                    if self.eval_bool(body, &c)? {
                        return Ok(x.clone());
                    }
                }
                self.fail("Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.".into(), n)
            }
            E::SetFilter { bound, pred } => {
                let s = self.eval_set(bound.set.as_ref().unwrap(), ctx)?;
                if !s.reducible() {
                    // the predicate may depend on the state: capture it for later (lazy) evaluation
                    return Ok(Value::Set(Rc::new(SetV::new(SetK::Filter(Box::new(FilterSet {
                        s,
                        node: n,
                        ctx: ctx.clone(),
                        cur: self.cur.borrow().clone(),
                        nxt: self.nxt.borrow().clone(),
                    }))))));
                }
                let es = s.elems()?;
                let mut out = Vec::new();
                for x in es {
                    let c = match &bound.tuple {
                        Some(t) => self.bind_tuple(t, x, ctx)?,
                        None => cons(bound.names.as_ref().unwrap()[0], x.clone(), ctx),
                    };
                    if self.eval_bool(pred, &c)? {
                        out.push(x.clone());
                    }
                }
                Ok(SetV::of(out))
            }
            E::SetMap { e, bounds } => {
                let mut out: Vec<Value> = Vec::new();
                let e: N = e;
                self.for_bindings(bounds, ctx, &mut |c| {
                    out.push(self.eval(e, c)?);
                    Ok(false)
                })?;
                mk_set(out)
            }
            E::FnDef { .. } => self.eval_fn_def(n, ctx),
            E::Rec(fields, shape) => {
                let mut vals = Vec::with_capacity(fields.len());
                for (_, e) in fields {
                    vals.push(self.eval(e, ctx)?);
                }
                let sh = shape.get_or_init(|| {
                    let mut idx: Vec<usize> = (0..fields.len()).collect();
                    idx.sort_by_key(|&i| fields[i].0 .0);
                    let sorted = idx.iter().enumerate().all(|(i, &j)| i == j);
                    RecShape { names: Rc::new(idx.iter().map(|&i| fields[i].0).collect()), order: if sorted { None } else { Some(idx) } }
                });
                let vals = match &sh.order {
                    None => vals,
                    Some(idx) => {
                        let mut slots: Vec<Option<Value>> = vals.into_iter().map(Some).collect();
                        idx.iter().map(|&i| slots[i].take().unwrap()).collect()
                    }
                };
                Ok(Value::Record(Rc::new(RecordV::new(sh.names.clone(), vals))))
            }
            E::RecSet(fields) => {
                let mut idx: Vec<usize> = (0..fields.len()).collect();
                idx.sort_by_key(|&i| fields[i].0 .0);
                let mut sets = Vec::with_capacity(fields.len());
                for &i in &idx {
                    sets.push(self.eval_set(&fields[i].1, ctx)?);
                }
                Ok(Value::Set(Rc::new(SetV::new(SetK::RecSet(Rc::new(idx.iter().map(|&i| fields[i].0).collect()), sets)))))
            }
            E::Except { base, updates } => {
                // (step-cache estimate: an EXCEPT on a variable reads the elements it replaces, when it uses them)
                let pv = if self.steps.on.get() { plain_var(base, ctx) } else { None };
                let mut f = match pv {
                    Some(_) => self.steps_quiet(base, ctx)?,
                    None => self.eval(base, ctx)?,
                };
                for (path, val) in updates {
                    // the keys of the path, on the stack when there are at most two (the usual case)
                    let mut short: [Value; 2] = [Value::Undef, Value::Undef];
                    let long: Vec<Value>;
                    let p: &[Value] = if path.len() <= 2 {
                        for (i, x) in path.iter().enumerate() {
                            short[i] = self.eval(x, ctx)?;
                        }
                        &short[..path.len()]
                    } else {
                        let mut v = Vec::with_capacity(path.len());
                        for x in path {
                            v.push(self.eval(x, ctx)?);
                        }
                        long = v;
                        &long
                    };
                    if let Some(i) = pv {
                        let plain = path.len() == 1 && (matches!(val.e, E::Num(_) | E::Bool(_) | E::Str(..)) || matches!(&val.e, E::App { args, sel: None, .. } if args.is_empty()));
                        if !plain {
                            let old = self.apply_fcn(&f, &p[0], None).and_then(|o| value_word(&o));
                            self.steps.elem(i as usize, value_word(&p[0]), old);
                        }
                    }
                    f = self.except_update(f, p, 0, val, ctx, n)?;
                }
                Ok(f)
            }
            E::FnApp { f, args } => {
                let fv = self.eval_fn_operand(f, ctx)?;
                let arg = self.eval_fn_arg(args, ctx)?;
                let v = self.apply_fcn(&fv, &arg, Some(n))?;
                if let Value::LazyFcn(lf) = &v {
                    return lf.force(self);
                }
                Ok(v)
            }
            E::Dot { e, field } => {
                let r = self.eval(e, ctx)?;
                if let Value::Record(rec) = &r {
                    return match rec.get(*field) {
                        Some(v) => Ok(v.clone()),
                        None => self.fail(format!("Attempted to access nonexistent field '{}' of record\n{}", str_of(*field), fmt(&r)), n),
                    };
                }
                self.fail(format!("Attempted to select field '{}' from the non-record value {}", str_of(*field), fmt(&r)), n)
            }
            E::Lambda { params, body } => Ok(Value::Closure(Rc::new(Closure { params, body, ctx: ctx.clone(), name: self.lambda }))),
            E::At => match self.lookup(ctx, self.at)? {
                Looked::Val(v) => Ok(v),
                _ => unreachable!(),
            },
            E::TQuant { .. } => self.fail("TLC attempted to evaluate a temporal formula where a state or action-level expression was expected.".into(), n),
            E::StepRef => self.fail("TLC does not support the construct 'stepref' here.".into(), n),
            E::AssumeProve => self.fail("TLC does not support the construct 'assumeprove' here.".into(), n),
        }
    }

    #[inline(never)]
    fn eval_op(&self, n: N, k: K, a: &'static [Node], ctx: &C) -> R<Value> {
        match k {
            K::And => {
                for x in a {
                    if !self.eval_bool(x, ctx)? {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            }
            K::Or => {
                for x in a {
                    if self.eval_bool(x, ctx)? {
                        return Ok(Value::Bool(true));
                    }
                }
                Ok(Value::Bool(false))
            }
            K::Not => Ok(Value::Bool(!self.eval_bool(&a[0], ctx)?)),
            K::Imp => Ok(Value::Bool(!self.eval_bool(&a[0], ctx)? || self.eval_bool(&a[1], ctx)?)),
            K::Eqv => Ok(Value::Bool(self.eval_bool(&a[0], ctx)? == self.eval_bool(&a[1], ctx)?)),
            K::Eq => Ok(Value::Bool(val_eq(&self.eval(&a[0], ctx)?, &self.eval(&a[1], ctx)?)?)),
            K::Ne => Ok(Value::Bool(!val_eq(&self.eval(&a[0], ctx)?, &self.eval(&a[1], ctx)?)?)),
            K::In | K::NotIn if self.steps.on.get() && plain_var(&a[1], ctx).is_some() => {
                // (step-cache estimate: x \in var reads one element)
                let x = self.eval(&a[0], ctx)?;
                let s = match self.steps_quiet(&a[1], ctx)? {
                    Value::Set(s) => s,
                    _ => return Ok(Value::Bool(self.eval_set(&a[1], ctx)?.contains(&x)? == (k == K::In))),
                };
                let r = s.contains(&x)?;
                self.steps.elem(plain_var(&a[1], ctx).unwrap() as usize, value_word(&x), Ok(r as u64));
                Ok(Value::Bool(r == (k == K::In)))
            }
            K::In => {
                let x = self.eval(&a[0], ctx)?;
                Ok(Value::Bool(self.eval_set(&a[1], ctx)?.contains(&x)?))
            }
            K::NotIn => {
                let x = self.eval(&a[0], ctx)?;
                Ok(Value::Bool(!self.eval_set(&a[1], ctx)?.contains(&x)?))
            }
            K::Cup | K::Diff if self.steps.on.get() && plain_var(&a[0], ctx).is_some() => {
                // (step-cache estimate: var \cup S and var \ S are changes to the variable, not reads of it)
                let x = match self.steps_quiet(&a[0], ctx)? {
                    Value::Set(s) => s,
                    _ => self.eval_set(&a[0], ctx)?,
                };
                let y = self.eval_set(&a[1], ctx)?;
                if k == K::Cup {
                    return self.set_union(x, y);
                }
                if x.reducible() {
                    let mut out = Vec::new();
                    for e in x.elems()? {
                        if !y.contains(e)? {
                            out.push(e.clone());
                        }
                    }
                    return Ok(SetV::of(out));
                }
                Ok(Value::Set(Rc::new(SetV::new(SetK::Diff(x, y)))))
            }
            K::Subseteq => {
                let (mut x, mut y) = (self.eval_set(&a[0], ctx)?, self.eval_set(&a[1], ctx)?);
                // SUBSET A \subseteq SUBSET B  iff  A \subseteq B
                loop {
                    let (bx, by) = match (&x.k, &y.k) {
                        (SetK::Subset(bx), SetK::Subset(by)) => (bx.clone(), by.clone()),
                        _ => break,
                    };
                    x = bx;
                    y = by;
                }
                if !x.enumerable() {
                    return self.fail(format!("Attempted to check if the non-enumerable set {} is a subset of {}", fmt_set(&x), fmt_set(&y)), n);
                }
                if let (SetK::Interval(l1, h1), SetK::Interval(l2, h2)) = (&x.k, &y.k) {
                    return Ok(Value::Bool(h1 < l1 || (l1 >= l2 && h1 <= h2)));
                }
                for e in x.elems()? {
                    if !y.contains(e)? {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            }
            K::Cup => self.set_union(self.eval_set(&a[0], ctx)?, self.eval_set(&a[1], ctx)?),
            K::Cap => {
                let (x, y) = (self.eval_set(&a[0], ctx)?, self.eval_set(&a[1], ctx)?);
                if x.reducible() && y.reducible() {
                    let mut out = Vec::new();
                    for e in x.elems()? {
                        if y.contains(e)? {
                            out.push(e.clone());
                        }
                    }
                    return Ok(SetV::of(out));
                }
                Ok(Value::Set(Rc::new(SetV::new(SetK::Cap(x, y)))))
            }
            K::Diff => {
                let (x, y) = (self.eval_set(&a[0], ctx)?, self.eval_set(&a[1], ctx)?);
                if x.reducible() {
                    let mut out = Vec::new();
                    for e in x.elems()? {
                        if !y.contains(e)? {
                            out.push(e.clone());
                        }
                    }
                    return Ok(SetV::of(out));
                }
                Ok(Value::Set(Rc::new(SetV::new(SetK::Diff(x, y)))))
            }
            K::Powerset => Ok(Value::Set(Rc::new(SetV::new(SetK::Subset(self.eval_set(&a[0], ctx)?))))),
            K::BigUnion => {
                let s = self.eval_set(&a[0], ctx)?;
                let es = self.elems_at(&s, &a[0])?;
                // TLC keeps UNION lazy (UnionValue) unless every element is an explicit set: membership works
                // even over non-enumerable sets, and nothing is enumerated until it has to be.
                if es.iter().any(|x| matches!(x, Value::Set(xs) if !matches!(xs.k, SetK::Enum(_)))) {
                    let mut sets: Vec<Rc<SetV>> = Vec::with_capacity(es.len());
                    for x in es {
                        match x {
                            Value::Set(xs) => sets.push(xs.clone()),
                            _ => return self.fail(format!("Attempted to apply UNION to a set containing the non-set value {}", fmt(x)), n),
                        }
                    }
                    return Ok(Value::Set(Rc::new(SetV::new(SetK::Union(sets)))));
                }
                let mut all: Vec<Value> = Vec::new();
                for x in es {
                    match x {
                        Value::Set(xs) => all.extend_from_slice(xs.elems()?),
                        _ => return self.fail(format!("Attempted to apply UNION to a set containing the non-set value {}", fmt(x)), n),
                    }
                }
                mk_set(all)
            }
            K::Domain => {
                let pv = if self.steps.on.get() { plain_var(&a[0], ctx) } else { None };
                let f = match pv {
                    Some(_) => self.steps_quiet(&a[0], ctx)?,
                    None => self.eval_fn_operand(&a[0], ctx)?,
                };
                if let Value::LazyFcn(lf) = &f {
                    return Ok(Value::Set(lf.domain(self)?));
                }
                match domain_of(&f) {
                    Some(d) => {
                        let d = Value::Set(d);
                        if let Some(i) = pv {
                            self.steps_domain(i as usize, &d);
                        }
                        Ok(d)
                    }
                    None => self.fail(format!("Attempted to apply the operator DOMAIN to the non-function value\n{}", fmt(&f)), n),
                }
            }
            K::Prime => {
                let sn = match self.nxt.borrow_mut().take() {
                    Some(s) => s,
                    None => return self.fail("Attempted to evaluate a primed expression where no next state is available (the expression is not a state-level expression).".into(), n),
                };
                let im = self.init_mode.get();
                let sc = self.cur.replace(sn);
                self.prime_depth.set(self.prime_depth.get() + 1);
                self.init_mode.set(false);
                let r = self.eval(&a[0], ctx);
                let sn = self.cur.replace(sc);
                *self.nxt.borrow_mut() = Some(sn);
                self.prime_depth.set(self.prime_depth.get() - 1);
                self.init_mode.set(im);
                r
            }
            K::Enabled => Ok(Value::Bool(self.enabled(&a[0], ctx)?)),
            K::Unchanged => {
                let v0 = self.eval(&a[0], ctx)?;
                if self.nxt.borrow().is_none() {
                    return self.fail("Attempted to evaluate UNCHANGED where no next state is available.".into(), n);
                }
                Ok(Value::Bool(self.primed_eq(&a[0], ctx, &v0)?))
            }
            K::Cross => {
                let mut sets = Vec::with_capacity(a.len());
                for x in a {
                    sets.push(self.eval_set(x, ctx)?);
                }
                Ok(Value::Set(Rc::new(SetV::new(SetK::Cross(sets)))))
            }
            K::If => {
                if self.eval_bool(&a[0], ctx)? {
                    self.eval(&a[1], ctx)
                } else {
                    self.eval(&a[2], ctx)
                }
            }
            K::SetEnum => {
                let mut out = Vec::with_capacity(a.len());
                for x in a {
                    out.push(self.eval(x, ctx)?);
                }
                mk_set(out)
            }
            K::FnSet => Ok(Value::Set(Rc::new(SetV::new(SetK::FcnSet(self.eval_set(&a[0], ctx)?, self.eval_set(&a[1], ctx)?))))),
            K::Tuple => {
                let mut out = Vec::with_capacity(a.len());
                for x in a {
                    out.push(self.eval(x, ctx)?);
                }
                Ok(Value::Tuple(TupleV::rc(out)))
            }
            K::BoxAct => Ok(Value::Bool(self.eval_bool(&a[0], ctx)? || self.unchanged_val(&a[1], ctx)?)),
            K::AngleAct => Ok(Value::Bool(self.eval_bool(&a[0], ctx)? && !self.unchanged_val(&a[1], ctx)?)),
            K::Cdot if !cdot_enabled() => self.fail(NO_CDOT.into(), n),
            K::Cdot => match self.enumerate(n, ctx, &mut || Err(Box::new(Fail::Found))) {
                Ok(()) => Ok(Value::Bool(false)),
                Err(e) if matches!(*e, Fail::Found) => Ok(Value::Bool(true)),
                Err(e) => Err(e),
            },
            K::Always | K::Eventually | K::LeadsTo | K::Wf | K::Sf | K::Guarantee => {
                self.fail("TLC attempted to evaluate a temporal formula where a state or action-level expression was expected.".into(), n)
            }
        }
    }

    /// The function operand of f[x] / DOMAIN f: kept lazy when it can be a function constructor.
    #[inline]
    fn eval_fn_operand(&self, f: N, ctx: &C) -> R<Value> {
        let tf = f.tf.get();
        if if tf >= 0 { tf == 1 } else { crate::modules::tail_fn(f) } {
            self.eval_lazy(f, ctx)
        } else if let E::App { name, args, sel, r, .. } = &f.e {
            // An operator parameter or bound identifier: TLC forces its lazy value in keep-lazy mode too, so
            // `Op(f, x) == f[x]` applied to a function definition computes one point, not the whole function.
            if let Res::Decl(d) = r.get() {
                // a state variable (pc[self], grid[p]): read it directly
                if d.is_var && ctx.as_ref().map_or(true, |c| !c.env && c.base.is_none()) {
                    let idx = d.idx.get();
                    if idx >= 0 {
                        let v = self.cur.borrow().get(idx as usize);
                        if !matches!(v, Value::Undef) {
                            if self.prime_depth.get() > 0 {
                                self.pr_touch.set(self.pr_touch.get() + 1);
                            } else {
                                self.st_touch.set(self.st_touch.get() + 1);
                            }
                            return Ok(v);
                        }
                    }
                }
            }
            if args.is_empty() && sel.is_none() && matches!(r.get(), Res::Local) {
                match self.lookup(ctx, *name)? {
                    Looked::Val(Value::Thunk(lz)) => return self.force_lazy(&lz),
                    Looked::Val(v) if matches!(v, Value::Tuple(_) | Value::Record(_) | Value::Fcn(_) | Value::LazyFcn(_)) => return Ok(v),
                    _ => {}
                }
            }
            self.eval_app(f, ctx)
        } else {
            self.eval(f, ctx)
        }
    }
    #[inline]
    pub(crate) fn eval_fn_arg(&self, args: &'static [Node], ctx: &C) -> R<Value> {
        if args.len() == 1 {
            return self.eval(&args[0], ctx);
        }
        let mut t = Vec::with_capacity(args.len());
        for a in args {
            t.push(self.eval(a, ctx)?);
        }
        Ok(Value::Tuple(TupleV::rc(t)))
    }

    /// Evaluate in TLC's "keep lazy" mode: a function constructor reached through IF/CASE/LET/definitions is
    /// returned as an unevaluated LazyFcn (the caller applies it, takes its DOMAIN or enumerates its body).
    pub fn eval_lazy(&self, n: N, ctx: &C) -> R<Value> {
        match &n.e {
            E::FnDef { .. } => return Ok(Value::LazyFcn(LazyFcn::new(n, ctx.clone()))),
            E::Op(K::If, a) => return if self.eval_bool(&a[0], ctx)? { self.eval_lazy(&a[1], ctx) } else { self.eval_lazy(&a[2], ctx) },
            E::Case { arms, other } => {
                for (c, e) in arms {
                    if self.eval_bool(c, ctx)? {
                        return self.eval_lazy(e, ctx);
                    }
                }
                if let Some(o) = other {
                    return self.eval_lazy(o, ctx);
                }
                return self.fail("Attempted to evaluate a CASE expression in which none of the conditions were true.".into(), n);
            }
            E::Let { defs, body } => return self.eval_lazy(body, &self.bind_let(defs, ctx)),
            E::FnApp { f, args } => {
                if crate::modules::tail_fn(n) {
                    let fv = self.eval_lazy(f, ctx)?;
                    let arg = self.eval_fn_arg(args, ctx)?;
                    return match &fv {
                        Value::LazyFcn(lf) => lf.apply(self, &arg, true),
                        _ => self.apply_fcn(&fv, &arg, Some(n)),
                    };
                }
            }
            E::App { name, r, .. } => {
                if !crate::modules::tail_fn(n) {
                    return self.eval_app(n, ctx);
                }
                match r.get() {
                    Res::Local => {
                        return match self.lookup(ctx, *name)? {
                            Looked::Val(Value::Thunk(lz)) => self.force_lazy(&lz),
                            Looked::LetLazy(node, head) => self.force_let(&node, head, true),
                            _ => self.eval_app(n, ctx),
                        };
                    }
                    Res::Def(d) => {
                        let def = d.resolved();
                        if def.builtin.get().is_none() {
                            let top = def.params.is_empty() && def.inst.is_none() && base_of(ctx).is_none();
                            if top {
                                if let Some(v) = def.cache.borrow().as_ref() {
                                    return Ok(v.clone());
                                }
                            }
                            if let Some((b, c)) = self.expand_app(n, ctx)? {
                                let (s0, p0) = (self.st_touch.get(), self.pr_touch.get());
                                let v = self.eval_lazy(b, &c)?;
                                if top && crate::modules::def_level(def) == 0 && self.st_touch.get() == s0 && self.pr_touch.get() == p0 {
                                    // a constant: evaluate it completely once (TLC precomputes constant definitions),
                                    // unless that fails
                                    let mut w = v.clone();
                                    if let Value::LazyFcn(lf) = &v {
                                        match lf.force(self) {
                                            Ok(x) => w = x,
                                            Err(e) if matches!(*e, Fail::Tla(_)) => {}
                                            Err(e) => return Err(e),
                                        }
                                        if self.st_touch.get() != s0 || self.pr_touch.get() != p0 {
                                            return Ok(v);
                                        }
                                    }
                                    *def.cache.borrow_mut() = Some(w.clone());
                                    return Ok(w);
                                }
                                return Ok(v);
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        self.eval(n, ctx)
    }

    /// Evaluates `e` in the next state and compares it with `v0` (the value in the current state).
    fn primed_eq(&self, e: N, ctx: &C, v0: &Value) -> R<bool> {
        let sn = self.nxt.borrow_mut().take().unwrap();
        let sc = self.cur.replace(sn);
        self.prime_depth.set(self.prime_depth.get() + 1);
        let r = self.eval(e, ctx);
        let sn = self.cur.replace(sc);
        *self.nxt.borrow_mut() = Some(sn);
        self.prime_depth.set(self.prime_depth.get() - 1);
        val_eq(&r?, v0)
    }

    fn unchanged_val(&self, e: N, ctx: &C) -> R<bool> {
        let v0 = self.eval(e, ctx)?;
        if self.nxt.borrow().is_none() {
            return self.fail("Attempted to evaluate an action where no next state is available.".into(), e);
        }
        self.primed_eq(e, ctx, &v0)
    }

    pub(crate) fn set_union(&self, a: Rc<SetV>, b: Rc<SetV>) -> R<Value> {
        if !a.reducible() || !b.reducible() {
            return Ok(Value::Set(Rc::new(SetV::new(SetK::Cup(a, b)))));
        }
        let (x, y) = (a.elems()?, b.elems()?);
        if x.is_empty() {
            return Ok(Value::Set(b.clone()));
        }
        if y.is_empty() {
            return Ok(Value::Set(a.clone()));
        }
        let mut out = Vec::with_capacity(x.len() + y.len());
        let (mut i, mut j) = (0, 0);
        while i < x.len() && j < y.len() {
            match compare(&x[i], &y[j])? {
                std::cmp::Ordering::Less => {
                    out.push(x[i].clone());
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    out.push(y[j].clone());
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    out.push(x[i].clone());
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&x[i..]);
        out.extend_from_slice(&y[j..]);
        Ok(SetV::of(out))
    }

    fn eval_fn_def(&self, n: N, ctx: &C) -> R<Value> {
        let (bounds, body, is_rec) = match &n.e {
            E::FnDef { bounds, body, is_rec, .. } => (bounds, &**body, is_rec.get()),
            _ => unreachable!(),
        };
        let lazy = || Value::LazyFcn(LazyFcn::new(n, ctx.clone()));
        if is_rec {
            return Ok(lazy());
        }
        if bounds.len() == 1 && (bounds[0].tuple.is_some() || bounds[0].names.as_ref().unwrap().len() == 1) {
            let b = &bounds[0];
            let s = self.eval_set(b.set.as_ref().unwrap(), ctx)?;
            if !s.enumerable() {
                return Ok(lazy());
            }
            if let (SetK::Interval(1, hi), None) = (&s.k, &b.tuple) {
                // [i \in 1..n |-> e] is a sequence: no domain needs to be materialized
                let nm = b.names.as_ref().unwrap()[0];
                let mut vals = Vec::with_capacity((*hi).max(0) as usize);
                for i in 1..=*hi {
                    vals.push(self.eval(body, &cons(nm, Value::Int(i), ctx))?);
                }
                return Ok(if vals.is_empty() { empty_tuple() } else { Value::Tuple(TupleV::rc(vals)) });
            }
            let dom = s.elems()?;
            let mut vals = Vec::with_capacity(dom.len());
            match &b.tuple {
                Some(t) => {
                    for d in dom {
                        vals.push(self.eval(body, &self.bind_tuple(t, d, ctx)?)?);
                    }
                }
                None => {
                    let nm = b.names.as_ref().unwrap()[0];
                    for d in dom {
                        vals.push(self.eval(body, &cons(nm, d.clone(), ctx))?);
                    }
                }
            }
            return Ok(s.fcn_shape()?.make(vals));
        }
        let mut dom: Vec<Value> = vec![];
        let mut vals: Vec<Value> = vec![];
        let mut sets: Vec<Rc<SetV>> = vec![];
        enum Nm {
            One(Name),
            Tup(&'static [Name]),
        }
        let mut names: Vec<Nm> = vec![];
        let mut bsets: Vec<Rc<SetV>> = Vec::with_capacity(bounds.len());
        for b in bounds.iter() {
            let bs = self.eval_set(b.set.as_ref().unwrap(), ctx)?;
            if !bs.enumerable() {
                return Ok(lazy());
            }
            bsets.push(bs);
        }
        for (bi, b) in bounds.iter().enumerate() {
            let set = b.set.as_ref().unwrap();
            let s = bsets[bi].clone();
            self.elems_at(&s, set)?;
            match &b.tuple {
                Some(t) => {
                    sets.push(s);
                    names.push(Nm::Tup(t));
                }
                None => {
                    for nm in b.names.as_ref().unwrap() {
                        sets.push(s.clone());
                        names.push(Nm::One(*nm));
                    }
                }
            }
        }
        struct St<'a> {
            ev: &'a Evaluator,
            sets: &'a [Rc<SetV>],
            names: &'a [Nm],
            body: N,
            cur: Vec<Value>,
            dom: &'a mut Vec<Value>,
            vals: &'a mut Vec<Value>,
        }
        fn rec(st: &mut St, i: usize, c: &C) -> R<()> {
            if i == st.sets.len() {
                st.dom.push(Value::Tuple(TupleV::rc(st.cur.clone())));
                st.vals.push(st.ev.eval(st.body, c)?);
                return Ok(());
            }
            let sets = st.sets;
            for v in sets[i].elems()? {
                st.cur.push(v.clone());
                let c2 = match &st.names[i] {
                    Nm::One(nm) => cons(*nm, v.clone(), c),
                    Nm::Tup(t) => st.ev.bind_tuple(t, v, c)?,
                };
                rec(st, i + 1, &c2)?;
                st.cur.pop();
            }
            Ok(())
        }
        rec(&mut St { ev: self, sets: &sets, names: &names, body, cur: vec![], dom: &mut dom, vals: &mut vals }, 0, ctx)?;
        Ok(make_fcn(&dom, vals))
    }

    pub fn apply_fcn(&self, f: &Value, arg: &Value, n: Option<N>) -> R<Value> {
        let r = match f {
            Value::Tuple(t) => match arg {
                Value::Int(i) if *i >= 1 && *i as usize <= t.len() => return Ok(t[*i as usize - 1].clone()),
                Value::Int(i) => eval_err(format!("Attempted to apply tuple\n{}\nto integer {} which is out of domain.", fmt(f), i)),
                _ => eval_err(format!("Attempted to apply tuple\n{}\nto non-integer argument {}", fmt(f), fmt(arg))),
            },
            Value::Record(r) => {
                if let Value::Str(s) = arg {
                    if let Some(v) = r.get(*s) {
                        return Ok(v.clone());
                    }
                }
                eval_err(format!("Attempted to apply function:\n{}\nto argument {}, which is not in the domain of the function.", fmt(f), fmt(arg)))
            }
            Value::Fcn(fc) => match bsearch(&fc.dom, arg) {
                Ok(Some(i)) => return Ok(fc.vals[i].clone()),
                Ok(None) => eval_err(format!("Attempted to apply function:\n{}\nto argument {}, which is not in the domain of the function.", fmt(f), fmt(arg))),
                Err(e) => Err(e),
            },
            Value::LazyFcn(lf) => return lf.apply(self, arg, false),
            Value::Closure(_) | Value::DefRef(_) => eval_err("Attempted to apply an operator as if it were a function (use parentheses, not brackets).".into()),
            _ => eval_err(format!("A non-function ({}) was applied as a function.", fmt(f))),
        };
        match n {
            Some(n) => self.at_node(r, n),
            None => r,
        }
    }

    fn except_update(&self, f: Value, path: &[Value], i: usize, val_node: N, ctx: &C, n: N) -> R<Value> {
        self.except_with(f, path, i, &mut |old: Value| -> R<Value> {
            if matches!(val_node.e, E::Num(_) | E::Bool(_) | E::Str(..)) || matches!(&val_node.e, E::App { args, sel: None, .. } if args.is_empty()) {
                // a literal or a name: `@` cannot occur in it, so it needs no binding
                return self.eval(val_node, ctx);
            }
            self.eval(val_node, &cons(self.at, old, ctx))
        }, n)
    }
    /// `[f EXCEPT !path = leaf(old)]` from position `i` of the path: `leaf` computes the new value of the
    /// element from its old one.
    pub(crate) fn except_with(&self, f: Value, path: &[Value], i: usize, leaf: &mut dyn FnMut(Value) -> R<Value>, n: N) -> R<Value> {
        let key = &path[i];
        let last = i == path.len() - 1;
        let mut upd = |old: Value| -> R<Value> {
            if last {
                leaf(old)
            } else {
                self.except_with(old, path, i + 1, &mut *leaf, n)
            }
        };
        match f {
            Value::Tuple(mut t) => {
                let k = match key {
                    Value::Int(k) if *k >= 1 && *k as usize <= t.len() => *k as usize - 1,
                    _ => return Ok(Value::Tuple(t)),
                };
                let nv = upd(t[k].clone())?;
                match Rc::get_mut(&mut t) {
                    Some(v) => {
                        v.e[k] = nv;
                        v.h.set(0);
                        Ok(Value::Tuple(t))
                    }
                    None => {
                        let mut e = t.e.clone();
                        e[k] = nv;
                        Ok(Value::Tuple(TupleV::rc(e)))
                    }
                }
            }
            Value::Record(mut r) => {
                let k = match key {
                    Value::Str(s) => r.names.iter().position(|x| x == s),
                    _ => None,
                };
                let k = match k {
                    Some(k) => k,
                    None => return Ok(Value::Record(r)),
                };
                let nv = upd(r.vals[k].clone())?;
                match Rc::get_mut(&mut r) {
                    Some(v) => {
                        v.vals[k] = nv;
                        v.h.set(0);
                        Ok(Value::Record(r))
                    }
                    None => {
                        let mut vals = r.vals.clone();
                        vals[k] = nv;
                        Ok(Value::Record(Rc::new(RecordV::new(r.names.clone(), vals))))
                    }
                }
            }
            Value::Fcn(mut fc) => {
                let k = match bsearch(&fc.dom, key)? {
                    Some(k) => k,
                    None => return Ok(Value::Fcn(fc)),
                };
                let nv = upd(fc.vals[k].clone())?;
                match Rc::get_mut(&mut fc) {
                    Some(v) => {
                        v.vals[k] = nv;
                        v.h.set(0);
                        Ok(Value::Fcn(fc))
                    }
                    None => {
                        let mut vals = fc.vals.clone();
                        vals[k] = nv;
                        Ok(Value::Fcn(Rc::new(FcnV::new(fc.dom.clone(), vals))))
                    }
                }
            }
            Value::LazyFcn(lf) => {
                let d = lf.domain(self)?;
                if d.enumerable() {
                    drop(upd);
                    return self.except_with(lf.force(self)?, path, i, leaf, n);
                }
                if !d.contains(key)? {
                    return Ok(Value::LazyFcn(lf));
                }
                let nv = upd(lf.apply(self, key, false)?)?;
                Ok(Value::LazyFcn(lf.with_override(key.clone(), nv)))
            }
            f => self.fail(format!("Attempted to apply EXCEPT to the non-function value\n{}", fmt(&f)), n),
        }
    }

    // ---------- lazy filtered sets ----------
    fn in_state<T>(&self, f: &FilterSet, g: impl FnOnce() -> R<T>) -> R<T> {
        let c0 = self.cur.replace(f.cur.clone());
        let n0 = self.nxt.replace(f.nxt.clone());
        let r = g();
        *self.cur.borrow_mut() = c0;
        *self.nxt.borrow_mut() = n0;
        r
    }
    fn filter_pred(&self, f: &FilterSet, v: &Value) -> R<bool> {
        let (bound, pred) = match &f.node.e {
            E::SetFilter { bound, pred } => (bound, &**pred),
            _ => unreachable!(),
        };
        let c = match &bound.tuple {
            Some(t) => self.bind_tuple(t, v, &f.ctx)?,
            None => cons(bound.names.as_ref().unwrap()[0], v.clone(), &f.ctx),
        };
        self.eval_bool(pred, &c)
    }
    pub fn filter_test(&self, f: &FilterSet, v: &Value) -> R<bool> {
        self.in_state(f, || self.filter_pred(f, v))
    }
    pub fn filter_elems(&self, f: &FilterSet) -> R<Vec<Value>> {
        self.in_state(f, || {
            let mut out = Vec::new();
            for x in f.s.elems()? {
                if self.filter_pred(f, x)? {
                    out.push(x.clone());
                }
            }
            Ok(out)
        })
    }

    // ---------- ENABLED ----------
    fn enabled(&self, a: N, ctx: &C) -> R<bool> {
        self.enabled_by(ctx, &mut |c, k| self.enumerate(a, c, k))
    }
    /// ENABLED <<A>>_v for an action and subscript given separately (fairness conditions).
    pub fn enabled_angle(&self, a: N, v: N, ctx: &C) -> R<bool> {
        self.enabled_by(ctx, &mut |c, k| {
            self.enumerate(a, c, &mut || {
                if !self.unchanged_val(v, c)? {
                    return k();
                }
                Ok(())
            })
        })
    }
    /// <<A>>_v as a predicate on a pair of states.
    pub fn eval_angle(&self, a: N, v: N, ctx: &C) -> R<bool> {
        Ok(self.eval_bool(a, ctx)? && !self.unchanged_val(v, ctx)?)
    }
    #[allow(clippy::type_complexity)]
    fn enabled_by(&self, ctx: &C, run: &mut dyn FnMut(&C, &mut dyn FnMut() -> R<()>) -> R<()>) -> R<bool> {
        let marked: C;
        let mut ctx = ctx;
        let base = base_of(ctx);
        if let Some(b) = &base {
            if b.name != self.enabled_mark {
                // mark the instance environment the ENABLED is evaluated in (see as_var)
                let env = Rc::new(Ctx { name: self.enabled_mark, val: Bind::Val(Value::Bool(true)), next: base.clone(), base: None, env: true, let_head: false });
                marked = Some(Rc::new(Ctx { name: self.enabled_mark, val: Bind::Val(Value::Bool(true)), next: ctx.clone(), base: Some(env), env: false, let_head: false }));
                ctx = &marked;
            }
        }
        let sn = self.nxt.replace(Some(StateData::blank(self.nvars.get())));
        let (im, na, cd) = (self.init_mode.get(), self.n_assigned.get(), self.call_depth.get());
        self.init_mode.set(false);
        self.n_assigned.set(-1_000_000_000); // no all-assigned shortcut inside ENABLED
        self.in_enabled.set(self.in_enabled.get() + 1);
        let r = run(ctx, &mut || Err(Box::new(Fail::Found)));
        *self.nxt.borrow_mut() = sn;
        self.init_mode.set(im);
        self.n_assigned.set(na);
        self.call_depth.set(cd);
        self.in_enabled.set(self.in_enabled.get() - 1);
        match r {
            Ok(()) => Ok(false),
            Err(e) if matches!(*e, Fail::Found) => Ok(true),
            Err(e) => Err(e),
        }
    }

    // ---------- action / initial-predicate enumeration ----------
    /// Resolve an expression to a variable index if it denotes a variable (possibly through substitutions).
    pub fn as_var(&self, e: N, ctx: &C) -> R<i64> {
        if let Some(i) = plain_var(e, ctx) {
            return Ok(i);
        }
        let mut e = e;
        let mut ctx = ctx.clone();
        for _ in 0..100 {
            if let E::Let { defs, body } = &e.e {
                ctx = self.bind_let(defs, &ctx);
                e = body;
                continue;
            }
            let (name, r) = match &e.e {
                E::App { name, args, sel, r, .. } if args.is_empty() && sel.is_none() => (*name, r.get()),
                _ => return Ok(-1),
            };
            match r {
                Res::Local => match self.lookup(&ctx, name)? {
                    Looked::Val(Value::Thunk(lz)) => {
                        e = lz.e;
                        ctx = lz.ctx.clone();
                        continue;
                    }
                    Looked::LetLazy(node, head) => {
                        if let Bind::LetLazy { body, .. } = &node.val {
                            e = body;
                            ctx = Some(head);
                        }
                        continue;
                    }
                    _ => return Ok(-1),
                },
                Res::Def(_) => match self.expand_app(e, &ctx)? {
                    None => return Ok(-1),
                    Some((b, c)) => {
                        e = b;
                        ctx = c;
                        continue;
                    }
                },
                Res::Decl(d) if d.is_var => {
                    let base = base_of(&ctx);
                    if let Some(bh) = &base {
                        match self.env_lookup(&base, name) {
                            Some(Value::Thunk(lz)) => {
                                if bh.name == self.enabled_mark {
                                    // Like TLC's context cut-off: a variable of an instantiated module that is reached from
                                    // inside an ENABLED evaluated in that module stands for itself, not for the expression
                                    // substituted for it.
                                    let mut sc = self.scratch.borrow_mut();
                                    let key = d as *const Decl;
                                    if let Some(x) = sc.iter().find(|x| x.0 == key) {
                                        return Ok(x.1 as i64);
                                    }
                                    let si = self.nvars.get() + sc.len();
                                    sc.push((key, si));
                                    return Ok(si as i64);
                                }
                                e = lz.e;
                                ctx = lz.ctx.clone();
                                continue;
                            }
                            Some(_) => return Ok(-1),
                            None => {}
                        }
                    }
                    return Ok(d.idx.get() as i64);
                }
                _ => return Ok(-1),
            }
        }
        Ok(-1)
    }

    fn target_var(&self, lhs: N, ctx: &C) -> R<i64> {
        if self.init_mode.get() {
            return if matches!(lhs.e, E::App { .. }) { self.as_var(lhs, ctx) } else { Ok(-1) };
        }
        if self.nxt.borrow().is_none() || self.prime_depth.get() > 0 {
            return Ok(-1);
        }
        match &lhs.e {
            E::Op(K::Prime, a) => return self.as_var(&a[0], ctx),
            E::Let { .. } => {}
            E::App { args, .. } if args.is_empty() => {}
            _ => return Ok(-1),
        }
        // look through operator parameters bound to primed variables, e.g. Send(p, d, mem, mem')
        let mut lhs = lhs;
        let mut ctx = ctx.clone();
        for _ in 0..100 {
            match &lhs.e {
                E::Let { defs, body } => {
                    ctx = self.bind_let(defs, &ctx);
                    lhs = body;
                }
                E::App { name, args, r, sel, .. } if args.is_empty() => match r.get() {
                    Res::Local => match self.lookup(&ctx, *name)? {
                        Looked::Val(Value::Thunk(lz)) => {
                            lhs = lz.e;
                            ctx = lz.ctx.clone();
                        }
                        Looked::LetLazy(node, head) => {
                            if let Bind::LetLazy { body, .. } = &node.val {
                                lhs = body;
                                ctx = Some(head);
                            }
                        }
                        _ => return Ok(-1),
                    },
                    Res::Def(_) if sel.is_none() => match self.expand_app(lhs, &ctx)? {
                        // a definition whose body is a primed variable (a == x')
                        None => return Ok(-1),
                        Some((b, c)) => {
                            lhs = b;
                            ctx = c;
                        }
                    },
                    _ => return Ok(-1),
                },
                _ => break,
            }
        }
        match &lhs.e {
            E::Op(K::Prime, a) => self.as_var(&a[0], &ctx),
            _ => Ok(-1),
        }
    }

    fn target_state(&self) -> StateRef {
        if self.init_mode.get() {
            self.cur.borrow().clone()
        } else {
            self.nxt.borrow().as_ref().unwrap().clone()
        }
    }

    /// Enumerate all ways of satisfying `e`, assigning unassigned target variables (primed variables in
    /// next-state mode, unprimed variables in init mode). Calls k for each satisfying (partial) assignment.
    pub fn enumerate(&self, e: N, ctx: &C, k: &mut dyn FnMut() -> R<()>) -> R<()> {
        // Like TLC: once every variable is assigned, the remaining conjuncts are plain predicates.
        if self.n_assigned.get() == self.nvars.get() as i64 && !e.is_k(K::Cdot) {
            if self.eval_bool(e, ctx)? {
                return k();
            }
            return Ok(());
        }
        match &e.e {
            E::Op(kind, a) => match kind {
                K::Cdot if !cdot_enabled() => return self.fail(NO_CDOT.into(), e),
                K::Cdot => {
                    // s -(A \cdot B)-> u  iff  there is a t with  s -A-> t  and  t -B-> u
                    if !self.init_mode.get() {
                        let nv = self.nvars.get();
                        let na = self.n_assigned.get();
                        let mid = StateData::blank(nv);
                        let sn = self.nxt.replace(Some(mid.clone()));
                        self.n_assigned.set(0);
                        let mut mids: Vec<StateRef> = vec![];
                        let r = self.enumerate(&a[0], ctx, &mut || {
                            for i in 0..nv {
                                if mid.is_undef(i) {
                                    return self.fail("The first action of an action composition (\\cdot) does not completely specify the intermediate state.".into(), e);
                                }
                            }
                            mids.push(StateData::new(mid.snapshot(nv)));
                            Ok(())
                        });
                        *self.nxt.borrow_mut() = sn;
                        self.n_assigned.set(na);
                        r?;
                        if self.in_enabled.get() == 0 {
                            self.extra_generated.set(self.extra_generated.get() + mids.len() as u64);
                        }
                        let sc = self.cur.borrow().clone();
                        for t in mids {
                            *self.cur.borrow_mut() = t.clone();
                            let r = self.enumerate(&a[1], ctx, &mut || {
                                let c = self.cur.replace(sc.clone());
                                let r = k();
                                *self.cur.borrow_mut() = c;
                                r
                            });
                            *self.cur.borrow_mut() = sc.clone();
                            r?;
                        }
                        return Ok(());
                    }
                }
                K::And => return self.enum_conj(a, 0, ctx, k),
                K::Or => {
                    for d in a {
                        self.enumerate(d, ctx, k)?;
                    }
                    return Ok(());
                }
                K::Imp => {
                    if !self.eval_bool(&a[0], ctx)? {
                        return k();
                    }
                    return self.enumerate(&a[1], ctx, k);
                }
                K::Subseteq => {
                    let tgt = self.target_var(&a[0], ctx)?;
                    if tgt >= 0 {
                        let arr = self.target_state();
                        let tgt = tgt as usize;
                        if arr.is_undef(tgt) {
                            let sub = SetV::new(SetK::Subset(self.eval_set(&a[1], ctx)?));
                            let es = sub.elems()?;
                            self.n_assigned.set(self.n_assigned.get() + 1);
                            let mut r = Ok(());
                            for x in es {
                                arr.set(tgt, x.clone());
                                r = k();
                                if r.is_err() {
                                    break;
                                }
                            }
                            arr.set(tgt, Value::Undef);
                            self.n_assigned.set(self.n_assigned.get() - 1);
                            return r;
                        }
                    }
                }
                K::If => {
                    return if self.eval_bool(&a[0], ctx)? { self.enumerate(&a[1], ctx, k) } else { self.enumerate(&a[2], ctx, k) };
                }
                K::Eq => {
                    let tgt = self.target_var(&a[0], ctx)?;
                    if tgt >= 0 {
                        let arr = self.target_state();
                        let tgt = tgt as usize;
                        if arr.is_undef(tgt) {
                            let v = self.eval(&a[1], ctx)?;
                            arr.set(tgt, v);
                            self.n_assigned.set(self.n_assigned.get() + 1);
                            let r = k();
                            arr.set(tgt, Value::Undef);
                            self.n_assigned.set(self.n_assigned.get() - 1);
                            return r;
                        }
                    }
                }
                K::In => {
                    let tgt = self.target_var(&a[0], ctx)?;
                    if tgt >= 0 {
                        let arr = self.target_state();
                        let tgt = tgt as usize;
                        if arr.is_undef(tgt) {
                            let s = self.eval_set(&a[1], ctx)?;
                            let es = s.elems()?;
                            self.n_assigned.set(self.n_assigned.get() + 1);
                            let mut r = Ok(());
                            for x in es {
                                arr.set(tgt, x.clone());
                                r = k();
                                if r.is_err() {
                                    break;
                                }
                            }
                            arr.set(tgt, Value::Undef);
                            self.n_assigned.set(self.n_assigned.get() - 1);
                            return r;
                        }
                    }
                }
                K::Unchanged => {
                    if !self.init_mode.get() {
                        return self.enum_unchanged(&a[0], ctx, k);
                    }
                }
                K::BoxAct => {
                    if !self.init_mode.get() {
                        self.enumerate(&a[0], ctx, k)?;
                        return self.enum_unchanged(&a[1], ctx, k);
                    }
                }
                K::AngleAct => {
                    if !self.init_mode.get() {
                        return self.enumerate(&a[0], ctx, &mut || {
                            if !self.unchanged_val(&a[1], ctx)? {
                                return k();
                            }
                            Ok(())
                        });
                    }
                }
                _ => {}
            },
            E::Quant { forall, bounds, body } => {
                let body: N = body;
                if !*forall {
                    self.for_bindings(bounds, ctx, &mut |c| {
                        self.enumerate(body, c, k)?;
                        Ok(false)
                    })?;
                    return Ok(());
                }
                // \A is a conjunction over all bindings
                let mut ctxs: Vec<C> = vec![];
                self.for_bindings(bounds, ctx, &mut |c| {
                    ctxs.push(c.clone());
                    Ok(false)
                })?;
                fn go(ev: &Evaluator, body: N, ctxs: &[C], i: usize, k: &mut dyn FnMut() -> R<()>) -> R<()> {
                    if i == ctxs.len() {
                        return k();
                    }
                    ev.enumerate(body, &ctxs[i], &mut || go(ev, body, ctxs, i + 1, &mut *k))
                }
                return go(self, body, &ctxs, 0, k);
            }
            E::Case { arms, other } => {
                for (c, x) in arms {
                    if self.eval_bool(c, ctx)? {
                        return self.enumerate(x, ctx, k);
                    }
                }
                if let Some(o) = other {
                    return self.enumerate(o, ctx, k);
                }
                return self.fail("Attempted to evaluate a CASE expression in which none of the conditions were true.".into(), e);
            }
            E::Let { defs, body } => return self.enumerate(body, &self.bind_let(defs, ctx), k),
            E::App { .. } => {
                if let Some((b, c)) = self.expand_app(e, ctx)? {
                    return self.enumerate(b, &c, k);
                }
            }
            E::FnApp { f, args } => {
                // TLC enters the body of a lazily evaluated (recursive) function
                let fv = self.eval_fn_operand(f, ctx)?;
                if let Value::LazyFcn(lf) = &fv {
                    let arg = if args.len() == 1 {
                        self.eval(&args[0], ctx)?
                    } else {
                        let mut t = Vec::with_capacity(args.len());
                        for x in args {
                            t.push(self.eval(x, ctx)?);
                        }
                        Value::Tuple(TupleV::rc(t))
                    };
                    let c = lf.bind(self, &arg)?;
                    return self.enumerate(lf.body(), &c, k);
                }
            }
            _ => {}
        }
        if self.eval_bool(e, ctx)? {
            return k();
        }
        Ok(())
    }

    pub(crate) fn enum_conj(&self, items: &'static [Node], i: usize, ctx: &C, k: &mut dyn FnMut() -> R<()>) -> R<()> {
        if i == items.len() {
            return k();
        }
        if i == items.len() - 1 {
            return self.enumerate(&items[i], ctx, k);
        }
        self.enumerate(&items[i], ctx, &mut || self.enum_conj(items, i + 1, ctx, &mut *k))
    }

    fn enum_unchanged(&self, e: N, ctx: &C, k: &mut dyn FnMut() -> R<()>) -> R<()> {
        if let E::Op(K::Tuple, items) = &e.e {
            // The usual shape, a tuple of variables: one pass instead of a continuation per variable.
            let mut idxs = [0u32; 32];
            let mut plain = items.len() <= 32;
            if plain {
                for (j, it) in items.iter().enumerate() {
                    match plain_var(it, ctx) {
                        Some(i) => idxs[j] = i as u32,
                        None => {
                            plain = false;
                            break;
                        }
                    }
                }
            }
            if plain {
                let nxt = self.nxt.borrow().as_ref().unwrap().clone();
                let cur = self.cur.borrow().clone();
                let ids = &idxs[..items.len()];
                // Nearly always: distinct variables, none assigned yet, all defined. Copy them over in one go.
                let mut seen: u64 = 0;
                let distinct = ids.iter().all(|&i| {
                    let fresh = i < 64 && seen & (1 << i) == 0;
                    seen |= 1 << (i & 63);
                    fresh
                });
                if distinct && !Rc::ptr_eq(&nxt, &cur) && nxt.can_fill(&cur, ids) {
                    nxt.fill(&cur, ids);
                    drop(cur);
                    self.st_touch.set(self.st_touch.get() + ids.len() as u64);
                    self.n_assigned.set(self.n_assigned.get() + ids.len() as i64);
                    let r = k();
                    for &i in ids.iter().rev() {
                        nxt.clear(i as usize);
                    }
                    self.n_assigned.set(self.n_assigned.get() - ids.len() as i64);
                    return r;
                }
                let mut set: u32 = 0; // the items assigned here
                let mut r: R<()> = Ok(());
                let mut go_on = true;
                for (j, it) in items.iter().enumerate() {
                    let idx = idxs[j] as usize;
                    if nxt.is_undef(idx) {
                        let v = cur.get(idx);
                        self.st_touch.set(self.st_touch.get() + 1);
                        if matches!(v, Value::Undef) {
                            r = self.at_node(undefined_ident(self.var_names.borrow().get(idx).copied().unwrap_or(self.at)), it);
                            go_on = false;
                            break;
                        }
                        nxt.set(idx, v);
                        self.n_assigned.set(self.n_assigned.get() + 1);
                        set |= 1 << j;
                    } else {
                        if self.steps.on.get() {
                            self.steps.var(idx, &cur.get(idx), false);
                        }
                        match val_eq(&nxt.get(idx), &cur.get(idx)) {
                            Ok(true) => {}
                            Ok(false) => {
                                go_on = false;
                                break;
                            }
                            Err(e) => {
                                r = Err(e);
                                go_on = false;
                                break;
                            }
                        }
                    }
                }
                drop(cur);
                if go_on {
                    r = k();
                }
                for j in (0..items.len()).rev() {
                    if set & (1 << j) != 0 {
                        nxt.clear(idxs[j] as usize);
                    }
                }
                self.n_assigned.set(self.n_assigned.get() - set.count_ones() as i64);
                return r;
            }
            fn go(ev: &Evaluator, items: &'static [Node], i: usize, ctx: &C, k: &mut dyn FnMut() -> R<()>) -> R<()> {
                if i == items.len() {
                    return k();
                }
                ev.enum_unchanged(&items[i], ctx, &mut || go(ev, items, i + 1, ctx, &mut *k))
            }
            return go(self, items, 0, ctx, k);
        }
        if let E::App { args, sel: None, r, .. } = &e.e {
            // a name for a tuple of variables (UNCHANGED vars): straight to the tuple
            if let (Res::Def(d), true) = (r.get(), args.is_empty()) {
                let d = d.over.get().unwrap_or(d);
                if d.builtin.get().is_none() && d.inst.is_none() && d.params.is_empty() {
                    if let Some(body) = d.body.get() {
                        if matches!(body.e, E::Op(K::Tuple, _)) {
                            return self.enum_unchanged(body, &base_of(ctx), k);
                        }
                    }
                }
            }
        }
        if let E::App { .. } = &e.e {
            let idx = self.as_var(e, ctx)?;
            if idx >= 0 {
                let idx = idx as usize;
                let nxt = self.nxt.borrow().as_ref().unwrap().clone();
                let nv = self.nvars.get();
                if nxt.is_undef(idx) {
                    let v = if idx >= nv { self.eval(e, ctx)? } else { self.cur.borrow().get(idx) };
                    self.st_touch.set(self.st_touch.get() + 1);
                    if matches!(v, Value::Undef) {
                        return self.at_node(undefined_ident(self.var_names.borrow().get(idx).copied().unwrap_or(self.at)), e);
                    }
                    nxt.set(idx, v);
                    self.n_assigned.set(self.n_assigned.get() + 1);
                    let r = k();
                    nxt.set(idx, Value::Undef);
                    self.n_assigned.set(self.n_assigned.get() - 1);
                    return r;
                }
                let old = if idx >= nv { self.eval(e, ctx)? } else { self.cur.borrow().get(idx) };
                if self.steps.on.get() {
                    self.steps.var(idx, &old, false);
                }
                if val_eq(&nxt.get(idx), &old)? {
                    return k();
                }
                return Ok(());
            }
            if let Some((b, c)) = self.expand_app(e, ctx)? {
                return self.enum_unchanged(b, &c, k);
            }
        }
        if self.unchanged_val(e, ctx)? {
            return k();
        }
        Ok(())
    }

    pub fn random(&self) -> f64 {
        // xorshift64*; only used by RandomElement and the Randomization module
        worker_impure("a random choice (RandomElement or the Randomization module)");
        let mut x = self.rng.get();
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.rng.set(x);
        (x.wrapping_mul(0x2545F4914F6CDD1D) >> 11) as f64 / (1u64 << 53) as f64
    }
}
