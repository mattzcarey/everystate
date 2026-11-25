//! A compiled form of actions and invariants (the default; EVERYSTATE_EVAL=tree turns it off); the tree-walker of eval.rs stays
//! the reference.
//!
//! Before the search each top-level action and each invariant is turned into a tree of closures:
//! identifiers are resolved to what they denote (a state variable's index, a slot of a frame, a constant),
//! applications of definitions with value parameters are inlined, and the enumerator's work (which
//! conjunct assigns which primed variable, which leave variables unchanged, where the branches are) is
//! decided once instead of being rediscovered for every state. Nothing is memoised across states; the
//! invariants of one state share a memo of the definitions they have in common (`InvMemo`).
//!
//! The rules that keep it equal to the tree-walker:
//! * Whatever the compiler does not handle is compiled to a *fallback*: the expression is evaluated by the
//!   tree-walker in a context rebuilt from the frame. Coverage is a matter of speed only.
//! * A parameter of an inlined definition is bound by name: every use evaluates the argument where it is
//!   used (so an unused argument is never evaluated, as with the tree-walker's thunks); the value is kept
//!   for the rest of the call when the argument is a state-level expression.
//! * The compiled code only has to be right when it succeeds. If it fails in any way, what it produced
//!   for the action (or invariant) is discarded and the tree-walker evaluates it again from the start, so
//!   error messages, locations and precedence are the tree-walker's by construction. For that to be
//!   sound, an action that may reach an operator with an effect (printing, TLCSet, random choice, I/O, a
//!   new string) is not compiled at all.
use crate::ast::*;
use crate::eval::*;
use crate::intern::*;
use crate::modules::{for_children, level_of, tail_fn, BFn, Builtin, Def};
use crate::stepcache::{self as sc_, DOp, Entry, Leaf, Loc, Table, Tmpl, Write};
use crate::value::*;
use std::cell::{Cell, OnceCell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub struct Cx<'a> {
    pub ev: &'a Evaluator,
    /// the frame: bound variables, values of by-name parameters and LET definitions, `@`
    pub f: &'a StateData,
    pub cur: &'a StateData,
    /// the next state being assigned (the blank state for an invariant)
    pub nxt: &'a StateData,
    pub nv: i64,
    pub fallbacks: &'a Cell<u64>,
    /// the step cache (stepcache.rs), when it is on; `rec_on` while a unit's evaluation is being recorded
    pub cache: Option<&'a RefCell<Table>>,
    pub rec_on: &'a Cell<bool>,
    pub rec: &'a RefCell<Rec>,
    pub cache_always: bool,
    pub meas: &'a Meas,
}
/// What the evaluation of a unit read and did, noted for the step cache.
#[derive(Default)]
pub struct Rec {
    reads: Vec<(Loc, Value)>,
    /// something happened that an entry cannot describe
    bad: bool,
    /// per variable: the changes that turn the parent's value into the value now assigned (None: the value
    /// was computed some other way)
    delta: Vec<Option<Vec<DOp>>>,
    succs: Vec<Vec<Write>>,
}
/// A program that, for an expression known to compute a change of one variable's value, produces the
/// changes instead of the value (false: not expressible this time).
type DProg = dyn Fn(&Cx, &mut Vec<DOp>) -> R<bool>;
#[derive(Clone)]
struct DShape {
    var: usize,
    /// the expression is the variable itself
    direct: bool,
    prog: Rc<DProg>,
}
/// The parent's value of a variable after the changes; None when one of them cannot be applied.
fn apply_ops(cx: &Cx, parent: &Value, ops: &[DOp], n: N) -> Option<Value> {
    let mut v = parent.clone();
    for op in ops {
        v = match op {
            DOp::Bag { e, plus } => crate::stdlib::bag_one(&v, e, *plus)?,
            DOp::Set { e, add } => match &v {
                Value::Set(s) => set_one(s, e, *add)?,
                _ => return None,
            },
            DOp::Exc { path, v: nv } => {
                let mut hit = false;
                let r = cx
                    .ev
                    .except_with(
                        v,
                        path,
                        0,
                        &mut |_| {
                            hit = true;
                            Ok(nv.clone())
                        },
                        n,
                    )
                    .ok()?;
                if !hit {
                    return None;
                }
                r
            }
        };
    }
    Some(v)
}
fn uses_at(n: N) -> bool {
    if matches!(n.e, E::At) {
        return true;
    }
    let mut r = false;
    for_children(n, &mut |c| {
        if !r && uses_at(c) {
            r = true;
        }
    });
    r
}
type CE = Box<dyn Fn(&Cx) -> R<Value>>;
type AE = Box<dyn Fn(&Cx, &mut dyn FnMut() -> R<()>) -> R<()>>;

#[cold]
fn bail<T>() -> R<T> {
    // any failure: the caller discards the compiled attempt and asks the tree-walker
    eval_err(String::new())
}

// ---------- scopes: what the tree-walker's context would be ----------
struct Sc {
    k: ScK,
    next: Option<Rc<Sc>>,
}
enum ScK {
    /// the bottom: the context the tree-walker starts from (an action's own context, or none)
    Root(C),
    Slot { name: Name, slot: usize },
    At { slot: usize },
    /// a value parameter of an inlined definition, bound to an argument of the call
    Arg { name: Name, node: N, sc: Rc<Sc>, bd: ArgBd },
    /// one definition of a LET group; `below` is the scope under the whole group
    /// (`root`: the definition is part of the context the action starts from, see `root_scope`)
    Let { d: &'static DefNode, defs: &'static [LetDef], below: Rc<Sc>, head: bool, cache: usize, ce: RefCell<Option<(Rc<CE>, bool)>>, root: bool },
    /// a value bound in the context the action starts from
    RootVal { name: Name, v: Value },
}
enum ArgBd {
    Const(Value),
    /// `stable`: the value cannot change while the binding lives (no dependence on the next state)
    ByName { ce: Rc<CE>, cache: Option<usize>, stable: bool },
}

/// The tree-walker's context for a scope, from the current frame.
/// `share`: values the compiled code has already computed for parameters and LET definitions are passed
/// instead of thunks. Only for an expression that cannot prime, assign or test ENABLED: there a parameter
/// is used for the expression it stands for (`q' = ...` with `q` bound to a variable), not for its value.
fn build(sc: &Rc<Sc>, cx: &Cx, share: bool) -> R<C> {
    let below = |cx: &Cx| -> R<C> {
        match &sc.next {
            Some(n) => build(n, cx, share),
            None => Ok(None),
        }
    };
    Ok(match &sc.k {
        ScK::Root(c) => c.clone(),
        ScK::Slot { name, slot } => cons(*name, cx.f.get(*slot), &below(cx)?),
        ScK::At { slot } => cons(cx.ev.at, cx.f.get(*slot), &below(cx)?),
        ScK::Arg { name, node, sc: asc, bd } => {
            // a value the compiled code already has is passed on instead of a thunk that would compute it again
            let known = match bd {
                ArgBd::Const(v) => Some(v.clone()),
                ArgBd::ByName { cache: Some(slot), .. } if share => Some(cx.f.get(*slot)).filter(|v| !matches!(v, Value::Undef)),
                _ => None,
            };
            let v = match known {
                Some(v) => v,
                None => cx.ev.mk_arg(node, &build(asc, cx, share)?)?,
            };
            cons(*name, v, &below(cx)?)
        }
        ScK::Let { root: true, .. } | ScK::RootVal { .. } => below(cx)?,
        ScK::Let { defs, below: b, head, .. } => {
            debug_assert!(*head);
            let ctx = cx.ev.bind_let(defs, &build(b, cx, share)?);
            // likewise for the LET definitions already evaluated: their cells start out filled
            let mut s = if share { Some(sc) } else { None };
            while let Some(node) = s {
                match &node.k {
                    ScK::Let { d, cache, root: false, below: b2, .. } if Rc::ptr_eq(b2, b) => {
                        let v = cx.f.get(*cache);
                        if !matches!(v, Value::Undef) {
                            let mut c = ctx.as_ref();
                            while let Some(cn) = c {
                                if cn.name == d.name {
                                    if let Bind::LetLazy { v: cell, st, .. } = &cn.val {
                                        *cell.borrow_mut() = v;
                                        st.set(cx.cur.id);
                                    }
                                    break;
                                }
                                c = cn.next.as_ref();
                            }
                        }
                    }
                    _ => break,
                }
                s = node.next.as_ref();
            }
            ctx
        }
    })
}

/// EVERYSTATE_EVAL_DEBUG: each fallback site reports itself the first time it runs.
fn debug_fb(seen: &Cell<bool>, what: &str, node: N) {
    if !seen.replace(true) && std::env::var_os("EVERYSTATE_EVAL_DEBUG").is_some() {
        eprintln!("fallback {} at line {} col {} to line {} col {}", what, node.loc[0], node.loc[1], node.loc[2], node.loc[3]);
    }
}
/// Nothing reachable from `n` primes, assigns, or asks what is enabled.
fn primeless(n: N, seen: &mut HashSet<usize>) -> bool {
    match &n.e {
        E::Op(K::Prime | K::Enabled | K::Unchanged | K::Cdot | K::BoxAct | K::AngleAct | K::Always | K::Eventually | K::LeadsTo | K::Wf | K::Sf | K::Guarantee, _) => return false,
        E::TQuant { .. } | E::StepRef | E::AssumeProve => return false,
        E::App { r, sel, .. } => {
            if sel.is_some() {
                return false;
            }
            let d = match r.get() {
                Res::Def(d) => Some(d),
                Res::Decl(d) => d.subst.get(),
                Res::Local => None,
                Res::None => return false,
            };
            if let Some(d) = d {
                let d = d.over.get().unwrap_or(d);
                if seen.insert(d as *const Def as usize) {
                    if let Some(inst) = &d.inst {
                        let _ = inst;
                        return false;
                    }
                    if d.builtin.get().is_none() {
                        match d.body.get() {
                            Some(b) => {
                                if !primeless(b, seen) {
                                    return false;
                                }
                            }
                            None => return false,
                        }
                    }
                }
            }
        }
        E::Let { defs, .. } => {
            if defs.iter().any(|d| matches!(d, LetDef::Inst(_))) {
                return false;
            }
        }
        _ => {}
    }
    let mut ok = true;
    for_children(n, &mut |c| {
        if ok && !primeless(c, seen) {
            ok = false;
        }
    });
    ok
}
fn fb(node: N, sc: &Rc<Sc>) -> CE {
    let sc = sc.clone();
    let seen = Cell::new(false);
    let share = primeless(node, &mut HashSet::new());
    Box::new(move |cx| {
        debug_fb(&seen, "expression", node);
        cx.fallbacks.set(cx.fallbacks.get() + 1);
        let ctx = build(&sc, cx, share)?;
        cx.ev.eval(node, &ctx)
    })
}
fn fb_act(node: N, sc: &Rc<Sc>) -> AE {
    let sc = sc.clone();
    let seen = Cell::new(false);
    Box::new(move |cx, k| {
        debug_fb(&seen, "action", node);
        cx.fallbacks.set(cx.fallbacks.get() + 1);
        let ctx = build(&sc, cx, false)?;
        cx.ev.enumerate(node, &ctx, k)
    })
}

#[inline]
fn truth(v: Value) -> R<bool> {
    match &v {
        Value::Bool(b) => {
            let b = *b;
            std::mem::forget(v); // nothing to drop: spares the call of the drop glue
            Ok(b)
        }
        _ => bail(),
    }
}
#[inline]
fn as_set(v: Value) -> R<Rc<SetV>> {
    match v {
        Value::Set(s) => Ok(s),
        _ => bail(),
    }
}
fn plain(v: &Value) -> bool {
    match v {
        Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) | Value::Tuple(_) | Value::Record(_) | Value::Fcn(_) => true,
        Value::Set(s) => s.reducible(),
        _ => false,
    }
}

/// Builtin operators of these modules have no effect and read nothing but their arguments.
fn pure_module(m: Name) -> bool {
    thread_local! {
        static PURE: Vec<Name> = ["Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "Bags"].iter().map(|s| name(s)).collect();
    }
    PURE.with(|p| p.contains(&m))
}
fn pure_builtin(d: &'static Def) -> bool {
    if pure_module(d.module) {
        return true;
    }
    let n = name_str(d.name);
    name_str(d.module).as_ref() == "TLC" && matches!(n.as_ref(), ":>" | "@@")
}

/// May evaluating `n` reach an operator with an effect? (Conservative: anything not understood counts.)
fn impure(n: N, seen: &mut HashSet<usize>) -> bool {
    let r = impure0(n, seen);
    if r && std::env::var_os("EVERYSTATE_EVAL_DEBUG").is_some() {
        if let E::App { name, r, sel, .. } = &n.e {
            eprintln!("  (may have an effect, or is not understood: {}{}{} at line {})", name, if sel.is_some() { " with a selector" } else { "" }, match r.get() { Res::Def(d) => format!(" of module {}{}", d.module, if d.inst.is_some() { " (instance)" } else { "" }), Res::Decl(_) => " (substituted declaration)".into(), _ => String::new() }, n.loc[0]);
        }
    }
    r
}
fn impure_def(d: &'static Def, seen: &mut HashSet<usize>) -> bool {
    let d = d.over.get().unwrap_or(d);
    if !seen.insert(d as *const Def as usize) {
        return false;
    }
    if let Some(bi) = d.builtin.get() {
        // a value given by the configuration is as pure as an operator of the standard modules
        return !(pure_builtin(d) || matches!(bi.f, BFn::Const(_) | BFn::Table(..)));
    }
    if let Some(inst) = &d.inst {
        // a definition of an instantiated module: the original and what is substituted into it
        return impure_def(inst.orig, seen) || inst.substs.iter().any(|s| impure(s.e, seen));
    }
    match d.body.get() {
        Some(b) => impure(b, seen),
        None => true,
    }
}
fn impure0(n: N, seen: &mut HashSet<usize>) -> bool {
    if let E::App { r, sel, .. } = &n.e {
        if sel.is_some() {
            return true;
        }
        match r.get() {
            Res::Def(d) => {
                if impure_def(d, seen) {
                    return true;
                }
            }
            Res::Decl(d) => {
                // a constant the configuration replaces by a definition
                if let Some(sd) = d.subst.get() {
                    if impure_def(sd, seen) {
                        return true;
                    }
                }
            }
            Res::Local => {}
            Res::None => return true,
        }
    }
    if matches!(n.e, E::Let { .. }) {
        if let E::Let { defs, .. } = &n.e {
            if defs.iter().any(|d| matches!(d, LetDef::Inst(_))) {
                return true;
            }
        }
    }
    let mut bad = false;
    for_children(n, &mut |c| {
        if !bad && impure(c, seen) {
            bad = true;
        }
    });
    bad
}

// ---------- the compiler ----------
struct Comp {
    nslots: usize,
    /// the memo the invariants of one state share (`InvMemo`); None while an action is compiled
    inv_memo: Option<Rc<InvMemo>>,
    /// definitions and LET definitions being inlined (recursion guard)
    stack: Vec<usize>,
    budget: i64,
    /// set while compiling an expression whose value may depend on the next state
    unstable: bool,
    /// what the expression just compiled is known to build (see `One`); `shape_ok` is set by the cases
    /// of `expr0` that leave a shape for their caller
    shape: Option<One>,
    shape_ok: bool,
    /// likewise, the expression just compiled computes a change of a variable's value
    dshape: Option<DShape>,
    dshape_ok: bool,
    /// the step cache is on: units are marked out (`top`: still above the units; `descend`: the node being
    /// compiled passes `top` on to its parts)
    cache: bool,
    top: bool,
    descend: bool,
    /// every slot that keeps the value of a by-name binding
    cache_slots: Vec<usize>,
    /// the slots of the variables bound by the existential quantifiers above the units
    top_slots: Vec<usize>,
    units: u32,
    unit_stats: Vec<Rc<UnitStat>>,
    plan_id: u32,
}
pub struct UnitStat {
    loc: Loc4,
    lookups: Cell<u64>,
    hits: Cell<u64>,
    /// the last measurement said the cache does not pay for this unit
    off: Cell<bool>,
    skip: Cell<u64>,
    penalty: Cell<u64>,
    phase: Cell<u8>,
    /// evaluations in the current phase
    count: Cell<u64>,
    /// on trial: the time per state expanded without (0) and with (1) the cache
    acc: [Acc; 2],
    /// on trial: the last expansion this unit was evaluated in, and whether it uses the cache in it
    seen: Cell<u64>,
    arm: Cell<bool>,
    /// the means at the last verdict, and the number of states it was based on
    last: Cell<(f64, f64)>,
    trials: Cell<u64>,
    /// evaluations before the next trial (16 times the length of the last one, at least 262144)
    again: Cell<u64>,
    /// on trial: the unit had the cache before
    held: Cell<bool>,
    /// hits and lookups when the warm-up or the current window began
    mark: Cell<u64>,
    mark_l: Cell<u64>,
    /// evaluations whose result was stored, and that count when the warm-up began
    stored: Cell<u64>,
    mark_s: Cell<u64>,
}
type Loc4 = [u32; 4];

/// The expression just compiled is `{e}` or `SetToBag({e})`, possibly behind inlined definitions:
/// `elem` computes `e` after the slots in `clear` are reset. Consumers (`S \cup {e}`, `S \ {e}`,
/// `B (+) SetToBag({e})`, `B (-) SetToBag({e})`) then update the set or bag directly instead of building
/// the one-element value first.
#[derive(Clone)]
struct One {
    bag: bool,
    elem: Rc<CE>,
    clear: Vec<PreOp>,
}
/// What happens when an inlined call (or a LET) is entered, before its body.
#[derive(Clone, Copy)]
enum PreOp {
    /// forget the value kept for a by-name binding
    Clear(usize),
    /// a string literal passed as an argument: the tree-walker evaluates it when it binds the parameter,
    /// which is when the string gets its number if it is new
    Intern(N),
}
#[inline]
fn run_pre(pre: &[PreOp], cx: &Cx) {
    for op in pre {
        match op {
            PreOp::Clear(s) => cx.f.clear(*s),
            PreOp::Intern(n) => {
                if let E::Str(s, id) = &n.e {
                    cx.ev.str_node(s, id);
                }
            }
        }
    }
}
impl One {
    #[inline]
    fn eval(&self, cx: &Cx) -> R<Value> {
        run_pre(&self.clear, cx);
        (self.elem)(cx)
    }
}

/// Position of `e` in the sorted `es`: (index, found). None when a comparison fails.
fn locate(es: &[Value], e: &Value) -> Option<(usize, bool)> {
    let (mut lo, mut hi) = (0, es.len());
    while lo < hi {
        let mid = (lo + hi) / 2;
        let c = match scalar_cmp(&es[mid], e) {
            Some(c) => c,
            None => compare(&es[mid], e).ok()?,
        };
        match c {
            std::cmp::Ordering::Less => lo = mid + 1,
            std::cmp::Ordering::Greater => hi = mid,
            std::cmp::Ordering::Equal => return Some((mid, true)),
        }
    }
    Some((lo, false))
}
/// `s \cup {e}` (add) or `s \ {e}` for an explicit set; None for the general code to decide.
fn set_one(s: &Rc<SetV>, e: &Value, add: bool) -> Option<Value> {
    let es = match &s.k {
        SetK::Enum(es) => es,
        _ => return None,
    };
    let (i, found) = locate(es, e)?;
    if found == add {
        return Some(Value::Set(s.clone()));
    }
    let mut out = Vec::with_capacity(if add { es.len() + 1 } else { es.len() - 1 });
    out.extend_from_slice(&es[..i]);
    if add {
        out.push(e.clone());
        out.extend_from_slice(&es[i..]);
    } else {
        out.extend_from_slice(&es[i + 1..]);
    }
    Some(SetV::of(out))
}

enum Found {
    Slot(usize),
    Const(Value),
    ByName(Rc<CE>, Option<usize>),
    /// a LET definition: its scope node and the head of its group
    Let(Rc<Sc>, Rc<Sc>),
    Arg(Rc<Sc>),
    No,
}

fn lookup(sc: &Rc<Sc>, nm: Name) -> Found {
    let mut cur = Some(sc);
    let mut head: Option<&Rc<Sc>> = None;
    while let Some(s) = cur {
        match &s.k {
            ScK::Slot { name, slot } if *name == nm => return Found::Slot(*slot),
            ScK::Arg { name, .. } if *name == nm => return Found::Arg(s.clone()),
            ScK::Let { d, head: h, .. } => {
                if *h {
                    head = Some(s);
                }
                if d.name == nm {
                    return match head {
                        Some(h) => Found::Let(s.clone(), h.clone()),
                        None => Found::No,
                    };
                }
            }
            ScK::RootVal { name, v } if *name == nm => return Found::Const(v.clone()),
            ScK::Root(_) => return Found::No,
            _ => {}
        }
        cur = s.next.as_ref();
    }
    Found::No
}
fn lookup_at(sc: &Rc<Sc>) -> Option<usize> {
    let mut cur = Some(sc);
    while let Some(s) = cur {
        if let ScK::At { slot } = &s.k {
            return Some(*slot);
        }
        cur = s.next.as_ref();
    }
    None
}
fn push(sc: &Rc<Sc>, k: ScK) -> Rc<Sc> {
    Rc::new(Sc { k, next: Some(sc.clone()) })
}
/// Several bounds, several names per bound, tuple patterns: `\E x, y \in S, <<a, b>> \in T : ...`.
struct Bnds {
    sets: Vec<CE>,
    /// one entry per bound name or tuple pattern, in the order written
    flat: Vec<FlatB>,
}
struct FlatB {
    set: usize,
    slots: Vec<usize>,
    tuple: bool,
}
impl Bnds {
    /// Calls `f` for every binding, in the tree-walker's order (the first name varies fastest), until it
    /// returns true; all the sets are evaluated and enumerated before the first binding.
    fn each(&self, cx: &Cx, f: &mut dyn FnMut() -> R<bool>) -> R<bool> {
        let mut sets: Vec<Rc<SetV>> = Vec::with_capacity(self.sets.len());
        for s in &self.sets {
            let s = as_set(s(cx)?)?;
            s.elems()?;
            sets.push(s);
        }
        fn rec(b: &Bnds, sets: &[Rc<SetV>], i: isize, cx: &Cx, f: &mut dyn FnMut() -> R<bool>) -> R<bool> {
            if i < 0 {
                return f();
            }
            let fb = &b.flat[i as usize];
            for v in sets[fb.set].elems()? {
                if fb.tuple {
                    match v {
                        Value::Tuple(t) if t.len() == fb.slots.len() => {
                            for (j, &s) in fb.slots.iter().enumerate() {
                                cx.f.set(s, t[j].clone());
                            }
                        }
                        _ => return bail(),
                    }
                } else {
                    cx.f.set(fb.slots[0], v.clone());
                }
                if rec(b, sets, i - 1, cx, f)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        rec(self, &sets, self.flat.len() as isize - 1, cx, f)
    }
}
fn simple_bound(bounds: &'static [Bound]) -> Option<(Name, N)> {
    if bounds.len() != 1 {
        return None;
    }
    one_bound(&bounds[0])
}
fn one_bound(b: &'static Bound) -> Option<(Name, N)> {
    match (&b.names, &b.tuple, &b.set) {
        (Some(ns), None, Some(set)) if ns.len() == 1 => Some((ns[0], set)),
        _ => None,
    }
}
fn var_of(n: N) -> Option<usize> {
    if let E::App { args, sel: None, r, .. } = &n.e {
        if let Res::Decl(d) = r.get() {
            if d.is_var && d.idx.get() >= 0 && args.is_empty() {
                return Some(d.idx.get() as usize);
            }
        }
    }
    None
}

impl Comp {
    fn new(cache: bool, plan_id: u32) -> Comp {
        Comp { nslots: 0, inv_memo: None, stack: vec![], budget: 20_000, unstable: false, shape: None, shape_ok: false, dshape: None, dshape_ok: false, cache, top: false, descend: false, cache_slots: vec![], top_slots: vec![], units: 0, unit_stats: vec![], plan_id }
    }
    /// The compiled bounds of a quantifier and the scope of its body. None when a bound has no set.
    fn bounds(&mut self, bounds: &'static [Bound], sc: &Rc<Sc>) -> Option<(Bnds, Rc<Sc>)> {
        if bounds.iter().any(|b| b.set.is_none() || (b.names.is_none() && b.tuple.is_none())) {
            return None;
        }
        let mut sets = vec![];
        let mut flat: Vec<(FlatB, Vec<Name>)> = vec![];
        for (i, b) in bounds.iter().enumerate() {
            sets.push(self.expr(b.set.as_ref().unwrap(), sc));
            if let Some(t) = &b.tuple {
                let slots = t.iter().map(|_| self.slot()).collect();
                flat.push((FlatB { set: i, slots, tuple: true }, t.clone()));
            } else {
                for nm in b.names.as_ref().unwrap() {
                    let s = self.slot();
                    flat.push((FlatB { set: i, slots: vec![s], tuple: false }, vec![*nm]));
                }
            }
        }
        // the last name is the outermost loop, so it is bound first
        let mut inner = sc.clone();
        for (fb, names) in flat.iter().rev() {
            for (j, nm) in names.iter().enumerate() {
                inner = push(&inner, ScK::Slot { name: *nm, slot: fb.slots[j] });
            }
        }
        Some((Bnds { sets, flat: flat.into_iter().map(|x| x.0).collect() }, inner))
    }
    fn slot(&mut self) -> usize {
        self.nslots += 1;
        self.nslots - 1
    }
    fn fallback(&mut self, n: N, sc: &Rc<Sc>) -> CE {
        if level_of(n) >= 2 {
            self.unstable = true;
        }
        fb(n, sc)
    }

    /// The scope and prologue for inlining a definition: its parameters bound by name to the arguments.
    /// `base` is the scope the body sees under its parameters. None when the call cannot be inlined.
    fn bind_args(&mut self, params: &'static [Param], args: &'static [Node], base: Rc<Sc>, sc: &Rc<Sc>) -> Option<(Rc<Sc>, Vec<PreOp>)> {
        if params.len() != args.len() || params.iter().any(|p| p.arity != 0) {
            return None;
        }
        let mut inner = base;
        let mut clear = vec![];
        for (p, a) in params.iter().zip(args.iter()) {
            if matches!(a.e, E::Lambda { .. }) {
                return None;
            }
            let bd = match &a.e {
                E::Num(v) => ArgBd::Const(Value::Int(*v)),
                E::Bool(b) => ArgBd::Const(Value::Bool(*b)),
                _ => {
                    let was = std::mem::replace(&mut self.unstable, false);
                    let ce = self.expr(a, sc);
                    let stable = !self.unstable;
                    self.unstable |= was;
                    // a value that cannot change during the call is kept in a slot after its first use
                    // (not worth it for a string or a name that is itself a slot or a constant)
                    let trivial = matches!(a.e, E::Str(..))
                        || matches!(&a.e, E::App { name, args, sel: None, r, .. } if args.is_empty() && matches!(r.get(), Res::Local) && matches!(lookup(sc, *name), Found::Slot(_) | Found::Const(_)));
                    if matches!(a.e, E::Str(..)) {
                        clear.push(PreOp::Intern(a));
                    }
                    let cache = if stable && !trivial {
                        let s = self.slot();
                        self.cache_slots.push(s);
                        clear.push(PreOp::Clear(s));
                        Some(s)
                    } else {
                        None
                    };
                    ArgBd::ByName { ce: Rc::new(ce), cache, stable }
                }
            };
            inner = push(&inner, ScK::Arg { name: p.name, node: a, sc: sc.clone(), bd });
        }
        Some((inner, clear))
    }

    /// What a use of a by-name binding evaluates.
    fn by_name(ce: Rc<CE>, cache: Option<usize>) -> CE {
        match cache {
            None => Box::new(move |cx| ce(cx)),
            Some(slot) => Box::new(move |cx| {
                let v = cx.f.get(slot);
                if !matches!(v, Value::Undef) {
                    return Ok(v);
                }
                let v = ce(cx)?;
                cx.f.set(slot, v.clone());
                Ok(v)
            }),
        }
    }

    /// The compiled body of a LET definition without parameters (compiled once, on first use).
    fn let_value(&mut self, def_sc: &Rc<Sc>, head: &Rc<Sc>) -> Option<CE> {
        if let ScK::Let { d, cache, ce, .. } = &def_sc.k {
            if !d.params.is_empty() {
                return None;
            }
            if ce.borrow().is_none() {
                let id = *d as *const DefNode as usize;
                if self.stack.contains(&id) {
                    return None;
                }
                self.stack.push(id);
                let was = std::mem::replace(&mut self.unstable, false);
                let body = self.expr(&d.body, head);
                let stable = !self.unstable;
                self.unstable |= was;
                self.stack.pop();
                *ce.borrow_mut() = Some((Rc::new(body), stable));
            }
            let (c, stable) = ce.borrow().as_ref().unwrap().clone();
            if !stable {
                self.unstable = true;
            }
            return Some(Comp::by_name(c, if stable { Some(*cache) } else { None }));
        }
        None
    }

    /// The scope of a LET body: one node per definition, as the tree-walker's `bind_let`.
    fn let_scope(&mut self, defs: &'static [LetDef], sc: &Rc<Sc>) -> Option<(Rc<Sc>, Vec<PreOp>)> {
        let mut inner = sc.clone();
        let mut clear = vec![];
        let n = defs.len();
        for (i, d) in defs.iter().enumerate() {
            let d = match d {
                LetDef::Def(d) => d,
                LetDef::Inst(_) => return None,
            };
            let cache = self.slot();
            self.cache_slots.push(cache);
            clear.push(PreOp::Clear(cache));
            inner = push(&inner, ScK::Let { d, defs, below: sc.clone(), head: i + 1 == n, cache, ce: RefCell::new(None), root: false });
        }
        if n == 0 {
            return None;
        }
        Some((inner, clear))
    }

    /// Can the function operand of `f[x]` / `DOMAIN f` be evaluated as an ordinary value? (The tree-walker
    /// keeps a function constructor unevaluated there.)
    fn operand_ok(&self, f: N, sc: &Rc<Sc>) -> bool {
        if tail_fn(f) {
            return false;
        }
        match &f.e {
            E::App { name, args, sel: None, r, .. } if args.is_empty() => match r.get() {
                Res::Local => match lookup(sc, *name) {
                    Found::Slot(_) | Found::Const(_) => true,
                    Found::Arg(a) => match &a.k {
                        ScK::Arg { node, sc: asc, .. } => self.operand_ok(node, asc),
                        _ => false,
                    },
                    // a LET definition that cannot be a function constructor: the tree-walker evaluates it in full
                    Found::Let(d, _) => matches!(&d.k, ScK::Let { d, .. } if d.params.is_empty()),
                    _ => false,
                },
                Res::Decl(d) => d.subst.get().is_none(),
                Res::Def(_) => false,
                Res::None => false,
            },
            E::Dot { .. } | E::FnApp { .. } | E::Except { .. } | E::Rec(..) => true,
            E::Op(K::Tuple, _) => true,
            _ => false,
        }
    }

    fn expr(&mut self, n: N, sc: &Rc<Sc>) -> CE {
        self.shape = None;
        self.shape_ok = false;
        self.dshape = None;
        self.dshape_ok = false;
        let ce = self.expr0(n, sc);
        if !std::mem::replace(&mut self.shape_ok, false) {
            self.shape = None;
        }
        if !std::mem::replace(&mut self.dshape_ok, false) {
            self.dshape = None;
        }
        ce
    }
    /// Passes the shape of an inlined body on to the caller of the inlining: the slots of the call are
    /// reset before the element is computed.
    fn keep_shape(&mut self, clear: &[PreOp]) {
        if let Some(sh) = &mut self.shape {
            sh.clear.extend_from_slice(clear);
            self.shape_ok = true;
        }
        if let Some(d) = self.dshape.take() {
            let pre = clear.to_vec();
            let prog = d.prog.clone();
            self.dshape = Some(DShape {
                var: d.var,
                direct: d.direct && pre.is_empty(),
                prog: Rc::new(move |cx, ops| {
                    run_pre(&pre, cx);
                    prog(cx, ops)
                }),
            });
            self.dshape_ok = true;
        }
    }
    fn expr0(&mut self, n: N, sc: &Rc<Sc>) -> CE {
        self.budget -= 1;
        if self.budget < 0 {
            return self.fallback(n, sc);
        }
        match &n.e {
            E::Num(v) => {
                let v = *v;
                Box::new(move |_| Ok(Value::Int(v)))
            }
            E::Bool(b) => {
                let b = *b;
                Box::new(move |_| Ok(Value::Bool(b)))
            }
            E::Str(s, id) => Box::new(move |cx| Ok(Value::Str(cx.ev.str_node(s, id)))),
            E::At => match lookup_at(sc) {
                Some(slot) => Box::new(move |cx| Ok(cx.f.get(slot))),
                None => self.fallback(n, sc),
            },
            E::App { name, args, sel, r, .. } => {
                if sel.is_some() {
                    return self.fallback(n, sc);
                }
                match r.get() {
                    Res::Local => match lookup(sc, *name) {
                        Found::Slot(slot) if args.is_empty() => Box::new(move |cx| Ok(cx.f.get(slot))),
                        Found::Const(v) if args.is_empty() => Box::new(move |_| Ok(v.clone())),
                        Found::Arg(a) if args.is_empty() => match &a.k {
                            ScK::Arg { bd: ArgBd::Const(v), .. } => {
                                let v = v.clone();
                                Box::new(move |_| Ok(v.clone()))
                            }
                            ScK::Arg { bd: ArgBd::ByName { ce, cache, stable }, .. } => {
                                if !*stable {
                                    self.unstable = true;
                                }
                                Comp::by_name(ce.clone(), *cache)
                            }
                            _ => self.fallback(n, sc),
                        },
                        Found::Let(def_sc, head) => {
                            let d = match &def_sc.k {
                                ScK::Let { d, .. } => *d,
                                _ => unreachable!(),
                            };
                            if d.params.is_empty() {
                                if !args.is_empty() {
                                    return self.fallback(n, sc);
                                }
                                match self.let_value(&def_sc, &head) {
                                    Some(ce) => ce,
                                    None => self.fallback(n, sc),
                                }
                            } else {
                                // a LET operator applied to arguments: its body, inlined
                                let id = d as *const DefNode as usize;
                                if self.stack.contains(&id) || self.stack.len() > 40 {
                                    return self.fallback(n, sc);
                                }
                                match self.bind_args(&d.params, args, head.clone(), sc) {
                                    Some((inner, clear)) => {
                                        self.stack.push(id);
                                        let body = self.expr(&d.body, &inner);
                                        self.stack.pop();
                                        with_clear(clear, body)
                                    }
                                    None => self.fallback(n, sc),
                                }
                            }
                        }
                        _ => self.fallback(n, sc),
                    },
                    Res::Decl(d) => {
                        if !args.is_empty() || d.subst.get().is_some() {
                            return self.fallback(n, sc);
                        }
                        if d.is_var {
                            let idx = d.idx.get();
                            if idx < 0 {
                                return self.fallback(n, sc);
                            }
                            let idx = idx as usize;
                            self.dshape = Some(DShape { var: idx, direct: true, prog: Rc::new(|_, _| Ok(true)) });
                            self.dshape_ok = true;
                            return Box::new(move |cx| {
                                let v = cx.cur.get(idx);
                                if matches!(v, Value::Undef) {
                                    return bail();
                                }
                                if cx.rec_on.get() {
                                    cx.rec.borrow_mut().reads.push((Loc::Whole(idx as u32), v.clone()));
                                }
                                Ok(v)
                            });
                        }
                        let v = d.value.borrow().clone();
                        match v {
                            Some(v) if plain(&v) => Box::new(move |_| Ok(v.clone())),
                            _ => self.fallback(n, sc),
                        }
                    }
                    Res::Def(d) => self.def_app(n, d, args, sc),
                    Res::None => self.fallback(n, sc),
                }
            }
            E::Op(k, a) => self.op(n, *k, a, sc),
            E::Case { arms, other } => {
                let arms: Vec<(CE, CE)> = arms.iter().map(|(c, e)| (self.expr(c, sc), self.expr(e, sc))).collect();
                let other = other.as_ref().map(|o| self.expr(o, sc));
                Box::new(move |cx| {
                    for (c, e) in &arms {
                        if truth(c(cx)?)? {
                            return e(cx);
                        }
                    }
                    match &other {
                        Some(o) => o(cx),
                        None => bail(),
                    }
                })
            }
            E::Let { defs, body } => match self.let_scope(defs, sc) {
                Some((inner, clear)) => {
                    let body = self.expr(body, &inner);
                    with_clear(clear, body)
                }
                None => self.fallback(n, sc),
            },
            E::Quant { forall, bounds, body } => {
                let (nm, set) = match simple_bound(bounds) {
                    Some(x) => x,
                    None => {
                        let (b, inner) = match self.bounds(bounds, sc) {
                            Some(x) => x,
                            None => return self.fallback(n, sc),
                        };
                        let body = self.expr(body, &inner);
                        let forall = *forall;
                        return Box::new(move |cx| {
                            let stopped = b.each(cx, &mut || Ok(truth(body(cx)?)? != forall))?;
                            Ok(Value::Bool(stopped != forall))
                        });
                    }
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let body = self.expr(body, &push(sc, ScK::Slot { name: nm, slot }));
                let forall = *forall;
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    if let SetK::Interval(lo, hi) = &s.k {
                        for i in *lo..=*hi {
                            cx.f.set(slot, Value::Int(i));
                            if truth(body(cx)?)? != forall {
                                return Ok(Value::Bool(!forall));
                            }
                        }
                        return Ok(Value::Bool(forall));
                    }
                    for x in s.elems()? {
                        cx.f.set(slot, x.clone());
                        if truth(body(cx)?)? != forall {
                            return Ok(Value::Bool(!forall));
                        }
                    }
                    Ok(Value::Bool(forall))
                })
            }
            E::Choose { bound, body } => {
                let (nm, set) = match one_bound(bound) {
                    Some(x) => x,
                    None => return self.fallback(n, sc),
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let always = matches!(body.e, E::Bool(true));
                let body = self.expr(body, &push(sc, ScK::Slot { name: nm, slot }));
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    let es = s.elems()?;
                    if always {
                        if let Some(x) = es.first() {
                            return Ok(x.clone());
                        }
                    }
                    for x in es {
                        cx.f.set(slot, x.clone());
                        if truth(body(cx)?)? {
                            return Ok(x.clone());
                        }
                    }
                    bail()
                })
            }
            E::SetFilter { bound, pred } => {
                let (nm, set) = match one_bound(bound) {
                    Some(x) => x,
                    None => return self.fallback(n, sc),
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let pred = self.expr(pred, &push(sc, ScK::Slot { name: nm, slot }));
                // over a set that is not explicit the tree-walker builds a lazy set that keeps its context
                let lazy = self.fallback(n, sc);
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    if !s.reducible() {
                        return lazy(cx);
                    }
                    let mut out = Vec::new();
                    for x in s.elems()? {
                        cx.f.set(slot, x.clone());
                        if truth(pred(cx)?)? {
                            out.push(x.clone());
                        }
                    }
                    Ok(SetV::of(out))
                })
            }
            E::SetMap { e, bounds } => {
                let (nm, set) = match simple_bound(bounds) {
                    Some(x) => x,
                    None => {
                        let (b, inner) = match self.bounds(bounds, sc) {
                            Some(x) => x,
                            None => return self.fallback(n, sc),
                        };
                        let e = self.expr(e, &inner);
                        return Box::new(move |cx| {
                            let mut out: Vec<Value> = Vec::new();
                            b.each(cx, &mut || {
                                out.push(e(cx)?);
                                Ok(false)
                            })?;
                            mk_set(out)
                        });
                    }
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let e = self.expr(e, &push(sc, ScK::Slot { name: nm, slot }));
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    let mut out: Vec<Value> = Vec::new();
                    if let SetK::Interval(lo, hi) = &s.k {
                        for i in *lo..=*hi {
                            cx.f.set(slot, Value::Int(i));
                            out.push(e(cx)?);
                        }
                    } else {
                        for x in s.elems()? {
                            cx.f.set(slot, x.clone());
                            out.push(e(cx)?);
                        }
                    }
                    mk_set(out)
                })
            }
            E::FnDef { bounds, body, is_rec, .. } => {
                let (nm, set) = match simple_bound(bounds) {
                    Some(x) if !is_rec.get() => x,
                    _ => return self.fallback(n, sc),
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                let body = self.expr(body, &push(sc, ScK::Slot { name: nm, slot }));
                let lazy = self.fallback(n, sc);
                Box::new(move |cx| {
                    let s = as_set(set(cx)?)?;
                    if !s.enumerable() {
                        return lazy(cx);
                    }
                    if let SetK::Interval(1, hi) = &s.k {
                        let mut vals = Vec::with_capacity((*hi).max(0) as usize);
                        for i in 1..=*hi {
                            cx.f.set(slot, Value::Int(i));
                            vals.push(body(cx)?);
                        }
                        return Ok(if vals.is_empty() { empty_tuple() } else { Value::Tuple(TupleV::rc(vals)) });
                    }
                    let dom = s.elems()?;
                    let mut vals = Vec::with_capacity(dom.len());
                    for d in dom {
                        cx.f.set(slot, d.clone());
                        vals.push(body(cx)?);
                    }
                    Ok(s.fcn_shape()?.make(vals))
                })
            }
            E::Rec(fields, shape) => {
                let ces: Vec<CE> = fields.iter().map(|(_, e)| self.expr(e, sc)).collect();
                Box::new(move |cx| {
                    let mut vals = Vec::with_capacity(ces.len());
                    for c in &ces {
                        vals.push(c(cx)?);
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
                })
            }
            E::Except { base, updates } => {
                let base = self.expr(base, sc);
                let dbase = self.dshape.take();
                let at = self.slot();
                let inner = push(sc, ScK::At { slot: at });
                if let (Some(d), true, true) = (&dbase, updates.len() == 1, self.cache) {
                    if d.direct {
                        // [var EXCEPT !path = v]: for the step cache, a change of the variable at that path
                        let (path, val) = &updates[0];
                        let pces: Rc<Vec<CE>> = Rc::new(path.iter().map(|x| self.expr(x, sc)).collect());
                        let vce: Rc<CE> = Rc::new(self.expr(val, &inner));
                        let needs_old = path.len() > 1 || uses_at(val);
                        let var = d.var;
                        let (p2, v2) = (pces.clone(), vce.clone());
                        self.dshape = Some(DShape {
                            var,
                            direct: false,
                            prog: Rc::new(move |cx, ops| {
                                let mut keys = Vec::with_capacity(p2.len());
                                for x in p2.iter() {
                                    keys.push(x(cx)?);
                                }
                                let cur = cx.cur.get(var);
                                let mut newv = None;
                                cx.ev.except_with(
                                    cur.clone(),
                                    &keys,
                                    0,
                                    &mut |old| {
                                        cx.f.set(at, old);
                                        let v = v2(cx)?;
                                        newv = Some(v.clone());
                                        Ok(v)
                                    },
                                    n,
                                )?;
                                let v = match newv {
                                    Some(v) => v,
                                    None => return Ok(false),
                                };
                                if needs_old {
                                    match sc_::elem_at(&cur, &keys[0]) {
                                        Some(old) => cx.rec.borrow_mut().reads.push((Loc::Elem(var as u32, keys[0].clone()), old)),
                                        None => return Ok(false),
                                    }
                                }
                                ops.push(DOp::Exc { path: keys, v });
                                Ok(true)
                            }),
                        });
                        self.dshape_ok = true;
                        return Box::new(move |cx| {
                            let f = base(cx)?;
                            let mut short: [Value; 2] = [Value::Undef, Value::Undef];
                            let long: Vec<Value>;
                            let keys: &[Value] = if pces.len() <= 2 {
                                for (i, x) in pces.iter().enumerate() {
                                    short[i] = x(cx)?;
                                }
                                &short[..pces.len()]
                            } else {
                                let mut v = Vec::with_capacity(pces.len());
                                for x in pces.iter() {
                                    v.push(x(cx)?);
                                }
                                long = v;
                                &long
                            };
                            cx.ev.except_with(
                                f,
                                keys,
                                0,
                                &mut |old| {
                                    cx.f.set(at, old);
                                    vce(cx)
                                },
                                n,
                            )
                        });
                    }
                }
                let ups: Vec<(Vec<CE>, CE)> = updates.iter().map(|(path, val)| (path.iter().map(|x| self.expr(x, sc)).collect(), self.expr(val, &inner))).collect();
                Box::new(move |cx| {
                    let mut f = base(cx)?;
                    for (path, val) in &ups {
                        let mut short: [Value; 2] = [Value::Undef, Value::Undef];
                        let long: Vec<Value>;
                        let p: &[Value] = if path.len() <= 2 {
                            for (i, x) in path.iter().enumerate() {
                                short[i] = x(cx)?;
                            }
                            &short[..path.len()]
                        } else {
                            let mut v = Vec::with_capacity(path.len());
                            for x in path {
                                v.push(x(cx)?);
                            }
                            long = v;
                            &long
                        };
                        f = cx.ev.except_with(
                            f,
                            p,
                            0,
                            &mut |old| {
                                cx.f.set(at, old);
                                val(cx)
                            },
                            n,
                        )?;
                    }
                    Ok(f)
                })
            }
            E::FnApp { f, args } => {
                if !self.operand_ok(f, sc) {
                    return self.fallback(n, sc);
                }
                let fvar = var_of(f);
                let fce = self.expr(f, sc);
                let args: Vec<CE> = args.iter().map(|a| self.expr(a, sc)).collect();
                if let (Some(idx), true) = (fvar, self.cache) {
                    // var[k]: for the step cache this reads one element of the variable
                    return Box::new(move |cx| {
                        let fv = cx.cur.get(idx);
                        let arg = if args.len() == 1 {
                            args[0](cx)?
                        } else {
                            let mut t = Vec::with_capacity(args.len());
                            for a in &args {
                                t.push(a(cx)?);
                            }
                            Value::Tuple(TupleV::rc(t))
                        };
                        let v = cx.ev.apply_fcn(&fv, &arg, Some(n))?;
                        if cx.rec_on.get() {
                            cx.rec.borrow_mut().reads.push((Loc::Elem(idx as u32, arg), v.clone()));
                        }
                        if let Value::LazyFcn(lf) = &v {
                            return lf.force(cx.ev);
                        }
                        Ok(v)
                    });
                }
                Box::new(move |cx| {
                    let fv = fce(cx)?;
                    let arg = if args.len() == 1 {
                        args[0](cx)?
                    } else {
                        let mut t = Vec::with_capacity(args.len());
                        for a in &args {
                            t.push(a(cx)?);
                        }
                        Value::Tuple(TupleV::rc(t))
                    };
                    let v = cx.ev.apply_fcn(&fv, &arg, Some(n))?;
                    if let Value::LazyFcn(lf) = &v {
                        return lf.force(cx.ev);
                    }
                    Ok(v)
                })
            }
            E::Dot { e, field } => {
                let e = self.expr(e, sc);
                let field = *field;
                Box::new(move |cx| match e(cx)? {
                    Value::Record(rec) => match rec.get(field) {
                        Some(v) => Ok(v.clone()),
                        None => bail(),
                    },
                    _ => bail(),
                })
            }
            _ => self.fallback(n, sc),
        }
    }

    fn def_app(&mut self, n: N, d: &'static Def, args: &'static [Node], sc: &Rc<Sc>) -> CE {
        let d = d.over.get().unwrap_or(d);
        if let Some(bi) = d.builtin.get() {
            return self.builtin(n, d, bi, args, sc);
        }
        let body = match d.body.get() {
            Some(b) if d.inst.is_none() => b,
            _ => return self.fallback(n, sc),
        };
        let id = d as *const Def as usize;
        if self.stack.contains(&id) || self.stack.len() > 40 {
            return self.fallback(n, sc);
        }
        if d.params.is_empty() && args.is_empty() && crate::modules::def_level(d) == 0 {
            // a constant definition: the tree-walker evaluates it once and keeps the value on the definition
            let cell: OnceCell<Value> = OnceCell::new();
            return Box::new(move |cx| {
                if let Some(v) = cell.get() {
                    return Ok(v.clone());
                }
                let v = cx.ev.eval(n, &None)?;
                if d.cache.borrow().is_some() && plain(&v) {
                    let _ = cell.set(v.clone());
                }
                Ok(v)
            });
        }
        // A definition with no parameters that an invariant refers to is memoised for the state, so an
        // invariant that refers to it after another one has does not evaluate its body again.
        let memo = match &self.inv_memo {
            Some(m) if d.params.is_empty() && args.is_empty() && crate::modules::def_level(d) <= 1 => Some((m.clone(), m.slot(id))),
            _ => None,
        };
        let root = Rc::new(Sc { k: ScK::Root(None), next: None });
        match self.bind_args(&d.params, args, root, sc) {
            Some((inner, clear)) => {
                self.stack.push(id);
                let b = self.expr(body, &inner);
                self.stack.pop();
                self.keep_shape(&clear);
                let b = with_clear(clear, b);
                match memo {
                    // The body is inlined with slots of its own, which are read only inside it, so a hit
                    // that skips the body never reads a stale one. The shape is dropped: a caller may use
                    // it only when it evaluates the body itself.
                    Some((memo, slot)) if !self.unstable => {
                        self.shape = None;
                        self.shape_ok = false;
                        self.dshape = None;
                        self.dshape_ok = false;
                        Box::new(move |cx| {
                            if let Some(v) = memo.get(slot) {
                                return Ok(v);
                            }
                            let v = b(cx)?;
                            memo.put(slot, &v);
                            Ok(v)
                        })
                    }
                    _ => b,
                }
            }
            None => self.fallback(n, sc),
        }
    }

    fn builtin(&mut self, n: N, d: &'static Def, bi: &'static Builtin, args: &'static [Node], sc: &Rc<Sc>) -> CE {
        if bi.lazy || bi.ops != 0 {
            return self.fallback(n, sc);
        }
        if let BFn::Const(v) = &bi.f {
            if args.is_empty() && plain(v) {
                return Box::new(move |_| Ok(v.clone()));
            }
        }
        let bags = name_str(d.module).as_ref() == "Bags";
        let opname = name_str(d.name);
        let mut ces: Vec<CE> = Vec::with_capacity(args.len());
        let mut last_shape = None;
        let mut first_d = None;
        for (i, a) in args.iter().enumerate() {
            ces.push(self.expr(a, sc));
            last_shape = self.shape.take();
            if i == 0 {
                first_d = self.dshape.take();
            }
        }
        if bags && args.len() == 2 && opname.as_ref() == "BagIn" && self.cache {
            if let Some(idx) = var_of(&args[1]) {
                // BagIn(x, var): for the step cache this reads whether one value is in the bag
                let x = ces.into_iter().next().unwrap();
                return Box::new(move |cx| {
                    let x = x(cx)?;
                    let b = cx.cur.get(idx);
                    let r = cx.ev.call_builtin(bi, &[x.clone(), b])?;
                    if cx.rec_on.get() {
                        cx.rec.borrow_mut().reads.push((Loc::Member(idx as u32, x), r.clone()));
                    }
                    Ok(r)
                });
            }
        }
        if bags && args.len() == 1 && opname.as_ref() == "SetToBag" {
            // SetToBag({e}): remembered for a consumer
            if let Some(sh) = last_shape.take() {
                if !sh.bag {
                    self.shape = Some(One { bag: true, ..sh });
                    self.shape_ok = true;
                }
            }
        }
        if bags && args.len() == 2 && matches!(opname.as_ref(), "\\oplus" | "\\ominus") {
            if let Some(sh) = last_shape.take() {
                if sh.bag {
                    // B (+) SetToBag({e}) / B (-) SetToBag({e}): one element in or out of the bag
                    let plus = opname.as_ref() == "\\oplus";
                    if let Some(d) = first_d {
                        let sh2 = sh.clone();
                        self.dshape = Some(DShape {
                            var: d.var,
                            direct: false,
                            prog: Rc::new(move |cx, ops| {
                                if !(d.prog)(cx, ops)? {
                                    return Ok(false);
                                }
                                ops.push(DOp::Bag { e: sh2.eval(cx)?, plus });
                                Ok(true)
                            }),
                        });
                        self.dshape_ok = true;
                    }
                    let mut it = ces.into_iter();
                    let (b, one) = (it.next().unwrap(), it.next().unwrap());
                    return Box::new(move |cx| {
                        let bv = b(cx)?;
                        let e = sh.eval(cx)?;
                        if let Some(v) = crate::stdlib::bag_one(&bv, &e, plus) {
                            return Ok(v);
                        }
                        // anything unusual: the operator itself, on the one-element bag
                        let y = one(cx)?;
                        cx.ev.call_builtin(bi, &[bv, y])
                    });
                }
            }
        }
        if bi.arith != 0 && ces.len() == 2 {
            let mut it = ces.into_iter();
            let (x, y) = (it.next().unwrap(), it.next().unwrap());
            let arith = bi.arith;
            return Box::new(move |cx| {
                let x = x(cx)?;
                let y = y(cx)?;
                if let (Value::Int(a), Value::Int(b)) = (&x, &y) {
                    let (a, b) = (*a, *b);
                    std::mem::forget(x); // two integers: nothing to drop
                    std::mem::forget(y);
                    match arith {
                        1 | 2 => {
                            let r = if arith == 1 { a.checked_add(b) } else { a.checked_sub(b) };
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
                    // out of range: the operator itself reports it
                    return cx.ev.call_builtin(bi, &[Value::Int(a), Value::Int(b)]);
                }
                cx.ev.call_builtin(bi, &[x, y])
            });
        }
        match ces.len() {
            1 => {
                let a = ces.into_iter().next().unwrap();
                Box::new(move |cx| cx.ev.call_builtin(bi, &[a(cx)?]))
            }
            2 => {
                let mut it = ces.into_iter();
                let (a, b) = (it.next().unwrap(), it.next().unwrap());
                Box::new(move |cx| {
                    let x = a(cx)?;
                    let y = b(cx)?;
                    cx.ev.call_builtin(bi, &[x, y])
                })
            }
            _ => Box::new(move |cx| {
                let mut v = Vec::with_capacity(ces.len());
                for c in &ces {
                    v.push(c(cx)?);
                }
                cx.ev.call_builtin(bi, &v)
            }),
        }
    }

    fn op(&mut self, n: N, k: K, a: &'static [Node], sc: &Rc<Sc>) -> CE {
        match k {
            K::And | K::Or => {
                let ces: Vec<CE> = a.iter().map(|x| self.expr(x, sc)).collect();
                let stop = k == K::Or;
                Box::new(move |cx| {
                    for c in &ces {
                        if truth(c(cx)?)? == stop {
                            return Ok(Value::Bool(stop));
                        }
                    }
                    Ok(Value::Bool(!stop))
                })
            }
            K::Not => {
                let x = self.expr(&a[0], sc);
                Box::new(move |cx| Ok(Value::Bool(!truth(x(cx)?)?)))
            }
            K::Imp => {
                let (x, y) = (self.expr(&a[0], sc), self.expr(&a[1], sc));
                Box::new(move |cx| Ok(Value::Bool(!truth(x(cx)?)? || truth(y(cx)?)?)))
            }
            K::Eqv => {
                let (x, y) = (self.expr(&a[0], sc), self.expr(&a[1], sc));
                Box::new(move |cx| Ok(Value::Bool(truth(x(cx)?)? == truth(y(cx)?)?)))
            }
            K::Eq | K::Ne => {
                let want = k == K::Eq;
                let x = self.expr(&a[0], sc);
                if matches!(&a[1].e, E::Op(K::SetEnum, e) if e.is_empty()) {
                    return Box::new(move |cx| {
                        let x = x(cx)?;
                        let eq = match &x {
                            Value::Set(s) if matches!(s.k, SetK::Enum(_)) => match &s.k {
                                SetK::Enum(el) => el.is_empty(),
                                _ => unreachable!(),
                            },
                            _ => val_eq(&x, &Value::Set(empty_set()))?,
                        };
                        Ok(Value::Bool(eq == want))
                    });
                }
                let y = self.expr(&a[1], sc);
                Box::new(move |cx| {
                    let (x, y) = (x(cx)?, y(cx)?);
                    let eq = match scalar_cmp(&x, &y) {
                        Some(c) => c == std::cmp::Ordering::Equal,
                        None => val_eq(&x, &y)?,
                    };
                    Ok(Value::Bool(eq == want))
                })
            }
            K::If => {
                let c: Rc<CE> = Rc::new(self.expr(&a[0], sc));
                let t = self.expr(&a[1], sc);
                let dt = self.dshape.take();
                let e = self.expr(&a[2], sc);
                let de = self.dshape.take();
                if let (Some(dt), Some(de)) = (dt, de) {
                    if dt.var == de.var {
                        let c2 = c.clone();
                        self.dshape = Some(DShape { var: dt.var, direct: false, prog: Rc::new(move |cx, ops| if truth(c2(cx)?)? { (dt.prog)(cx, ops) } else { (de.prog)(cx, ops) }) });
                        self.dshape_ok = true;
                    }
                }
                Box::new(move |cx| if truth(c(cx)?)? { t(cx) } else { e(cx) })
            }
            K::In | K::NotIn => {
                let want = k == K::In;
                let (x, s) = (self.expr(&a[0], sc), self.expr(&a[1], sc));
                if let (Some(idx), true) = (var_of(&a[1]), self.cache) {
                    // x \in var: for the step cache this reads whether one value is in the variable
                    return Box::new(move |cx| {
                        let x = x(cx)?;
                        let r = as_set(cx.cur.get(idx))?.contains(&x)?;
                        if cx.rec_on.get() {
                            cx.rec.borrow_mut().reads.push((Loc::Member(idx as u32, x), Value::Bool(r)));
                        }
                        Ok(Value::Bool(r == want))
                    });
                }
                Box::new(move |cx| {
                    let x = x(cx)?;
                    Ok(Value::Bool(as_set(s(cx)?)?.contains(&x)? == want))
                })
            }
            K::Cup => {
                let x = self.expr(&a[0], sc);
                let dx = self.dshape.take();
                let y = self.expr(&a[1], sc);
                if let Some(sh) = self.shape.take().filter(|sh| !sh.bag) {
                    if let Some(d) = dx {
                        let sh2 = sh.clone();
                        self.dshape = Some(DShape {
                            var: d.var,
                            direct: false,
                            prog: Rc::new(move |cx, ops| {
                                if !(d.prog)(cx, ops)? {
                                    return Ok(false);
                                }
                                ops.push(DOp::Set { e: sh2.eval(cx)?, add: true });
                                Ok(true)
                            }),
                        });
                        self.dshape_ok = true;
                    }
                    // S \cup {e}
                    return Box::new(move |cx| {
                        let xs = as_set(x(cx)?)?;
                        let e = sh.eval(cx)?;
                        if let Some(v) = set_one(&xs, &e, true) {
                            return Ok(v);
                        }
                        let ys = as_set(y(cx)?)?;
                        cx.ev.set_union(xs, ys)
                    });
                }
                Box::new(move |cx| {
                    let x = as_set(x(cx)?)?;
                    let y = as_set(y(cx)?)?;
                    cx.ev.set_union(x, y)
                })
            }
            K::Diff | K::Cap => {
                let x = self.expr(&a[0], sc);
                let dx = self.dshape.take();
                let y = self.expr(&a[1], sc);
                let diff = k == K::Diff;
                let one = self.shape.take().filter(|sh| !sh.bag && diff);
                if let (Some(d), Some(sh2)) = (dx, one.clone()) {
                    self.dshape = Some(DShape {
                        var: d.var,
                        direct: false,
                        prog: Rc::new(move |cx, ops| {
                            if !(d.prog)(cx, ops)? {
                                return Ok(false);
                            }
                            ops.push(DOp::Set { e: sh2.eval(cx)?, add: false });
                            Ok(true)
                        }),
                    });
                    self.dshape_ok = true;
                }
                Box::new(move |cx| {
                    if let Some(sh) = &one {
                        // S \ {e}
                        let xs = as_set(x(cx)?)?;
                        let e = sh.eval(cx)?;
                        if let Some(v) = set_one(&xs, &e, false) {
                            return Ok(v);
                        }
                    }
                    let x = as_set(x(cx)?)?;
                    let y = as_set(y(cx)?)?;
                    if x.reducible() && (diff || y.reducible()) {
                        let mut out = Vec::new();
                        for e in x.elems()? {
                            if y.contains(e)? != diff {
                                out.push(e.clone());
                            }
                        }
                        return Ok(SetV::of(out));
                    }
                    Ok(Value::Set(Rc::new(SetV::new(if diff { SetK::Diff(x, y) } else { SetK::Cap(x, y) }))))
                })
            }
            K::SetEnum if a.len() == 1 => {
                let e: Rc<CE> = Rc::new(self.expr(&a[0], sc));
                self.shape = Some(One { bag: false, elem: e.clone(), clear: vec![] });
                self.shape_ok = true;
                Box::new(move |cx| Ok(SetV::of(vec![e(cx)?])))
            }
            K::SetEnum => {
                let ces: Vec<CE> = a.iter().map(|x| self.expr(x, sc)).collect();
                Box::new(move |cx| {
                    let mut out = Vec::with_capacity(ces.len());
                    for c in &ces {
                        out.push(c(cx)?);
                    }
                    mk_set(out)
                })
            }
            K::Tuple => {
                let ces: Vec<CE> = a.iter().map(|x| self.expr(x, sc)).collect();
                Box::new(move |cx| {
                    let mut out = Vec::with_capacity(ces.len());
                    for c in &ces {
                        out.push(c(cx)?);
                    }
                    Ok(Value::Tuple(TupleV::rc(out)))
                })
            }
            K::Domain => {
                if !self.operand_ok(&a[0], sc) {
                    return self.fallback(n, sc);
                }
                let f = self.expr(&a[0], sc);
                Box::new(move |cx| {
                    let f = f(cx)?;
                    if let Value::LazyFcn(lf) = &f {
                        return Ok(Value::Set(lf.domain(cx.ev)?));
                    }
                    match domain_of(&f) {
                        Some(d) => Ok(Value::Set(d)),
                        None => bail(),
                    }
                })
            }
            _ => self.fallback(n, sc),
        }
    }

    // ---------- actions ----------
    /// The variables of `UNCHANGED e` when `e` is a variable, a tuple of such, or a name for one.
    fn unchanged_vars(&self, e: N, out: &mut Vec<u32>, depth: u32) -> bool {
        if depth > 16 {
            return false;
        }
        if let Some(i) = var_of(e) {
            out.push(i as u32);
            return true;
        }
        match &e.e {
            E::Op(K::Tuple, items) => items.iter().all(|x| self.unchanged_vars(x, out, depth + 1)),
            E::App { args, sel: None, r, .. } if args.is_empty() => match r.get() {
                Res::Def(d) => {
                    let d = d.over.get().unwrap_or(d);
                    match d.body.get() {
                        Some(b) if d.builtin.get().is_none() && d.inst.is_none() && d.params.is_empty() && matches!(b.e, E::Op(K::Tuple, _)) => self.unchanged_vars(b, out, depth + 1),
                        _ => false,
                    }
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn act(&mut self, n: N, sc: &Rc<Sc>) -> AE {
        let inner = self.act_inner(n, sc);
        // once every variable is assigned the tree-walker treats what follows as a plain predicate
        let sc = sc.clone();
        Box::new(move |cx, k| {
            if cx.ev.n_assigned.get() == cx.nv {
                if std::env::var_os("EVERYSTATE_EVAL_DEBUG").is_some() {
                    eprintln!("fallback all-assigned at line {} col {}", n.loc[0], n.loc[1]);
                }
                cx.fallbacks.set(cx.fallbacks.get() + 1);
                let ctx = build(&sc, cx, false)?;
                return cx.ev.enumerate(n, &ctx, k);
            }
            inner(cx, k)
        })
    }

    fn guard(&mut self, n: N, sc: &Rc<Sc>) -> AE {
        let ce = self.expr(n, sc);
        Box::new(move |cx, k| if truth(ce(cx)?)? { k() } else { Ok(()) })
    }

    /// With the step cache on: above the units the action is only disjunctions, existential quantifiers,
    /// LETs and inlined definitions; whatever else is met there is a unit.
    fn act_inner(&mut self, n: N, sc: &Rc<Sc>) -> AE {
        let top = std::mem::replace(&mut self.top, false);
        if !top || !self.cache {
            return self.act_inner0(n, sc);
        }
        let structural = match &n.e {
            E::Op(K::Or, _) | E::Let { .. } | E::Quant { forall: false, .. } => true,
            E::App { sel: None, r, .. } => matches!(r.get(), Res::Def(d) if d.over.get().unwrap_or(d).builtin.get().is_none()),
            _ => false,
        };
        if structural {
            self.descend = true;
            let r = self.act_inner0(n, sc);
            self.descend = false;
            return r;
        }
        self.unit(n, sc)
    }
    fn unit(&mut self, n: N, sc: &Rc<Sc>) -> AE {
        let inner = self.act_inner0(n, sc);
        // what the unit depends on besides the state: the variables bound by the quantifiers above it
        // (whether or not its own scope names them: an inlined definition sees them through its arguments)
        let bound = self.top_slots.clone();
        // values kept for by-name bindings may have been computed before the unit: they are computed
        // again inside it when it is recorded, so that what they read is noted
        let clear = self.cache_slots.clone();
        let id = (self.plan_id << 16) | self.units;
        self.units += 1;
        let stat = Rc::new(UnitStat { loc: n.loc, lookups: Cell::new(0), hits: Cell::new(0), off: Cell::new(false), skip: Cell::new(0), penalty: Cell::new(0), phase: Cell::new(PH_WARM), count: Cell::new(0), acc: Default::default(), seen: Cell::new(0), arm: Cell::new(false), last: Cell::new((0.0, 0.0)), trials: Cell::new(0), again: Cell::new(1 << 20), held: Cell::new(false), mark: Cell::new(0), mark_l: Cell::new(0), stored: Cell::new(0), mark_s: Cell::new(0) });
        self.unit_stats.push(stat.clone());
        Box::new(move |cx, k| unit_run(cx, k, id, &bound, &clear, &inner, &stat, n))
    }
    fn act_inner0(&mut self, n: N, sc: &Rc<Sc>) -> AE {
        let desc = std::mem::replace(&mut self.descend, false);
        self.budget -= 1;
        if self.budget < 0 {
            return fb_act(n, sc);
        }
        match &n.e {
            E::Op(k, a) => match k {
                K::And => {
                    // (the first conjunct starts with the same assignments as the conjunction itself)
                    let items: Vec<AE> = a.iter().enumerate().map(|(i, x)| if i == 0 { self.act_inner(x, sc) } else { self.act(x, sc) }).collect();
                    if items.is_empty() {
                        return Box::new(|_, k| k());
                    }
                    fn conj(items: &[AE], i: usize, cx: &Cx, k: &mut dyn FnMut() -> R<()>) -> R<()> {
                        if i + 1 == items.len() {
                            return items[i](cx, k);
                        }
                        items[i](cx, &mut || conj(items, i + 1, cx, &mut *k))
                    }
                    Box::new(move |cx, k| conj(&items, 0, cx, k))
                }
                K::Or => {
                    let items: Vec<AE> = a
                        .iter()
                        .map(|x| {
                            self.top = desc;
                            self.act_inner(x, sc)
                        })
                        .collect();
                    Box::new(move |cx, k| {
                        for it in &items {
                            it(cx, k)?;
                        }
                        Ok(())
                    })
                }
                K::If => {
                    let c = self.expr(&a[0], sc);
                    let (t, e) = (self.act_inner(&a[1], sc), self.act_inner(&a[2], sc));
                    Box::new(move |cx, k| if truth(c(cx)?)? { t(cx, k) } else { e(cx, k) })
                }
                K::Eq | K::In => {
                    // x' = e / x' \in S with x' a variable named directly
                    let tgt = match &a[0].e {
                        E::Op(K::Prime, p) => var_of(&p[0]),
                        _ => None,
                    };
                    match tgt {
                        Some(idx) => {
                            let rhs = self.expr(&a[1], sc);
                            let dprog = self.dshape.take().filter(|d| d.var == idx && self.cache && *k == K::Eq).map(|d| d.prog);
                            let assigned = fb_act(n, sc);
                            let is_eq = *k == K::Eq;
                            Box::new(move |cx, k| {
                                if !cx.nxt.is_undef(idx) {
                                    // already assigned: a condition on the next state
                                    return assigned(cx, k);
                                }
                                let ev = cx.ev;
                                if let (Some(prog), true) = (&dprog, cx.rec_on.get()) {
                                    // recording for the step cache: the new value as changes to the old one
                                    let mut ops = vec![];
                                    if prog(cx, &mut ops)? {
                                        if let Some(v) = apply_ops(cx, &cx.cur.get(idx), &ops, n) {
                                            cx.nxt.set(idx, v);
                                            cx.rec.borrow_mut().delta[idx] = Some(ops);
                                            ev.n_assigned.set(ev.n_assigned.get() + 1);
                                            let r = k();
                                            cx.nxt.clear(idx);
                                            cx.rec.borrow_mut().delta[idx] = None;
                                            ev.n_assigned.set(ev.n_assigned.get() - 1);
                                            return r;
                                        }
                                    }
                                }
                                if is_eq {
                                    let v = rhs(cx)?;
                                    cx.nxt.set(idx, v);
                                    ev.n_assigned.set(ev.n_assigned.get() + 1);
                                    let r = k();
                                    cx.nxt.clear(idx);
                                    ev.n_assigned.set(ev.n_assigned.get() - 1);
                                    return r;
                                }
                                let s = as_set(rhs(cx)?)?;
                                let es = s.elems()?;
                                ev.n_assigned.set(ev.n_assigned.get() + 1);
                                let mut r = Ok(());
                                for x in es {
                                    cx.nxt.set(idx, x.clone());
                                    r = k();
                                    if r.is_err() {
                                        break;
                                    }
                                }
                                cx.nxt.clear(idx);
                                ev.n_assigned.set(ev.n_assigned.get() - 1);
                                r
                            })
                        }
                        None => match &a[0].e {
                            // the left side may still denote a primed variable (a parameter, a definition)
                            E::Op(K::Prime, _) | E::Let { .. } => fb_act(n, sc),
                            E::App { name, args, sel, r, .. } if args.is_empty() => match r.get() {
                                Res::Local if sel.is_none() && matches!(lookup(sc, *name), Found::Slot(_) | Found::Const(_)) => self.guard(n, sc),
                                Res::Decl(d) if sel.is_none() && d.subst.get().is_none() => self.guard(n, sc),
                                _ => fb_act(n, sc),
                            },
                            _ => self.guard(n, sc),
                        },
                    }
                }
                K::Unchanged => {
                    let mut idxs = vec![];
                    if !self.unchanged_vars(&a[0], &mut idxs, 0) || idxs.len() > 32 {
                        return fb_act(n, sc);
                    }
                    let mut seen: u64 = 0;
                    let distinct = idxs.iter().all(|&i| {
                        let fresh = i < 64 && seen & (1 << i) == 0;
                        seen |= 1 << (i & 63);
                        fresh
                    });
                    Box::new(move |cx, k| {
                        let ev = cx.ev;
                        if distinct && cx.nxt.can_fill(cx.cur, &idxs) {
                            cx.nxt.fill(cx.cur, &idxs);
                            ev.n_assigned.set(ev.n_assigned.get() + idxs.len() as i64);
                            if cx.rec_on.get() {
                                let mut rec = cx.rec.borrow_mut();
                                for &i in &idxs {
                                    rec.delta[i as usize] = Some(vec![]);
                                }
                            }
                            let r = k();
                            if cx.rec_on.get() {
                                let mut rec = cx.rec.borrow_mut();
                                for &i in &idxs {
                                    rec.delta[i as usize] = None;
                                }
                            }
                            for &i in idxs.iter().rev() {
                                cx.nxt.clear(i as usize);
                            }
                            ev.n_assigned.set(ev.n_assigned.get() - idxs.len() as i64);
                            return r;
                        }
                        if cx.rec_on.get() {
                            // (a comparison with the next state: not something an entry describes)
                            cx.rec.borrow_mut().bad = true;
                        }
                        let mut set: u32 = 0;
                        let mut r: R<()> = Ok(());
                        let mut go_on = true;
                        for (j, &i) in idxs.iter().enumerate() {
                            let i = i as usize;
                            if cx.nxt.is_undef(i) {
                                let v = cx.cur.get(i);
                                if matches!(v, Value::Undef) {
                                    r = bail();
                                    go_on = false;
                                    break;
                                }
                                cx.nxt.set(i, v);
                                ev.n_assigned.set(ev.n_assigned.get() + 1);
                                set |= 1 << j;
                            } else {
                                match val_eq(&cx.nxt.get(i), &cx.cur.get(i)) {
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
                        if go_on {
                            r = k();
                        }
                        for j in (0..idxs.len()).rev() {
                            if set & (1 << j) != 0 {
                                cx.nxt.clear(idxs[j] as usize);
                            }
                        }
                        ev.n_assigned.set(ev.n_assigned.get() - set.count_ones() as i64);
                        r
                    })
                }
                // the enumerator has its own rules for these
                K::Imp | K::Subseteq | K::BoxAct | K::AngleAct | K::Cdot => fb_act(n, sc),
                _ => self.guard(n, sc),
            },
            E::Quant { forall: false, bounds, body } => {
                let (nm, set) = match simple_bound(bounds) {
                    Some(x) => x,
                    None => {
                        let (b, inner) = match self.bounds(bounds, sc) {
                            Some(x) => x,
                            None => return fb_act(n, sc),
                        };
                        self.top = desc;
                        let mark = self.top_slots.len();
                        if desc {
                            for fb in &b.flat {
                                self.top_slots.extend_from_slice(&fb.slots);
                            }
                        }
                        let body = self.act_inner(body, &inner);
                        self.top_slots.truncate(mark);
                        return Box::new(move |cx, k| {
                            b.each(cx, &mut || {
                                body(cx, &mut *k)?;
                                Ok(false)
                            })?;
                            Ok(())
                        });
                    }
                };
                let set = self.expr(set, sc);
                let slot = self.slot();
                self.top = desc;
                if desc {
                    self.top_slots.push(slot);
                }
                let body = self.act_inner(body, &push(sc, ScK::Slot { name: nm, slot }));
                if desc {
                    self.top_slots.pop();
                }
                Box::new(move |cx, k| {
                    let s = as_set(set(cx)?)?;
                    if let SetK::Interval(lo, hi) = &s.k {
                        for i in *lo..=*hi {
                            cx.f.set(slot, Value::Int(i));
                            body(cx, k)?;
                        }
                        return Ok(());
                    }
                    for x in s.elems()? {
                        cx.f.set(slot, x.clone());
                        body(cx, k)?;
                    }
                    Ok(())
                })
            }
            E::Quant { .. } => fb_act(n, sc),
            E::Case { arms, other } => {
                let arms: Vec<(CE, AE)> = arms.iter().map(|(c, e)| (self.expr(c, sc), self.act_inner(e, sc))).collect();
                let other = other.as_ref().map(|o| self.act_inner(o, sc));
                Box::new(move |cx, k| {
                    for (c, e) in &arms {
                        if truth(c(cx)?)? {
                            return e(cx, k);
                        }
                    }
                    match &other {
                        Some(o) => o(cx, k),
                        None => bail(),
                    }
                })
            }
            E::Let { defs, body } => match self.let_scope(defs, sc) {
                Some((inner, clear)) => {
                    self.top = desc;
                    let body = self.act_inner(body, &inner);
                    Box::new(move |cx, k| {
                        run_pre(&clear, cx);
                        body(cx, k)
                    })
                }
                None => fb_act(n, sc),
            },
            E::App { name, args, sel, r, .. } => {
                if sel.is_some() {
                    return fb_act(n, sc);
                }
                match r.get() {
                    Res::Def(d) => {
                        let d = d.over.get().unwrap_or(d);
                        if d.builtin.get().is_some() {
                            return self.guard(n, sc);
                        }
                        let body = match d.body.get() {
                            Some(b) if d.inst.is_none() => b,
                            _ => return fb_act(n, sc),
                        };
                        let id = d as *const Def as usize;
                        if self.stack.contains(&id) || self.stack.len() > 40 {
                            return fb_act(n, sc);
                        }
                        let root = Rc::new(Sc { k: ScK::Root(None), next: None });
                        match self.bind_args(&d.params, args, root, sc) {
                            Some((inner, clear)) => {
                                self.stack.push(id);
                                self.top = desc;
                                let b = self.act_inner(body, &inner);
                                self.stack.pop();
                                Box::new(move |cx, k| {
                                    run_pre(&clear, cx);
                                    b(cx, k)
                                })
                            }
                            None => fb_act(n, sc),
                        }
                    }
                    Res::Decl(d) => {
                        if d.subst.get().is_some() {
                            fb_act(n, sc)
                        } else {
                            self.guard(n, sc)
                        }
                    }
                    Res::Local => match lookup(sc, *name) {
                        // a bound variable or a constant: a plain condition
                        Found::Slot(_) | Found::Const(_) if args.is_empty() => self.guard(n, sc),
                        // a parameter or a LET definition: the enumerator enters the expression it stands for
                        _ => fb_act(n, sc),
                    },
                    Res::None => fb_act(n, sc),
                }
            }
            // the enumerator enters the body of a lazily evaluated function; a state variable is not one
            E::FnApp { f, .. } if var_of(f).is_some() => self.guard(n, sc),
            E::FnApp { .. } => fb_act(n, sc),
            _ => self.guard(n, sc),
        }
    }
}

const LEAF: u64 = 0x1EAF_1EAF_1EAF_1EAF;
fn bound_eq(vals: &[Value], cx: &Cx, bound: &[usize]) -> bool {
    vals.len() == bound.len() && vals.iter().zip(bound).all(|(v, &s)| sc_::same(v, &cx.f.get(s)))
}
/// A unit with the step cache on: the stored successors when an entry matches the state, else an
/// evaluation that is recorded and stored.
#[allow(clippy::too_many_arguments)]
fn unit_run(cx: &Cx, k: &mut dyn FnMut() -> R<()>, id: u32, bound: &[usize], clear: &[usize], inner: &AE, stat: &Rc<UnitStat>, n: N) -> R<()> {
    let table = match cx.cache {
        Some(t) if !cx.rec_on.get() && cx.ev.n_assigned.get() == 0 => t,
        _ => return inner(cx, k),
    };
    // Whether the cache pays is measured, not assumed, and measured on the whole work per state rather
    // than on the unit alone (a successor built from an entry shares its new values with its parent and
    // with the other successors built from that entry, which saves time after the unit, in fingerprinting
    // and in memory). After a warm-up the unit goes on trial: each state expanded is taken with or without
    // the cache, by a hash of its number, and the time from that expansion to the next is added to the one
    // or the other mean of every unit on trial evaluated in it (`UnitStat::sample`). The choice is the same
    // for all units on trial, so units that are tried together are judged together, on their joint effect
    // (the effect of one unit alone is often too small to tell from noise in a reasonable time, while
    // twenty such effects add up). A unit gets the cache when the mean with it is lower by 2.5 standard
    // errors (looked at every 256 states from 512 per side on), or by one standard error after 4096
    // states per side; the trial ends without the cache when the mean with it is higher by as much, or
    // higher at all past 1024 states per side (a trial costs time too). A unit that has the cache goes on
    // trial again after a million evaluations (or 16 times the length of its last trial, if that is more),
    // or when 4096 evaluations missed more than one time in five, and keeps it unless that trial goes
    // against it; a unit that does not pay is evaluated without the cache for as long, longer when it
    // fails again (up to 4 million evaluations; at once 4 million when it is far from paying).
    if cx.cache_always {
        // EVERYSTATE_STEP_CACHE=always (for testing): every unit uses the cache, whether or not it pays
        return unit_cached(cx, k, table, id, bound, clear, inner, stat, n);
    }
    let c = stat.count.get() + 1;
    stat.count.set(c);
    match stat.phase.get() {
        PH_OFF => {
            if c >= stat.skip.get() {
                stat.enter(PH_WARM);
            }
            inner(cx, k)
        }
        PH_WARM => {
            if c == 1 {
                stat.mark.set(stat.hits.get());
                stat.mark_l.set(stat.lookups.get());
                stat.mark_s.set(stat.stored.get());
            }
            if c == 32 && stat.hits.get() == stat.mark.get() && stat.stored.get() == stat.mark_s.get() {
                // nothing could be stored in 32 evaluations (the tree-walker was needed, or the key is too
                // large): no entry will ever be found
                stat.turn_off(true);
            } else if c == 256 {
                // a table that is still mostly missing after 256 lookups is not going to pay
                if (stat.hits.get() - stat.mark.get()) * 2 < 256 {
                    stat.turn_off(true);
                } else {
                    stat.begin_trial(cx.meas);
                }
            }
            unit_cached(cx, k, table, id, bound, clear, inner, stat, n)
        }
        PH_TRIAL => {
            let e = cx.meas.exp.get();
            if stat.seen.get() != e {
                stat.seen.set(e);
                stat.arm.set((sc_::mix(e, 0x7A11) >> 17) & 1 == 1);
                cx.meas.touched.borrow_mut().push(stat.clone());
            }
            if stat.arm.get() {
                unit_cached(cx, k, table, id, bound, clear, inner, stat, n)
            } else {
                inner(cx, k)
            }
        }
        _ => {
            if c % 4096 == 0 {
                let (looked, hit) = (stat.lookups.get() - stat.mark_l.get(), stat.hits.get() - stat.mark.get());
                if c >= stat.again.get() || hit * 5 < looked * 4 {
                    stat.begin_trial(cx.meas);
                } else {
                    stat.mark.set(stat.hits.get());
                    stat.mark_l.set(stat.lookups.get());
                }
            }
            unit_cached(cx, k, table, id, bound, clear, inner, stat, n)
        }
    }
}
const PH_WARM: u8 = 0;
const PH_TRIAL: u8 = 1;
const PH_ON: u8 = 3;
const PH_OFF: u8 = 4;
/// Nanoseconds from some fixed moment. (No clock in WebAssembly; the step cache is off there.)
#[cfg(not(target_arch = "wasm32"))]
fn now_ns() -> u64 {
    use std::sync::OnceLock;
    static T0: OnceLock<std::time::Instant> = OnceLock::new();
    T0.get_or_init(std::time::Instant::now).elapsed().as_nanos() as u64 + 1
}
#[cfg(target_arch = "wasm32")]
fn now_ns() -> u64 {
    0
}
/// The measurement shared by the units of one `Plans`: the number of the state being expanded, when its
/// expansion began, and the units on trial that were evaluated in it.
pub struct Meas {
    /// units on trial
    active: Cell<u32>,
    t0: Cell<u64>,
    exp: Cell<u64>,
    touched: RefCell<Vec<Rc<UnitStat>>>,
}
impl Meas {
    fn new() -> Meas {
        Meas { active: Cell::new(0), t0: Cell::new(0), exp: Cell::new(1), touched: RefCell::new(Vec::new()) }
    }
    /// A state is about to be expanded: the time since the last such moment goes to the units on trial
    /// that were evaluated in between. (No clock is read while no unit is on trial.)
    #[inline]
    fn tick(&self) {
        if self.active.get() == 0 && self.t0.get() == 0 {
            return;
        }
        let now = now_ns();
        let t0 = self.t0.replace(if self.active.get() == 0 { 0 } else { now });
        self.exp.set(self.exp.get() + 1);
        let mut t = self.touched.borrow_mut();
        if t0 != 0 {
            for u in t.iter() {
                u.sample((now - t0) as f64, self);
            }
        }
        t.clear();
    }
}
#[derive(Default)]
struct Acc {
    sum: Cell<f64>,
    sq: Cell<f64>,
    n: Cell<u64>,
}
impl Acc {
    fn add(&self, x: f64) {
        self.sum.set(self.sum.get() + x);
        self.sq.set(self.sq.get() + x * x);
        self.n.set(self.n.get() + 1);
    }
    fn reset(&self) {
        self.sum.set(0.0);
        self.sq.set(0.0);
        self.n.set(0);
    }
    fn mean(&self) -> f64 {
        self.sum.get() / self.n.get().max(1) as f64
    }
    /// the variance of the mean
    fn var_mean(&self) -> f64 {
        let n = self.n.get().max(2) as f64;
        let m = self.sum.get() / n;
        ((self.sq.get() / n - m * m).max(0.0)) / (n - 1.0)
    }
}
impl UnitStat {
    fn enter(&self, phase: u8) {
        self.phase.set(phase);
        self.count.set(0);
    }
    fn begin_trial(&self, meas: &Meas) {
        self.held.set(self.phase.get() == PH_ON);
        self.acc[0].reset();
        self.acc[1].reset();
        meas.active.set(meas.active.get() + 1);
        self.enter(PH_TRIAL);
    }
    /// One state expanded with this unit on trial took `dt` ns (to the next expansion).
    fn sample(&self, dt: f64, meas: &Meas) {
        if self.phase.get() != PH_TRIAL {
            return;
        }
        let (a, b) = (&self.acc[0], &self.acc[1]);
        let total = a.n.get() + b.n.get();
        // (one descheduled sample, or one that grew the fingerprint set, must not decide)
        let x = if total >= 32 { dt.min(8.0 * (a.sum.get() + b.sum.get()) / total as f64) } else { dt };
        self.acc[self.arm.get() as usize].add(x);
        let least = a.n.get().min(b.n.get());
        if least < 512 || (total + 1) % 256 != 0 {
            return;
        }
        let (plain, cached) = (a.mean(), b.mean());
        let se = (a.var_mean() + b.var_mean()).sqrt();
        let d = cached - plain;
        self.last.set((plain, cached));
        self.trials.set(total + 1);
        let done = least >= 4096;
        // (a trial of n evaluations is followed by at least 16 n evaluations without one)
        self.again.set((self.count.get() * 16).max(1 << 20));
        // (a unit that had the cache keeps it unless the trial goes against it)
        let held = self.held.get();
        if d < -2.5 * se || (done && d < if held { se } else { -se }) {
            meas.active.set(meas.active.get() - 1);
            self.penalty.set(0);
            self.off.set(false);
            self.mark.set(self.hits.get());
            self.mark_l.set(self.lookups.get());
            self.enter(PH_ON);
        } else if d > 2.5 * se || done || (!held && least >= 1024 && d > 0.0) {
            // (a trial costs time too: past 1024 states per side it goes on only while the cache is ahead)
            meas.active.set(meas.active.get() - 1);
            self.turn_off(d > 3.0 * se && d > 0.05 * plain);
        }
    }
    /// The cache does not pay for this unit; `far`: not worth trying again soon.
    fn turn_off(&self, far: bool) {
        let p = if far { 1 << 22 } else { (self.penalty.get() * 2).clamp(1 << 18, 1 << 22) };
        self.penalty.set(p);
        self.skip.set(p.max(self.again.get()));
        self.off.set(true);
        self.enter(PH_OFF);
    }
}
#[allow(clippy::too_many_arguments)]
fn unit_cached(cx: &Cx, k: &mut dyn FnMut() -> R<()>, table: &RefCell<Table>, id: u32, bound: &[usize], clear: &[usize], inner: &AE, stat: &UnitStat, n: N) -> R<()> {
    let nv = cx.nv as usize;
    let mut h0 = sc_::mix(0x5EED, id as u64);
    for &s in bound {
        match value_word(&cx.f.get(s)) {
            Ok(w) => h0 = sc_::mix(h0, w),
            Err(_) => return inner(cx, k),
        }
    }
    stat.lookups.set(stat.lookups.get() + 1);
    // 1. an entry whose unit, bound values and reads all match this state
    let hit: Option<Vec<Value>> = cx.cur.with(|cv| {
        let t = table.borrow();
        let tm = match t.get(h0) {
            Some(Entry::Tmpl(tm)) if tm.unit == id && bound_eq(&tm.bound, cx, bound) => tm,
            _ => return None,
        };
        let mut h1 = h0;
        for loc in &tm.locs {
            h1 = sc_::mix(h1, sc_::word_at(cv, loc)?);
        }
        let leaf = match t.get(sc_::mix(h1, LEAF)) {
            Some(Entry::Leaf(l)) if l.unit == id && bound_eq(&l.bound, cx, bound) => l,
            _ => return None,
        };
        if !leaf.reads.iter().all(|(loc, v)| sc_::holds(cv, loc, v)) {
            return None;
        }
        // every successor is built before any is handed on: if a change cannot be applied, this is a miss
        let mut rows = Vec::with_capacity(leaf.succs.len() * nv);
        for s in &leaf.succs {
            for (i, w) in s.iter().enumerate() {
                rows.push(match w {
                    Write::Val(v) => v.clone(),
                    Write::Delta(ops) if ops.is_empty() => cv[i].clone(),
                    Write::Delta(ops) => apply_ops(cx, &cv[i], ops, n)?,
                });
            }
        }
        Some(rows)
    });
    let ev = cx.ev;
    if let Some(rows) = hit {
        stat.hits.set(stat.hits.get() + 1);
        {
            let mut t = table.borrow_mut();
            t.n.lookups += 1;
            t.n.hits += 1;
        }
        let mut rows = rows.into_iter();
        while rows.len() > 0 {
            for i in 0..nv {
                cx.nxt.set(i, rows.next().unwrap());
            }
            ev.n_assigned.set(nv as i64);
            let r = k();
            for i in 0..nv {
                cx.nxt.clear(i);
            }
            ev.n_assigned.set(0);
            r?;
        }
        return Ok(());
    }
    // 2. evaluate, noting what is read and how each variable gets its value
    for &s in clear {
        cx.f.clear(s);
    }
    {
        let mut rec = cx.rec.borrow_mut();
        rec.reads.clear();
        rec.bad = false;
        rec.succs.clear();
        rec.delta.clear();
        rec.delta.resize(nv, None);
    }
    let f0 = cx.fallbacks.get();
    cx.rec_on.set(true);
    let r = inner(cx, &mut || {
        cx.nxt.with(|nx| {
            let mut rec = cx.rec.borrow_mut();
            let mut ws = Vec::with_capacity(nv);
            for i in 0..nv {
                match rec.delta[i].clone() {
                    Some(ops) => ws.push(Write::Delta(ops)),
                    None => {
                        if i >= nx.len() || matches!(nx[i], Value::Undef) {
                            rec.bad = true;
                        } else {
                            ws.push(Write::Val(nx[i].clone()));
                        }
                    }
                }
            }
            rec.succs.push(ws);
        });
        k()
    });
    cx.rec_on.set(false);
    let mut t = table.borrow_mut();
    t.n.lookups += 1;
    let mut rec = cx.rec.borrow_mut();
    let mut stored = false;
    if r.is_ok() && !rec.bad && cx.fallbacks.get() == f0 {
        stored = cx.cur.with(|cv| {
            let bvals: Vec<Value> = bound.iter().map(|&s| cx.f.get(s)).collect();
            // the locations whose values pick the entry: those of earlier evaluations of this unit with
            // these bound values, and any new ones
            let mut locs: Vec<Loc> = match t.get(h0) {
                Some(Entry::Tmpl(tm)) if tm.unit == id && bound_eq(&tm.bound, cx, bound) => tm.locs.clone(),
                _ => vec![],
            };
            let had = locs.len();
            let fresh = !matches!(t.get(h0), Some(Entry::Tmpl(tm)) if tm.unit == id && bound_eq(&tm.bound, cx, bound));
            for (loc, _) in &rec.reads {
                if !locs.iter().any(|l| sc_::same_loc(l, loc)) {
                    locs.push(loc.clone());
                }
            }
            // A large value read whole makes a poor key: it rarely recurs, and comparing it costs as much
            // as the evaluation saved. Such an evaluation is not stored (and its unit soon backs off).
            if locs.len() > 24 || rec.reads.iter().any(|(_, v)| sc_::vsize(v) > 512) {
                return false;
            }
            let mut h1 = h0;
            for loc in &locs {
                match sc_::word_at(cv, loc) {
                    Some(w) => h1 = sc_::mix(h1, w),
                    None => return false,
                }
            }
            if fresh || locs.len() != had {
                t.put(h0, Entry::Tmpl(Tmpl { unit: id, bound: bvals.clone(), locs }));
            }
            let leaf = Leaf { unit: id, bound: bvals, reads: std::mem::take(&mut rec.reads), succs: std::mem::take(&mut rec.succs) };
            t.put(sc_::mix(h1, LEAF), Entry::Leaf(leaf));
            true
        });
    }
    if !stored {
        t.n.uncacheable += 1;
    } else {
        stat.stored.set(stat.stored.get() + 1);
    }
    r
}
fn with_clear(clear: Vec<PreOp>, body: CE) -> CE {
    if clear.is_empty() {
        return body;
    }
    Box::new(move |cx| {
        run_pre(&clear, cx);
        body(cx)
    })
}

/// The scope for the context a top-level action or invariant starts from: plain values and LET
/// definitions (an action that was split out of a LET). None when the context holds anything else, or a
/// LET definition that may reach an operator with an effect. Also the slots to clear at each evaluation.
fn root_scope(ctx: &C, c: &mut Comp, seen: &mut HashSet<usize>) -> Option<(Rc<Sc>, Vec<PreOp>)> {
    let mut nodes: Vec<&Rc<Ctx>> = vec![];
    let mut cur = ctx.as_ref();
    while let Some(node) = cur {
        if node.env || node.base.is_some() {
            return None;
        }
        nodes.push(node);
        cur = node.next.as_ref();
    }
    let mut sc = Rc::new(Sc { k: ScK::Root(ctx.clone()), next: None });
    let mut clear = vec![];
    for node in nodes.iter().rev() {
        let k = match &node.val {
            Bind::Val(v) if plain(v) => ScK::RootVal { name: node.name, v: v.clone() },
            Bind::LetLazy { d, .. } | Bind::LetOp(d) => {
                if impure(&d.body, seen) {
                    return None;
                }
                let cache = c.slot();
                c.cache_slots.push(cache);
                clear.push(PreOp::Clear(cache));
                ScK::Let { d, defs: &[], below: sc.clone(), head: node.let_head, cache, ce: RefCell::new(None), root: true }
            }
            _ => return None,
        };
        sc = push(&sc, k);
    }
    Some((sc, clear))
}

pub struct ActPlan {
    run: AE,
    frame: StateRef,
    use_: Usage,
}
pub struct PredPlan {
    run: CE,
    frame: StateRef,
    use_: Usage,
}
/// Compiled code that mostly hands over to the tree-walker costs more than the tree-walker alone (a
/// context is rebuilt for every fallback). Such a plan is switched off after a trial; the result is the
/// same either way.
#[derive(Default)]
struct Usage {
    runs: Cell<u32>,
    fallbacks: Cell<u64>,
    off: Cell<bool>,
}
impl Usage {
    #[inline]
    fn note(&self, fallbacks: u64) {
        let r = self.runs.get();
        if r < 512 {
            self.runs.set(r + 1);
            self.fallbacks.set(self.fallbacks.get() + fallbacks);
            if r + 1 == 512 && self.fallbacks.get() > 4 * 512 {
                self.off.set(true);
            }
        }
    }
}
#[derive(Default)]
pub struct Counters {
    /// actions / invariants evaluated by compiled code, by the tree-walker because they are not compiled,
    /// and by the tree-walker after the compiled attempt failed
    pub compiled: Cell<u64>,
    pub uncompiled: Cell<u64>,
    pub redone: Cell<u64>,
    /// fallback expressions evaluated inside compiled code
    pub fallbacks: Cell<u64>,
}
/// The definitions the invariants of one state have in common, evaluated once for that state however many
/// invariants refer to them (`Checker::eval_invariants` runs the invariants of a state as one pass over a
/// cleared table).
///
/// Only a definition with no parameters is memoised, and only while an invariant is compiled: such a
/// definition reads nothing but the state (an invariant is compiled only when it is pure and of level at
/// most 1, so nothing it reads is primed), and the call in one invariant is the same call as in another.
/// A value that is not `plain` is not kept, so a value holding a closure or a LET operator — whose context
/// belongs to the plan that built it — is never handed to another plan.
#[derive(Default)]
pub struct InvMemo {
    /// the value of each memoised definition, by slot; None until it is evaluated in this state
    slots: RefCell<Vec<Option<Value>>>,
    /// the slot of each memoised definition, by the address of the definition
    defs: RefCell<HashMap<usize, usize>>,
}

impl InvMemo {
    /// The slot of a definition: the same definition gets the same slot in every invariant.
    fn slot(&self, def: usize) -> usize {
        let mut defs = self.defs.borrow_mut();
        if let Some(s) = defs.get(&def) {
            return *s;
        }
        let s = defs.len();
        defs.insert(def, s);
        self.slots.borrow_mut().push(None);
        s
    }
    fn get(&self, slot: usize) -> Option<Value> {
        self.slots.borrow().get(slot).cloned().flatten()
    }
    fn put(&self, slot: usize, v: &Value) {
        if !plain(v) {
            return;
        }
        if let Some(c) = self.slots.borrow_mut().get_mut(slot) {
            *c = Some(v.clone());
        }
    }
    /// Forgets every value: called when the invariant pass of a new state begins.
    pub fn clear(&self) {
        for c in self.slots.borrow_mut().iter_mut() {
            *c = None;
        }
    }
}

pub struct Plans {
    pub actions: Vec<Option<ActPlan>>,
    pub invariants: Vec<Option<PredPlan>>,
    pub n: Counters,
    blank: StateRef,
    /// the definitions the invariants of a state have in common
    inv_memo: Option<Rc<InvMemo>>,
    /// the step cache, when it is on
    cache: Option<RefCell<Table>>,
    rec_on: Cell<bool>,
    rec: RefCell<Rec>,
    units: Vec<Rc<UnitStat>>,
    cache_always: bool,
    meas: Meas,
}

/// The step cache is on with the compiled evaluator; EVERYSTATE_STEP_CACHE=off turns it off. (`on` and
/// `always` ask for it even with EVERYSTATE_EVAL=tree; `always` gives it to every unit, for testing.)
/// In WebAssembly it is off: there is no clock to measure whether it pays, so no unit would ever keep it.
pub fn cache_enabled() -> bool {
    if cfg!(target_arch = "wasm32") {
        return false;
    }
    match std::env::var("EVERYSTATE_STEP_CACHE").as_deref() {
        Ok("off") => false,
        Ok("on") | Ok("always") => true,
        _ => !matches!(std::env::var("EVERYSTATE_EVAL").as_deref(), Ok("tree")),
    }
}
fn cache_budget() -> usize {
    let mb: f64 = std::env::var("EVERYSTATE_STEP_CACHE_MB").ok().and_then(|v| v.parse().ok()).unwrap_or(32.0);
    (mb.max(0.001) * 1024.0 * 1024.0) as usize
}

/// The compiled evaluator is the default; EVERYSTATE_EVAL=tree selects the tree-walker alone.
pub fn enabled() -> bool {
    !matches!(std::env::var("EVERYSTATE_EVAL").as_deref(), Ok("tree")) || cache_enabled()
}

pub fn compile(model: &crate::model::Model) -> Plans {
    let mut cache_on = cache_enabled();
    let mut plan_id: u32 = 0;
    let mut units = vec![];
    let mut actions = vec![];
    for a in &model.actions {
        let mut seen = HashSet::new();
        let mut c = Comp::new(cache_on, plan_id);
        plan_id += 1;
        let root = if impure(a.e, &mut seen) { None } else { root_scope(&a.ctx, &mut c, &mut seen) };
        let (root, clear) = match root {
            Some(x) => x,
            None => {
                if std::env::var_os("EVERYSTATE_EVAL_DEBUG").is_some() {
                    eprintln!("action {}{} is not compiled (an operator with an effect, or a context that is not plain values and LET definitions)", a.name, a.params);
                }
                actions.push(None);
                continue;
            }
        };
        c.top = true;
        let body = c.act(a.e, &root);
        units.append(&mut c.unit_stats);
        let run: AE = if clear.is_empty() {
            body
        } else {
            Box::new(move |cx, k| {
                run_pre(&clear, cx);
                body(cx, k)
            })
        };
        actions.push(Some(ActPlan { run, frame: StateData::blank(c.nslots.max(1)), use_: Usage::default() }));
    }
    let with_cache = cache_on;
    cache_on = false; // (invariants are not cached)
    // the definitions the invariants of a state have in common (InvMemo)
    let inv_memo = if model.invariants.is_empty() { None } else { Some(Rc::new(InvMemo::default())) };
    let mut invariants = vec![];
    for p in &model.invariants {
        let mut seen = HashSet::new();
        let mut c = Comp::new(cache_on, plan_id);
        plan_id += 1;
        c.inv_memo = inv_memo.clone();
        let root = if impure(p.e, &mut seen) || level_of(p.e) > 1 { None } else { root_scope(&p.ctx, &mut c, &mut seen) };
        let (root, clear) = match root {
            Some(x) => x,
            None => {
                invariants.push(None);
                continue;
            }
        };
        let run = with_clear(clear, c.expr(p.e, &root));
        invariants.push(Some(PredPlan { run, frame: StateData::blank(c.nslots.max(1)), use_: Usage::default() }));
    }
    Plans {
        actions,
        invariants,
        n: Counters::default(),
        blank: StateData::blank(model.vars.len()),
        inv_memo,
        cache: if with_cache { Some(RefCell::new(Table::new(cache_budget()))) } else { None },
        rec_on: Cell::new(false),
        rec: RefCell::new(Rec::default()),
        units,
        cache_always: matches!(std::env::var("EVERYSTATE_STEP_CACHE").as_deref(), Ok("always")),
        meas: Meas::new(),
    }
}

impl Plans {
    /// Runs the compiled form of action `ai` (the evaluator's current and next state are set as for
    /// `enumerate`). None: the action is not compiled. Some(Err): the attempt failed and must be redone
    /// by the tree-walker after discarding what it produced.
    pub fn run_action(&self, ev: &Evaluator, ai: usize, cur: &StateData, nxt: &StateData, nv: usize, k: &mut dyn FnMut() -> R<()>) -> Option<R<()>> {
        let p = match &self.actions[ai] {
            Some(p) if !p.use_.off.get() => p,
            _ => {
                self.n.uncompiled.set(self.n.uncompiled.get() + 1);
                return None;
            }
        };
        let cx = Cx { ev, f: &p.frame, cur, nxt, nv: nv as i64, fallbacks: &self.n.fallbacks, cache: self.cache.as_ref(), rec_on: &self.rec_on, rec: &self.rec, cache_always: self.cache_always, meas: &self.meas };
        let f0 = self.n.fallbacks.get();
        let r = (p.run)(&cx, k);
        self.rec_on.set(false);
        p.use_.note(self.n.fallbacks.get() - f0);
        if r.is_err() {
            self.n.redone.set(self.n.redone.get() + 1);
        } else {
            self.n.compiled.set(self.n.compiled.get() + 1);
        }
        Some(r)
    }
    /// Starts the invariant pass of a state: the definitions the invariants of the previous state have in
    /// common are forgotten (see `InvMemo` and `Checker::eval_invariants`).
    pub fn begin_invariants(&self) {
        if let Some(m) = &self.inv_memo {
            m.clear();
        }
    }
    /// The value of invariant `i` in `s` (the evaluator's current state), or None for the tree-walker to decide.
    pub fn run_invariant(&self, ev: &Evaluator, i: usize, s: &StateData, nv: usize) -> Option<bool> {
        let p = match &self.invariants[i] {
            Some(p) if !p.use_.off.get() => p,
            _ => {
                self.n.uncompiled.set(self.n.uncompiled.get() + 1);
                return None;
            }
        };
        let cx = Cx { ev, f: &p.frame, cur: s, nxt: &self.blank, nv: nv as i64, fallbacks: &self.n.fallbacks, cache: None, rec_on: &self.rec_on, rec: &self.rec, cache_always: self.cache_always, meas: &self.meas };
        let f0 = self.n.fallbacks.get();
        let r = (p.run)(&cx);
        p.use_.note(self.n.fallbacks.get() - f0);
        match r {
            Ok(Value::Bool(b)) => {
                self.n.compiled.set(self.n.compiled.get() + 1);
                Some(b)
            }
            _ => {
                self.n.redone.set(self.n.redone.get() + 1);
                None
            }
        }
    }
    /// To be called before each state is expanded (the step cache measures the time between such calls).
    #[inline]
    pub fn tick(&self) {
        self.meas.tick();
    }
    pub fn report(&self) -> String {
        let c = &self.n;
        let mut cache = String::new();
        if let Some(t) = &self.cache {
            let t = t.borrow();
            let off = self.units.iter().filter(|u| u.off.get()).count();
            cache = format!(
                "step cache: budget {:.1} MB, in use {:.1} MB (peak {:.1} MB); {} units, {} measured as not paying; {} lookups, {} hits ({:.2}%), {} stored, {} replaced, {} not stored for size, {} evaluations not cacheable\n",
                t.budget as f64 / 1048576.0,
                t.used as f64 / 1048576.0,
                t.peak as f64 / 1048576.0,
                self.units.len(),
                off,
                t.n.lookups,
                t.n.hits,
                100.0 * t.n.hits as f64 / t.n.lookups.max(1) as f64,
                t.n.stored,
                t.n.replaced,
                t.n.too_big,
                t.n.uncacheable
            );
            if std::env::var_os("EVERYSTATE_EVAL_DEBUG").is_some() {
                for u in &self.units {
                    cache += &format!(
                        "  unit at line {} col {}: {} lookups, {} hits{}; last verdict on {:.0} ns per state without against {:.0} ns with the cache ({} states)\n",
                        u.loc[0],
                        u.loc[1],
                        u.lookups.get(),
                        u.hits.get(),
                        if u.off.get() { " (does not pay)" } else { "" },
                        u.last.get().0,
                        u.last.get().1,
                        u.trials.get()
                    );
                }
            }
        }
        cache + &format!(
            "compiled evaluator: {} of {} actions and {} of {} invariants compiled; evaluations: {} compiled, {} by the tree-walker (not compiled), {} redone by the tree-walker after a failed attempt; {} fallback expressions evaluated inside compiled code\n",
            self.actions.iter().filter(|a| a.is_some()).count(),
            self.actions.len(),
            self.invariants.iter().filter(|a| a.is_some()).count(),
            self.invariants.len(),
            c.compiled.get(),
            c.uncompiled.get(),
            c.redone.get(),
            c.fallbacks.get()
        )
    }
}
