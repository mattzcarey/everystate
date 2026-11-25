//! Runtime values. Functions are kept in canonical form: domain 1..n => Tuple, non-empty all-string
//! domain => Record, anything else => Fcn. Sets are an explicit sorted vector or a symbolic set.
use crate::ast::N;
use crate::eval::{ev, Closure, Ctx, DefRef, Lazy, LazyFcn, StateRef};
use crate::intern::*;
use std::cell::{Cell, OnceCell};
use std::cmp::Ordering;
use std::rc::Rc;

#[derive(Clone)]
pub enum Value {
    Undef,
    Bool(bool),
    Int(i64),
    Str(StrId),
    Model(StrId),
    Tuple(Rc<TupleV>),
    Record(Rc<RecordV>),
    Fcn(Rc<FcnV>),
    Set(Rc<SetV>),
    Closure(Rc<Closure>),
    DefRef(Rc<DefRef>),
    LazyFcn(Rc<LazyFcn>),
    Thunk(Rc<Lazy>),
}

/// A sequence / tuple. `h` caches the fingerprint hash of the value (0 = not computed yet).
pub struct TupleV {
    pub e: Vec<Value>,
    pub h: Cell<u64>,
}
impl TupleV {
    #[inline]
    pub fn rc(e: Vec<Value>) -> Rc<TupleV> {
        Rc::new(TupleV { e, h: Cell::new(0) })
    }
}
impl std::ops::Deref for TupleV {
    type Target = Vec<Value>;
    #[inline]
    fn deref(&self) -> &Vec<Value> {
        &self.e
    }
}

pub struct RecordV {
    pub names: Rc<Vec<StrId>>, // sorted by string id
    pub vals: Vec<Value>,
    pub h: Cell<u64>,
}
impl RecordV {
    #[inline]
    pub fn new(names: Rc<Vec<StrId>>, vals: Vec<Value>) -> RecordV {
        RecordV { names, vals, h: Cell::new(0) }
    }
    #[inline]
    pub fn get(&self, name: StrId) -> Option<&Value> {
        // `names` is sorted by string id (see the field), so a binary search finds the same index with
        // log2(k) comparisons instead of scanning up to k of them.
        let (mut lo, mut hi) = (0usize, self.names.len());
        while lo < hi {
            let mid = (lo + hi) / 2;
            match self.names[mid].cmp(&name) {
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
                std::cmp::Ordering::Equal => return Some(&self.vals[mid]),
            }
        }
        None
    }
}
pub struct FcnV {
    pub dom: Rc<Vec<Value>>, // sorted, deduplicated
    pub vals: Vec<Value>,
    pub h: Cell<u64>,
}
impl FcnV {
    #[inline]
    pub fn new(dom: Rc<Vec<Value>>, vals: Vec<Value>) -> FcnV {
        FcnV { dom, vals, h: Cell::new(0) }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Inf {
    Nat,
    Int,
    Real,
    String,
}

pub struct FilterSet {
    pub s: Rc<SetV>,
    pub node: N, // the SetFilter node
    pub ctx: Option<Rc<Ctx>>,
    pub cur: StateRef,
    pub nxt: Option<StateRef>,
}

pub enum SetK {
    Enum(Vec<Value>),
    Interval(i64, i64),
    Subset(Rc<SetV>),
    FcnSet(Rc<SetV>, Rc<SetV>),
    RecSet(Rc<Vec<StrId>>, Vec<Rc<SetV>>),
    Cross(Vec<Rc<SetV>>),
    Seq(Rc<SetV>),
    Inf(Inf),
    Any,
    KSubset(i64, Rc<SetV>),
    // TLC's lazy SetCup / SetCap / SetDiff / SetPred values
    Cup(Rc<SetV>, Rc<SetV>),
    Cap(Rc<SetV>, Rc<SetV>),
    Diff(Rc<SetV>, Rc<SetV>),
    Union(Vec<Rc<SetV>>),
    Filter(Box<FilterSet>),
}

pub struct SetV {
    pub k: SetK,
    cache: OnceCell<Vec<Value>>,
    shape: OnceCell<FcnShape>,
    h: Cell<u64>,
}

thread_local! {
    static EMPTY_TUPLE: Value = Value::Tuple(TupleV::rc(Vec::new()));
    static EMPTY_SET: Rc<SetV> = Rc::new(SetV::new(SetK::Enum(Vec::new())));
}
pub fn empty_tuple() -> Value {
    EMPTY_TUPLE.with(|v| v.clone())
}
pub fn empty_set() -> Rc<SetV> {
    EMPTY_SET.with(|v| v.clone())
}

impl SetV {
    pub fn new(k: SetK) -> SetV {
        SetV { k, cache: OnceCell::new(), shape: OnceCell::new(), h: Cell::new(0) }
    }
    pub fn of(elems: Vec<Value>) -> Value {
        Value::Set(Rc::new(SetV::new(SetK::Enum(elems))))
    }
    /// The canonical shape of functions whose domain is this set (cached: it is shared by all such functions).
    pub fn fcn_shape(&self) -> R<&FcnShape> {
        if let Some(s) = self.shape.get() {
            return Ok(s);
        }
        let sh = FcnShape::of(self.elems()?);
        let _ = self.shape.set(sh);
        Ok(self.shape.get().unwrap())
    }
    #[inline]
    pub fn reducible(&self) -> bool {
        matches!(self.k, SetK::Enum(_) | SetK::Interval(..))
    }
    pub fn enumerable(&self) -> bool {
        match &self.k {
            SetK::Enum(_) | SetK::Interval(..) => true,
            SetK::Subset(b) => b.enumerable(),
            SetK::FcnSet(d, r) => d.enumerable() && r.enumerable(),
            SetK::RecSet(_, s) | SetK::Cross(s) => s.iter().all(|x| x.enumerable()),
            SetK::Seq(_) | SetK::Inf(_) | SetK::Any => false,
            SetK::KSubset(k, _) => *k == 0, // kSubset(0, S) = {{}} whatever S is
            SetK::Cup(a, b) => a.enumerable() && b.enumerable(),
            SetK::Cap(a, b) => a.enumerable() || b.enumerable(),
            SetK::Diff(a, _) => a.enumerable(),
            SetK::Union(ss) => ss.iter().all(|x| x.enumerable()),
            SetK::Filter(f) => f.s.enumerable(),
        }
    }
    pub fn size(&self) -> R<i64> {
        Ok(match &self.k {
            SetK::Enum(e) => e.len() as i64,
            SetK::Interval(lo, hi) => (hi - lo + 1).max(0),
            SetK::Subset(b) => {
                let n = b.size()?;
                if n >= 62 { i64::MAX } else { 1i64 << n }
            }
            SetK::FcnSet(d, r) => {
                let (r, d) = (r.size()?, d.size()?);
                r.checked_pow(d.min(u32::MAX as i64) as u32).unwrap_or(i64::MAX)
            }
            SetK::RecSet(_, s) | SetK::Cross(s) => {
                let mut n: i64 = 1;
                for x in s {
                    n = n.saturating_mul(x.size()?);
                }
                n
            }
            SetK::KSubset(k, b) if *k > 0 && b.enumerable() => {
                // n choose k, through the short side of Pascal's triangle
                let n = b.size()? as i128;
                let k = (*k as i128).min(n - *k as i128);
                if k < 0 {
                    return Ok(0);
                }
                let mut c: i128 = 1;
                for i in 0..k {
                    c = c * (n - i) / (i + 1);
                    if c > i64::MAX as i128 {
                        return Ok(i64::MAX);
                    }
                }
                c as i64
            }
            _ => self.elems()?.len() as i64,
        })
    }
    fn is_derived(&self) -> bool {
        matches!(self.k, SetK::Cup(..) | SetK::Cap(..) | SetK::Diff(..) | SetK::Union(_) | SetK::Filter(_))
    }
    pub fn contains(&self, v: &Value) -> R<bool> {
        match &self.k {
            SetK::Enum(e) => Ok(bsearch(e, v)?.is_some()),
            SetK::Interval(lo, hi) => match v {
                Value::Int(i) => Ok(i >= lo && i <= hi),
                _ => {
                    if hi < lo || matches!(v, Value::Model(_)) {
                        Ok(false)
                    } else {
                        eval_err(format!("Attempted to check if the value:\n{}\nis in the integer interval {}", fmt(v), fmt_set(self)))
                    }
                }
            },
            SetK::Subset(base) => {
                let s = match v {
                    Value::Set(s) => s,
                    _ => return eval_err(format!("Attempted to check if the non-set value:\n{}\nis in {}", fmt(v), fmt_set(self))),
                };
                if !s.enumerable() {
                    return eval_err("Attempted to check if a non-enumerable set is an element of SUBSET".into());
                }
                for x in s.elems()? {
                    if !base.contains(x)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            SetK::FcnSet(dom, rng) => {
                // the common shape, a function whose domain is literally the set's (scalars in the same
                // order), without building the domain as a set
                let same_dom = match (v, &dom.k) {
                    (Value::Fcn(f), SetK::Enum(e)) => f.dom.len() == e.len() && f.dom.iter().zip(e.iter()).all(|(x, y)| scalar_cmp(x, y) == Some(Ordering::Equal)),
                    (Value::Tuple(t), SetK::Interval(1, hi)) => t.len() as i64 == *hi,
                    _ => false,
                };
                if same_dom {
                    for x in fcn_values(v)? {
                        if !rng.contains(x)? {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                let d = match domain_of(v) {
                    None => {
                        return match v {
                            Value::Model(m) => {
                                if model_type(*m).is_none() {
                                    Ok(false)
                                } else {
                                    eval_err(format!("Attempted to check if the typed model value {} is an element of\n{}", str_of(*m), fmt_set(self)))
                                }
                            }
                            Value::Set(_) | Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Undef => {
                                eval_err(format!("Attempted to check if \n{}\nwhich is not a TLC function value, is in the set of functions:\n{}", fmt(v), fmt_set(self)))
                            }
                            _ => Ok(false),
                        };
                    }
                    Some(d) => d,
                };
                if !set_eq(&d, dom)? {
                    return Ok(false);
                }
                for x in fcn_values(v)? {
                    if !rng.contains(x)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            SetK::RecSet(names, sets) => {
                let r = match v {
                    Value::Record(r) if r.names.len() == names.len() => r,
                    _ => return Ok(false),
                };
                for i in 0..names.len() {
                    if r.names[i] != names[i] || !sets[i].contains(&r.vals[i])? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            SetK::Cross(sets) => {
                let t = match v {
                    Value::Tuple(t) if t.len() == sets.len() => t,
                    _ => return Ok(false),
                };
                for i in 0..sets.len() {
                    if !sets[i].contains(&t[i])? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            SetK::Seq(base) => {
                let t = match v {
                    Value::Tuple(t) => t,
                    _ => return Ok(false),
                };
                for x in t.iter() {
                    if !base.contains(x)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            SetK::Inf(kind) => {
                let ok = match (kind, v) {
                    (Inf::Nat, Value::Int(i)) => *i >= 0,
                    (Inf::Int, Value::Int(_)) | (Inf::Real, Value::Int(_)) | (Inf::String, Value::Str(_)) => true,
                    (_, Value::Model(_)) => false,
                    _ => return eval_err(format!("Attempted to check if the value:\n{}\nis in {}.", fmt(v), fmt_set(self))),
                };
                Ok(ok)
            }
            SetK::Any => Ok(true),
            SetK::KSubset(k, base) => {
                let s = match v {
                    Value::Set(s) => s,
                    _ => return eval_err(format!("Attempted to check if the non-set value:\n{}\nis in {}", fmt(v), fmt_set(self))),
                };
                if !s.enumerable() {
                    return Ok(false);
                }
                let e = s.elems()?;
                if e.len() as i64 != *k {
                    return Ok(false);
                }
                for x in e {
                    if !base.contains(x)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => {
                if let Some(c) = self.cache.get() {
                    return Ok(bsearch(c, v)?.is_some());
                }
                match &self.k {
                    SetK::Cup(a, b) => Ok(a.contains(v)? || b.contains(v)?),
                    SetK::Cap(a, b) => Ok(a.contains(v)? && b.contains(v)?),
                    SetK::Diff(a, b) => Ok(a.contains(v)? && !b.contains(v)?),
                    SetK::Union(ss) => {
                        for x in ss {
                            if x.contains(v)? {
                                return Ok(true);
                            }
                        }
                        Ok(false)
                    }
                    SetK::Filter(f) => Ok(f.s.contains(v)? && ev().filter_test(f, v)?),
                    _ => unreachable!(),
                }
            }
        }
    }

    /// Normalized (sorted, duplicate-free) elements; fails if the set is not enumerable.
    pub fn elems(&self) -> R<&[Value]> {
        if let SetK::Enum(e) = &self.k {
            return Ok(e);
        }
        if let Some(c) = self.cache.get() {
            return Ok(c);
        }
        let v = self.compute()?;
        let _ = self.cache.set(v);
        Ok(self.cache.get().unwrap())
    }

    fn compute(&self) -> R<Vec<Value>> {
        match &self.k {
            SetK::Enum(_) => unreachable!(),
            SetK::Interval(lo, hi) => Ok((*lo..=*hi).map(Value::Int).collect()),
            SetK::Subset(base) => {
                let b = base.elems()?;
                let n = b.len();
                if n > 26 {
                    return eval_err(format!("Attempted to enumerate SUBSET of a set with {} elements; this is too large.", n));
                }
                let mut out: Vec<Value> = Vec::with_capacity(1usize << n);
                // by size, then lexicographic: this is the normalized set order
                let mut idx: Vec<usize> = Vec::new();
                fn rec(b: &[Value], n: usize, start: usize, k: usize, idx: &mut Vec<usize>, out: &mut Vec<Value>) {
                    if k == 0 {
                        out.push(SetV::of(idx.iter().map(|&i| b[i].clone()).collect()));
                        return;
                    }
                    let mut i = start;
                    while i + k <= n {
                        idx.push(i);
                        rec(b, n, i + 1, k - 1, idx, out);
                        idx.pop();
                        i += 1;
                    }
                }
                for k in 0..=n {
                    rec(b, n, 0, k, &mut idx, &mut out);
                }
                Ok(out)
            }
            SetK::FcnSet(dom, rng) => {
                let d = dom.elems()?;
                let r = rng.elems()?;
                let n = d.len();
                if r.is_empty() {
                    return Ok(if n == 0 { vec![empty_tuple()] } else { vec![] });
                }
                let total = (r.len() as f64).powi(n as i32);
                if total > 5e7 {
                    return eval_err(format!("Attempted to enumerate a set of functions with {} elements; this is too large.", total));
                }
                let mut out = Vec::with_capacity(total as usize);
                let mut idx = vec![0usize; n];
                let shape = dom.fcn_shape()?;
                loop {
                    out.push(shape.make(idx.iter().map(|&i| r[i].clone()).collect()));
                    let mut k = n as isize - 1;
                    while k >= 0 {
                        idx[k as usize] += 1;
                        if idx[k as usize] == r.len() {
                            idx[k as usize] = 0;
                            k -= 1;
                        } else {
                            break;
                        }
                    }
                    if k < 0 {
                        break;
                    }
                }
                Ok(out) // odometer order over normalized components is already the normalized order
            }
            SetK::RecSet(names, sets) => {
                let mut es = Vec::with_capacity(sets.len());
                for s in sets {
                    es.push(s.elems()?);
                }
                let mut out = Vec::new();
                if es.iter().any(|e| e.is_empty()) {
                    return Ok(out);
                }
                let n = es.len();
                let mut idx = vec![0usize; n];
                loop {
                    out.push(Value::Record(Rc::new(RecordV::new(names.clone(), idx.iter().enumerate().map(|(k, &i)| es[k][i].clone()).collect()))));
                    let mut k = n as isize - 1;
                    while k >= 0 {
                        idx[k as usize] += 1;
                        if idx[k as usize] == es[k as usize].len() {
                            idx[k as usize] = 0;
                            k -= 1;
                        } else {
                            break;
                        }
                    }
                    if k < 0 {
                        break;
                    }
                }
                Ok(out) // odometer order over normalized components is already the normalized order
            }
            SetK::Cross(sets) => {
                let mut es = Vec::with_capacity(sets.len());
                for s in sets {
                    es.push(s.elems()?);
                }
                let mut out = Vec::new();
                if es.iter().any(|e| e.is_empty()) {
                    return Ok(out);
                }
                let n = es.len();
                let mut idx = vec![0usize; n];
                loop {
                    out.push(Value::Tuple(TupleV::rc(idx.iter().enumerate().map(|(k, &i)| es[k][i].clone()).collect())));
                    let mut k = n as isize - 1;
                    while k >= 0 {
                        idx[k as usize] += 1;
                        if idx[k as usize] == es[k as usize].len() {
                            idx[k as usize] = 0;
                            k -= 1;
                        } else {
                            break;
                        }
                    }
                    if k < 0 {
                        break;
                    }
                }
                Ok(out)
            }
            SetK::Seq(base) => eval_err(format!("Attempted to enumerate the non-enumerable set Seq({}).", fmt_set(base))),
            SetK::Inf(_) => eval_err(format!("Attempted to enumerate the non-enumerable set {}.", fmt_set(self))),
            SetK::KSubset(0, _) => Ok(vec![Value::Set(empty_set())]),
            SetK::Any | SetK::KSubset(..) => eval_err(format!("Attempted to enumerate a non-enumerable set ({}).", fmt_set(self))),
            SetK::Cup(a, b) => {
                if !(a.enumerable() && b.enumerable()) {
                    return self.not_enum();
                }
                let mut out = a.elems()?.to_vec();
                out.extend_from_slice(b.elems()?);
                sort_dedup(out)
            }
            SetK::Cap(a, b) => {
                let (x, y) = if a.enumerable() {
                    (a, b)
                } else if b.enumerable() {
                    (b, a)
                } else {
                    return self.not_enum();
                };
                let mut out = Vec::new();
                for e in x.elems()? {
                    if y.contains(e)? {
                        out.push(e.clone());
                    }
                }
                sort_dedup(out)
            }
            SetK::Diff(a, b) => {
                if !a.enumerable() {
                    return self.not_enum();
                }
                let mut out = Vec::new();
                for e in a.elems()? {
                    if !b.contains(e)? {
                        out.push(e.clone());
                    }
                }
                sort_dedup(out)
            }
            SetK::Union(ss) => {
                if !self.enumerable() {
                    return self.not_enum();
                }
                let mut out = Vec::new();
                for x in ss {
                    out.extend_from_slice(x.elems()?);
                }
                sort_dedup(out)
            }
            SetK::Filter(f) => {
                if !f.s.enumerable() {
                    return self.not_enum();
                }
                sort_dedup(ev().filter_elems(f)?)
            }
        }
    }
    fn not_enum<X>(&self) -> R<X> {
        eval_err(format!("Attempted to enumerate a non-enumerable set ({}).", self.desc()))
    }
    fn desc(&self) -> String {
        match &self.k {
            SetK::Cup(a, b) => format!("{} \\cup {}", fmt_set(a), fmt_set(b)),
            SetK::Cap(a, b) => format!("{} \\cap {}", fmt_set(a), fmt_set(b)),
            SetK::Diff(a, b) => format!("{} \\ {}", fmt_set(a), fmt_set(b)),
            SetK::Filter(f) => format!("{{x \\in {} : ...}}", fmt_set(&f.s)),
            SetK::Union(_) => "UNION ...".to_string(),
            _ => fmt_set(self),
        }
    }
}

// ---- kinds, comparison, equality ----
fn kind_name(v: &Value) -> &'static str {
    match v {
        Value::Bool(_) => "boolean",
        Value::Int(_) => "integer",
        Value::Str(_) => "string",
        Value::Model(_) => "model value",
        Value::Tuple(_) => "tuple",
        Value::Record(_) => "record",
        Value::Fcn(_) => "function",
        Value::Set(_) => "set",
        _ => "operator",
    }
}
#[cold]
fn cmp_fail<X>(a: &Value, b: &Value) -> R<X> {
    eval_err(format!("Attempted to compare the {} {} with the {} {}", kind_name(a), fmt(a), kind_name(b), fmt(b)))
}
#[cold]
fn eq_fail<X>(a: &Value, b: &Value) -> R<X> {
    eval_err(format!("Attempted to check equality of the {} {} with the {} {}", kind_name(a), fmt(a), kind_name(b), fmt(b)))
}


fn model_cmp(m: StrId, o: &Value) -> R<Ordering> {
    if let Value::Model(x) = o {
        if m != *x && any_typed() {
            if let (Some(t1), Some(t2)) = (model_type(m), model_type(*x)) {
                if t1 != t2 {
                    return eval_err(format!("Attempted to compare the differently-typed model values {} and {}", str_of(m), str_of(*x)));
                }
            }
        }
        return Ok(m.0.cmp(&x.0));
    }
    if any_typed() && model_type(m).is_some() {
        return eval_err(format!("Attempted to compare the typed model value {} with the non-model value\n{}", str_of(m), fmt(o)));
    }
    Ok(Ordering::Less) // an untyped model value is smaller than every non-model value
}

/// Total order used for set normalization. Mirrors TLC's compareTo.
pub fn compare(a: &Value, b: &Value) -> R<Ordering> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Ok(x.cmp(y)),
        (Value::Str(x), Value::Str(y)) => Ok(x.0.cmp(&y.0)),
        (Value::Bool(x), Value::Bool(y)) => Ok(x.cmp(y)),
        (Value::Model(m), _) => model_cmp(*m, b),
        (_, Value::Model(m)) => Ok(model_cmp(*m, a)?.reverse()),
        (Value::Int(_), _) | (Value::Str(_), _) | (Value::Bool(_), _) => cmp_fail(a, b),
        (Value::Set(x), Value::Set(y)) => {
            if let (SetK::Inf(i), SetK::Inf(j)) = (&x.k, &y.k) {
                return Ok((*i as u8).cmp(&(*j as u8)));
            }
            if matches!(x.k, SetK::Inf(_)) || matches!(y.k, SetK::Inf(_)) {
                let (u, o) = if matches!(x.k, SetK::Inf(_)) { (x, y) } else { (y, x) };
                return eval_err(format!("Attempted to compare overridden value {} with non-overridden value:\n{}", fmt_set(u), fmt_set(o)));
            }
            if Rc::ptr_eq(x, y) {
                return Ok(Ordering::Equal);
            }
            // TLC (KSubsetValue.compareTo): k-subsets of the same infinite base are ordered by k
            if let (SetK::KSubset(k1, b1), SetK::KSubset(k2, b2)) = (&x.k, &y.k) {
                if let (SetK::Inf(i), SetK::Inf(j)) = (&b1.k, &b2.k) {
                    if i == j && k1 != k2 {
                        return Ok(k1.cmp(k2));
                    }
                }
            }
            let (x, y) = (x.elems()?, y.elems()?);
            if x.len() != y.len() {
                return Ok(x.len().cmp(&y.len()));
            }
            for i in 0..x.len() {
                let c = compare(&x[i], &y[i])?;
                if c != Ordering::Equal {
                    return Ok(c);
                }
            }
            Ok(Ordering::Equal)
        }
        (Value::Set(_), _) => cmp_fail(a, b),
        (Value::Tuple(x), Value::Tuple(y)) => {
            if Rc::ptr_eq(x, y) {
                return Ok(Ordering::Equal);
            }
            if x.len() != y.len() {
                return Ok(x.len().cmp(&y.len()));
            }
            for i in 0..x.len() {
                let c = match scalar_cmp(&x[i], &y[i]) {
                    Some(c) => c,
                    None => compare(&x[i], &y[i])?,
                };
                if c != Ordering::Equal {
                    return Ok(c);
                }
            }
            Ok(Ordering::Equal)
        }
        (Value::Record(x), Value::Record(y)) => {
            if Rc::ptr_eq(x, y) {
                return Ok(Ordering::Equal);
            }
            let n = x.names.len();
            if n != y.names.len() {
                return Ok(n.cmp(&y.names.len()));
            }
            if !Rc::ptr_eq(&x.names, &y.names) {
                for i in 0..n {
                    if x.names[i] != y.names[i] {
                        return Ok(x.names[i].0.cmp(&y.names[i].0));
                    }
                }
            }
            for i in 0..n {
                let c = match scalar_cmp(&x.vals[i], &y.vals[i]) {
                    Some(c) => c,
                    None => compare(&x.vals[i], &y.vals[i])?,
                };
                if c != Ordering::Equal {
                    return Ok(c);
                }
            }
            Ok(Ordering::Equal)
        }
        (Value::Tuple(_) | Value::Record(_) | Value::Fcn(_), Value::Tuple(_) | Value::Record(_) | Value::Fcn(_)) => fcn_cmp(a, b),
        _ => cmp_fail(a, b),
    }
}

fn fcn_cmp(a: &Value, b: &Value) -> R<Ordering> {
    let (da, db) = (domain_elems(a)?, domain_elems(b)?);
    if da.len() != db.len() {
        return Ok(da.len().cmp(&db.len()));
    }
    let (va, vb) = (fcn_values(a)?, fcn_values(b)?);
    for i in 0..da.len() {
        let c = compare(&da[i], &db[i])?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    for i in 0..da.len() {
        let c = compare(&va[i], &vb[i])?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}

fn model_eq(m: StrId, o: &Value) -> R<bool> {
    if let Value::Model(x) = o {
        if m == *x {
            return Ok(true);
        }
        if let (Some(t1), Some(t2)) = (model_type(m), model_type(*x)) {
            if t1 != t2 {
                return eval_err(format!("Attempted to check equality of the differently-typed model values {} and {}", str_of(m), str_of(*x)));
            }
        }
        return Ok(false);
    }
    if model_type(m).is_some() {
        return eval_err(format!("Attempted to check equality of typed model value {} and non-model value\n{}", str_of(m), fmt(o)));
    }
    Ok(false)
}

pub fn val_eq(a: &Value, b: &Value) -> R<bool> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Ok(x == y),
        (Value::Str(x), Value::Str(y)) => Ok(x == y),
        (Value::Bool(x), Value::Bool(y)) => Ok(x == y),
        (Value::Model(m), _) => model_eq(*m, b),
        (_, Value::Model(m)) => model_eq(*m, a),
        (Value::Int(_) | Value::Str(_) | Value::Bool(_) | Value::Undef, _) => eq_fail(a, b),
        (_, Value::Int(_) | Value::Str(_) | Value::Bool(_) | Value::Undef) => eq_fail(a, b),
        (Value::Set(x), Value::Set(y)) => set_eq(x, y),
        (Value::Set(_), _) => eq_fail(a, b),
        (Value::Tuple(x), Value::Tuple(y)) => {
            if Rc::ptr_eq(x, y) {
                return Ok(true);
            }
            if x.len() != y.len() {
                return Ok(false);
            }
            for i in 0..x.len() {
                if !val_eq(&x[i], &y[i])? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Value::Record(x), Value::Record(y)) => {
            if Rc::ptr_eq(x, y) {
                return Ok(true);
            }
            let n = x.names.len();
            if n != y.names.len() {
                return Ok(false);
            }
            if !Rc::ptr_eq(&x.names, &y.names) && x.names[..] != y.names[..] {
                return Ok(false);
            }
            for i in 0..n {
                if !val_eq(&x.vals[i], &y.vals[i])? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Value::Fcn(x), Value::Fcn(y)) => {
            if Rc::ptr_eq(x, y) {
                return Ok(true);
            }
            let n = x.dom.len();
            if n != y.dom.len() {
                return Ok(false);
            }
            if !Rc::ptr_eq(&x.dom, &y.dom) {
                for i in 0..n {
                    if !val_eq(&x.dom[i], &y.dom[i])? {
                        return Ok(false);
                    }
                }
            }
            for i in 0..n {
                if !val_eq(&x.vals[i], &y.vals[i])? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Value::Tuple(_) | Value::Record(_) | Value::Fcn(_), Value::Tuple(_) | Value::Record(_) | Value::Fcn(_)) => Ok(false), // canonical forms differ
        (Value::Closure(x), Value::Closure(y)) if Rc::ptr_eq(x, y) => Ok(true),
        (Value::DefRef(x), Value::DefRef(y)) if Rc::ptr_eq(x, y) => Ok(true),
        (Value::LazyFcn(x), Value::LazyFcn(y)) if Rc::ptr_eq(x, y) => Ok(true),
        _ => eq_fail(a, b),
    }
}

pub fn set_eq(a: &Rc<SetV>, b: &Rc<SetV>) -> R<bool> {
    if Rc::ptr_eq(a, b) {
        return Ok(true);
    }
    if let (SetK::Interval(l1, h1), SetK::Interval(l2, h2)) = (&a.k, &b.k) {
        let (s1, s2) = ((h1 - l1 + 1).max(0), (h2 - l2 + 1).max(0));
        return Ok(s1 == s2 && (s1 == 0 || l1 == l2));
    }
    let (ea, eb) = (a.enumerable(), b.enumerable());
    if !ea || !eb {
        if let (SetK::Inf(x), SetK::Inf(y)) = (&a.k, &b.k) {
            return Ok(x == y);
        }
        // TLC (KSubsetValue.equals): two non-empty k-subset values are equal iff k and the base sets are
        if let (SetK::KSubset(k1, b1), SetK::KSubset(k2, b2)) = (&a.k, &b.k) {
            if *k1 > 0 && *k2 > 0 {
                return Ok(k1 == k2 && set_eq(b1, b2)?);
            }
        }
        // sets of records over the same fields with equal component sets
        if let (SetK::RecSet(n1, s1), SetK::RecSet(n2, s2)) = (&a.k, &b.k) {
            if n1 == n2 {
                let mut all = true;
                for (x, y) in s1.iter().zip(s2.iter()) {
                    if !set_eq(x, y)? {
                        all = false;
                        break;
                    }
                }
                if all {
                    return Ok(true);
                }
            }
        }
        if ea != eb {
            return Ok(false);
        }
        return eval_err("Attempted to check equality of two non-enumerable sets.".into());
    }
    let (x, y) = (a.elems()?, b.elems()?);
    if x.len() != y.len() {
        return Ok(false);
    }
    for i in 0..x.len() {
        if !val_eq(&x[i], &y[i])? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `compare` for two scalars of the same kind, without a call; None for everything else.
#[inline(always)]
pub fn scalar_cmp(a: &Value, b: &Value) -> Option<Ordering> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Some(x.cmp(y)),
        (Value::Str(x), Value::Str(y)) => Some(x.0.cmp(&y.0)),
        (Value::Bool(x), Value::Bool(y)) => Some(x.cmp(y)),
        (Value::Model(x), Value::Model(y)) if !any_typed() => Some(x.0.cmp(&y.0)),
        _ => None,
    }
}

pub fn bsearch(arr: &[Value], v: &Value) -> R<Option<usize>> {
    let (mut lo, mut hi) = (0isize, arr.len() as isize - 1);
    while lo <= hi {
        let mid = (lo + hi) >> 1;
        let c = match scalar_cmp(&arr[mid as usize], v) {
            Some(c) => c,
            None => compare(&arr[mid as usize], v)?,
        };
        match c {
            Ordering::Equal => return Ok(Some(mid as usize)),
            Ordering::Less => lo = mid + 1,
            Ordering::Greater => hi = mid - 1,
        }
    }
    Ok(None)
}

/// Stable sort with a fallible comparator: the first comparison error is reported.
pub fn try_sort_by<T>(a: &mut [T], mut f: impl FnMut(&T, &T) -> R<Ordering>) -> R<()> {
    let mut error: Option<Box<Fail>> = None;
    a.sort_by(|x, y| {
        if error.is_some() {
            return Ordering::Equal;
        }
        match f(x, y) {
            Ok(o) => o,
            Err(e) => {
                error = Some(e);
                Ordering::Equal
            }
        }
    });
    match error {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

pub fn sort_dedup(mut a: Vec<Value>) -> R<Vec<Value>> {
    if a.len() < 2 {
        return Ok(a);
    }
    let mut sorted = true;
    for i in 1..a.len() {
        if compare(&a[i - 1], &a[i])? != Ordering::Less {
            sorted = false;
            break;
        }
    }
    if sorted {
        return Ok(a);
    }
    try_sort_by(&mut a, compare)?;
    let mut out: Vec<Value> = Vec::with_capacity(a.len());
    for v in a {
        if let Some(last) = out.last() {
            if compare(last, &v)? == Ordering::Equal {
                continue;
            }
        }
        out.push(v);
    }
    Ok(out)
}
pub fn mk_set(elems: Vec<Value>) -> R<Value> {
    Ok(SetV::of(sort_dedup(elems)?))
}

// ---- functions ----
/// The canonical shape of a function with a given (sorted, duplicate-free) domain.
pub enum FcnShape {
    Empty,
    Tuple,
    Record(Rc<Vec<StrId>>),
    Fcn(Rc<Vec<Value>>),
}
impl FcnShape {
    pub fn of(dom: &[Value]) -> FcnShape {
        let n = dom.len();
        if n == 0 {
            return FcnShape::Empty;
        }
        match &dom[0] {
            Value::Int(1) => {
                if dom.iter().enumerate().all(|(i, d)| matches!(d, Value::Int(x) if *x == i as i64 + 1)) {
                    return FcnShape::Tuple;
                }
            }
            Value::Str(_) => {
                if dom.iter().all(|d| matches!(d, Value::Str(_))) {
                    return FcnShape::Record(Rc::new(dom.iter().map(|d| if let Value::Str(s) = d { *s } else { unreachable!() }).collect()));
                }
            }
            _ => {}
        }
        FcnShape::Fcn(Rc::new(dom.to_vec()))
    }
    /// As `of`, taking the domain: a function that is neither a tuple nor a record keeps the vector.
    pub fn of_owned(dom: Vec<Value>) -> FcnShape {
        match dom.first() {
            None => FcnShape::Empty,
            Some(Value::Int(1)) | Some(Value::Str(_)) => match FcnShape::of(&dom) {
                FcnShape::Fcn(_) => FcnShape::Fcn(Rc::new(dom)),
                sh => sh,
            },
            _ => FcnShape::Fcn(Rc::new(dom)),
        }
    }
    pub fn make(&self, vals: Vec<Value>) -> Value {
        match self {
            FcnShape::Empty => empty_tuple(),
            FcnShape::Tuple => Value::Tuple(TupleV::rc(vals)),
            FcnShape::Record(names) => Value::Record(Rc::new(RecordV::new(names.clone(), vals))),
            FcnShape::Fcn(dom) => Value::Fcn(Rc::new(FcnV::new(dom.clone(), vals))),
        }
    }
}
/// Build a function from a sorted, deduplicated domain and parallel values, in canonical form.
pub fn make_fcn(dom: &[Value], vals: Vec<Value>) -> Value {
    FcnShape::of(dom).make(vals)
}
/// As `make_fcn`, for a domain the caller no longer needs.
pub fn make_fcn_owned(dom: Vec<Value>, vals: Vec<Value>) -> Value {
    FcnShape::of_owned(dom).make(vals)
}
/// Build from unsorted pairs (the first of equal keys wins).
pub fn make_fcn_from_pairs(mut pairs: Vec<(Value, Value)>) -> R<Value> {
    // already strictly increasing (the usual case: pairs derived from a sorted domain): nothing to sort
    let mut sorted = true;
    for i in 1..pairs.len() {
        let c = match scalar_cmp(&pairs[i - 1].0, &pairs[i].0) {
            Some(c) => c,
            None => compare(&pairs[i - 1].0, &pairs[i].0).unwrap_or(Ordering::Equal), // a failure is reported by the sort
        };
        if c != Ordering::Less {
            sorted = false;
            break;
        }
    }
    if sorted {
        let (dom, vals): (Vec<Value>, Vec<Value>) = pairs.into_iter().unzip();
        return Ok(make_fcn_owned(dom, vals));
    }
    try_sort_by(&mut pairs, |x, y| compare(&x.0, &y.0))?;
    let mut dom: Vec<Value> = Vec::with_capacity(pairs.len());
    let mut vals: Vec<Value> = Vec::with_capacity(pairs.len());
    for (d, v) in pairs {
        if let Some(last) = dom.last() {
            if compare(last, &d)? == Ordering::Equal {
                continue;
            }
        }
        dom.push(d);
        vals.push(v);
    }
    Ok(make_fcn(&dom, vals))
}
pub fn make_record(names: &[StrId], vals: Vec<Value>) -> Value {
    let mut idx: Vec<usize> = (0..names.len()).collect();
    idx.sort_by_key(|&i| names[i].0);
    let mut slots: Vec<Option<Value>> = vals.into_iter().map(Some).collect();
    Value::Record(Rc::new(RecordV::new(Rc::new(idx.iter().map(|&i| names[i]).collect()), idx.iter().map(|&i| slots[i].take().unwrap()).collect())))
}
pub fn is_fcn(v: &Value) -> bool {
    matches!(v, Value::Tuple(_) | Value::Record(_) | Value::Fcn(_))
}
pub fn domain_elems(f: &Value) -> R<std::borrow::Cow<'_, [Value]>> {
    use std::borrow::Cow;
    match f {
        Value::Tuple(t) => Ok(Cow::Owned((1..=t.len() as i64).map(Value::Int).collect())),
        Value::Record(r) => Ok(Cow::Owned(r.names.iter().map(|n| Value::Str(*n)).collect())),
        Value::Fcn(f) => Ok(Cow::Borrowed(&f.dom[..])),
        _ => eval_err(format!("Attempted to compute the domain of the non-function value:\n{}", fmt(f))),
    }
}
pub fn domain_of(f: &Value) -> Option<Rc<SetV>> {
    match f {
        Value::Tuple(t) => Some(Rc::new(SetV::new(SetK::Interval(1, t.len() as i64)))),
        Value::Record(r) => Some(Rc::new(SetV::new(SetK::Enum(r.names.iter().map(|n| Value::Str(*n)).collect())))),
        Value::Fcn(f) => Some(Rc::new(SetV::new(SetK::Enum(f.dom.to_vec())))),
        _ => None,
    }
}
pub fn fcn_values(f: &Value) -> R<&[Value]> {
    match f {
        Value::Tuple(t) => Ok(t),
        Value::Record(r) => Ok(&r.vals),
        Value::Fcn(f) => Ok(&f.vals),
        _ => eval_err(format!("Attempted to apply a function operation to the non-function value:\n{}", fmt(f))),
    }
}

// ---- hashing ----
/// 64-bit fingerprint hasher (folded-multiply mixing). Equal values (as decided by `val_eq`) hash equally
/// because every value is hashed in its canonical form.
pub struct Hasher {
    h: u64,
}
const K1: u64 = 0x9E37_79B9_7F4A_7C15;
const K2: u64 = 0xD6E8_FEB8_6659_FD93;
impl Hasher {
    pub fn new() -> Hasher {
        Hasher { h: 0x243F_6A88_85A3_08D3 }
    }
    #[inline]
    pub fn add(&mut self, x: u64) {
        let m = ((self.h ^ x) as u128).wrapping_mul(K2 as u128);
        self.h = ((m as u64) ^ ((m >> 64) as u64)).wrapping_add(K1);
    }
    /// Composite values are hashed once: the result is cached in the value and mixed into the enclosing
    /// hash as a single word (unchanged parts of a state are shared between states, so most of a state is
    /// never re-hashed).
    #[inline]
    pub fn value(&mut self, v: &Value) -> R<()> {
        let w = value_word(v)?;
        self.add(w);
        Ok(())
    }
    #[inline]
    pub fn finish(&self) -> u64 {
        let mut h = self.h;
        h ^= h >> 32;
        h = h.wrapping_mul(0xD6E8_FEB8_6659_FD93);
        h ^= h >> 32;
        h = h.wrapping_mul(0xD6E8_FEB8_6659_FD93);
        h ^= h >> 32;
        h
    }
}
/// The 64-bit word that stands for a value in a hash: a tagged scalar, or the (cached) hash of a composite.
/// It depends only on the content of the value.
#[inline]
pub fn value_word(v: &Value) -> R<u64> {
    Ok(match v {
        Value::Int(i) => 1 ^ ((*i as u64) << 4),
        Value::Bool(b) => {
            if *b {
                3
            } else {
                2
            }
        }
        Value::Str(s) => str_hash(*s).rotate_left(5) ^ 4,
        Value::Model(m) => str_hash(*m).rotate_left(11) ^ 9,
        Value::Tuple(t) => {
            let c = t.h.get();
            if c != 0 {
                c
            } else {
                composite_word(v)?
            }
        }
        Value::Record(r) => {
            let c = r.h.get();
            if c != 0 {
                c
            } else {
                composite_word(v)?
            }
        }
        Value::Fcn(f) => {
            let c = f.h.get();
            if c != 0 {
                c
            } else {
                composite_word(v)?
            }
        }
        _ => composite_word(v)?,
    })
}
#[inline(never)]
fn composite_word(v: &Value) -> R<u64> {
    let mut hh = Hasher::new();
    hh.composite(v)?;
    Ok(hh.h)
}
impl Hasher {
    /// Hashes a composite value once (the result is cached in the value) and leaves its word in `self.h`.
    fn composite(&mut self, v: &Value) -> R<()> {
        self.h = 0;
        match v {
            Value::Tuple(t) => {
                let mut c = t.h.get();
                if c == 0 {
                    let mut h = Hasher::new();
                    h.add(5 ^ ((t.len() as u64) << 4));
                    for x in t.iter() {
                        h.value(x)?;
                    }
                    c = h.finish();
                    t.h.set(c);
                }
                self.h = c;
            }
            Value::Record(r) => {
                let mut c = r.h.get();
                if c == 0 {
                    let mut h = Hasher::new();
                    h.add(6 ^ ((r.names.len() as u64) << 4));
                    for i in 0..r.names.len() {
                        h.add(str_hash(r.names[i]));
                        h.value(&r.vals[i])?;
                    }
                    c = h.finish();
                    r.h.set(c);
                }
                self.h = c;
            }
            Value::Set(s) => {
                let mut c = s.h.get();
                if c == 0 {
                    let mut h = Hasher::new();
                    if let SetK::Interval(lo, hi) = &s.k {
                        // same stream as the enumerated set, without materializing it
                        let n = (hi - lo + 1).max(0);
                        h.add(7 ^ ((n as u64) << 4));
                        for i in *lo..=*hi {
                            h.add(1 ^ ((i as u64) << 4));
                        }
                    } else {
                        let e = s.elems()?;
                        h.add(7 ^ ((e.len() as u64) << 4));
                        for x in e {
                            h.value(x)?;
                        }
                    }
                    c = h.finish();
                    s.h.set(c);
                }
                self.h = c;
            }
            Value::Fcn(f) => {
                let mut c = f.h.get();
                if c == 0 {
                    let mut h = Hasher::new();
                    h.add(8 ^ ((f.dom.len() as u64) << 4));
                    for i in 0..f.dom.len() {
                        h.value(&f.dom[i])?;
                        h.value(&f.vals[i])?;
                    }
                    c = h.finish();
                    f.h.set(c);
                }
                self.h = c;
            }
            _ => return eval_err("Attempted to fingerprint a non-value (operator or lazy function).".into()),
        }
        Ok(())
    }
}

// ---- printing (TLC format) ----
fn fmt_str(s: &str, o: &mut String) {
    o.push('"');
    for ch in s.chars() {
        match ch {
            '\\' => o.push_str("\\\\"),
            '"' => o.push_str("\\\""),
            '\n' => o.push_str("\\n"),
            '\t' => o.push_str("\\t"),
            '\r' => o.push_str("\\r"),
            '\x0c' => o.push_str("\\f"),
            c => o.push(c),
        }
    }
    o.push('"');
}
fn is_ident(s: &str) -> bool {
    s.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_') && s.bytes().any(|c| c.is_ascii_alphabetic())
}

thread_local! {
    static FMT_ERR: std::cell::RefCell<Option<Box<Fail>>> = const { std::cell::RefCell::new(None) };
}
/// Like `fmt`, but reports an error raised while enumerating a lazy set that has to be printed
/// (the TypeScript `fmt` throws in that case).
pub fn fmt_checked(v: &Value) -> R<String> {
    FMT_ERR.with(|c| *c.borrow_mut() = None);
    let s = fmt(v);
    match FMT_ERR.with(|c| c.borrow_mut().take()) {
        Some(e) => Err(e),
        None => Ok(s),
    }
}

pub fn fmt(v: &Value) -> String {
    let mut o = String::new();
    fmt_into(v, &mut o);
    o
}
pub fn fmt_set(s: &SetV) -> String {
    let mut o = String::new();
    fmt_set_into(s, &mut o);
    o
}
fn join(items: &[Value], sep: &str, o: &mut String) {
    for (i, x) in items.iter().enumerate() {
        if i > 0 {
            o.push_str(sep);
        }
        fmt_into(x, o);
    }
}
fn fmt_set_into(s: &SetV, o: &mut String) {
    match &s.k {
        SetK::Enum(e) => {
            o.push('{');
            join(e, ", ", o);
            o.push('}');
        }
        SetK::Interval(lo, hi) => {
            o.push_str(&format!("{}..{}", lo, hi));
        }
        SetK::Subset(b) => {
            o.push_str("SUBSET ");
            fmt_set_into(b, o);
        }
        SetK::FcnSet(d, r) => {
            o.push('[');
            fmt_set_into(d, o);
            o.push_str(" -> ");
            fmt_set_into(r, o);
            o.push(']');
        }
        SetK::RecSet(names, sets) => {
            o.push('[');
            for i in 0..names.len() {
                if i > 0 {
                    o.push_str(", ");
                }
                o.push_str(&str_of(names[i]));
                o.push_str(": ");
                fmt_set_into(&sets[i], o);
            }
            o.push(']');
        }
        SetK::Cross(sets) => {
            o.push('(');
            for (i, x) in sets.iter().enumerate() {
                if i > 0 {
                    o.push_str(" \\X ");
                }
                fmt_set_into(x, o);
            }
            o.push(')');
        }
        SetK::Seq(b) => {
            o.push_str("Seq(");
            fmt_set_into(b, o);
            o.push(')');
        }
        SetK::Inf(k) => o.push_str(match k {
            Inf::Nat => "Nat",
            Inf::Int => "Int",
            Inf::Real => "Real",
            Inf::String => "STRING",
        }),
        SetK::Any => o.push_str("Any"),
        SetK::KSubset(0, _) => o.push_str("{{}}"),
        SetK::KSubset(k, b) => {
            o.push_str(&format!("kSubset({}, ", k));
            fmt_set_into(b, o);
            o.push(')');
        }
        _ => {
            if s.is_derived() && s.enumerable() {
                match s.elems() {
                    Ok(e) => {
                        o.push('{');
                        join(e, ", ", o);
                        o.push('}');
                        return;
                    }
                    Err(e) => FMT_ERR.with(|c| {
                        let mut c = c.borrow_mut();
                        if c.is_none() {
                            *c = Some(e);
                        }
                    }),
                }
            }
            o.push_str(&s.desc());
        }
    }
}
pub fn fmt_into(v: &Value, o: &mut String) {
    match v {
        Value::Undef => o.push_str("<undefined>"),
        Value::Int(i) => o.push_str(&i.to_string()),
        Value::Bool(b) => o.push_str(if *b { "TRUE" } else { "FALSE" }),
        Value::Str(s) => fmt_str(&str_of(*s), o),
        Value::Model(m) => o.push_str(&str_of(*m)),
        Value::Tuple(t) => {
            o.push_str("<<");
            join(t, ", ", o);
            o.push_str(">>");
        }
        Value::Record(r) => {
            o.push('[');
            for i in 0..r.names.len() {
                if i > 0 {
                    o.push_str(", ");
                }
                let n = str_of(r.names[i]);
                if is_ident(&n) {
                    o.push_str(&n);
                } else {
                    fmt_str(&n, o);
                }
                o.push_str(" |-> ");
                fmt_into(&r.vals[i], o);
            }
            o.push(']');
        }
        Value::Fcn(f) => {
            o.push('(');
            for i in 0..f.dom.len() {
                if i > 0 {
                    o.push_str(" @@ ");
                }
                fmt_into(&f.dom[i], o);
                o.push_str(" :> ");
                fmt_into(&f.vals[i], o);
            }
            o.push(')');
        }
        Value::Set(s) => fmt_set_into(s, o),
        Value::Closure(c) => o.push_str(&format!("<operator {}>", c.name)),
        Value::DefRef(d) => o.push_str(&format!("<operator {}>", d.def.name)),
        Value::LazyFcn(_) => o.push_str("<lazy function>"),
        Value::Thunk(_) => o.push_str("<operator>"),
    }
}
