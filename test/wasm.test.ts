// End-to-end tests of the programmatic API on small in-memory specifications. Expected numbers were
// produced by the reference Java TLC (tla2tools 1.8.0).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { check, fmt } from '../wasm/everystate.mjs';

const DIEHARD = `---- MODULE DieHard ----
EXTENDS Naturals
VARIABLES big, small
TypeOK == small \\in 0..3 /\\ big \\in 0..5
Init == big = 0 /\\ small = 0
FillSmall == small' = 3 /\\ big' = big
FillBig == big' = 5 /\\ small' = small
EmptySmall == small' = 0 /\\ big' = big
EmptyBig == big' = 0 /\\ small' = small
Min(m, n) == IF m < n THEN m ELSE n
SmallToBig == /\\ big' = Min(big + small, 5)
              /\\ small' = small - (big' - big)
BigToSmall == /\\ small' = Min(big + small, 3)
              /\\ big' = big - (small' - small)
Next == FillSmall \\/ FillBig \\/ EmptySmall \\/ EmptyBig \\/ SmallToBig \\/ BigToSmall
Spec == Init /\\ [][Next]_<<big, small>>
NotSolved == big # 4
====`;

test('DieHard: invariant violation with the shortest trace', () => {
  const { result, model } = check({ root: 'DieHard', modules: { DieHard: DIEHARD }, config: 'SPECIFICATION Spec\nINVARIANTS TypeOK NotSolved' });
  assert.equal(result.status, 'invariant');
  assert.equal(result.name, 'NotSolved');
  assert.deepEqual([result.generated, result.distinct, result.queue, result.depth], [73, 14, 1, 7]);
  assert.deepEqual(result.trace!.map(t => t.action?.name ?? 'Init'), ['Init', 'FillBig', 'BigToSmall', 'EmptySmall', 'BigToSmall', 'FillBig', 'BigToSmall']);
  const last = result.trace!.at(-1)!.state;
  assert.equal(fmt(last[model.vars.findIndex(v => v.name === 'big')]), '4');
});

test('DieHard: full state space without the puzzle invariant', () => {
  const { result } = check({ root: 'DieHard', modules: { DieHard: DIEHARD }, config: 'SPECIFICATION Spec\nINVARIANT TypeOK' });
  assert.equal(result.status, 'ok');
  assert.deepEqual([result.generated, result.distinct, result.queue], [97, 16, 0]);
});

test('deadlock is reported unless disabled', () => {
  const spec = `---- MODULE D ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\n====`;
  const cfg = 'INIT Init\nNEXT Next';
  const a = check({ root: 'D', modules: { D: spec }, config: cfg });
  assert.equal(a.result.status, 'deadlock');
  assert.equal(a.result.trace!.length, 4);
  const b = check({ root: 'D', modules: { D: spec }, config: cfg, deadlock: false });
  assert.equal(b.result.status, 'ok');
  assert.deepEqual([b.result.generated, b.result.distinct], [4, 4]);
});

test('liveness: weak fairness lets the counter loop forever below 3', () => {
  const spec = `---- MODULE L ----
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Up == x < 2 /\\ x' = x + 1
Back == x = 2 /\\ x' = 1
Next == Up \\/ Back
Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)
ReachesThree == <>(x = 3)
ReachesTwo == <>(x = 2)
====`;
  const bad = check({ root: 'L', modules: { L: spec }, config: 'SPECIFICATION Spec\nPROPERTY ReachesThree' });
  assert.equal(bad.result.status, 'liveness');
  assert.deepEqual(bad.result.trace!.map(t => fmt(t.state[0])), ['0', '1', '2']);
  assert.equal(bad.result.loopTo, 1);
  assert.equal(bad.result.loopAction?.name, 'Back');
  const good = check({ root: 'L', modules: { L: spec }, config: 'SPECIFICATION Spec\nPROPERTY ReachesTwo' });
  assert.equal(good.result.status, 'ok');
});

test('constants, model values, symmetry and records', () => {
  const spec = `---- MODULE S ----
EXTENDS Naturals, FiniteSets, TLC
CONSTANTS Procs, None
VARIABLES owner, waiting
Init == owner = None /\\ waiting = {}
Request(p) == p \\notin waiting /\\ owner # p /\\ waiting' = waiting \\cup {p} /\\ UNCHANGED owner
Grant(p) == owner = None /\\ p \\in waiting /\\ owner' = p /\\ waiting' = waiting \\ {p}
Release(p) == owner = p /\\ owner' = None /\\ UNCHANGED waiting
Next == \\E p \\in Procs : Request(p) \\/ Grant(p) \\/ Release(p)
Spec == Init /\\ [][Next]_<<owner, waiting>>
Mutex == Cardinality({p \\in Procs : owner = p}) <= 1
Sym == Permutations(Procs)
====`;
  const cfg = 'SPECIFICATION Spec\nCONSTANTS Procs = {p1, p2, p3}\n None = None\nINVARIANT Mutex\n';
  const plain = check({ root: 'S', modules: { S: spec }, config: cfg });
  const sym = check({ root: 'S', modules: { S: spec }, config: cfg + 'SYMMETRY Sym\n' });
  assert.equal(plain.result.status, 'ok');
  assert.equal(sym.result.status, 'ok');
  assert.deepEqual([plain.result.generated, plain.result.distinct], [49, 20]);
  assert.deepEqual([sym.result.generated, sym.result.distinct], [19, 7]);
});

test('a function from strings prints as a record only when every key is a name', () => {
  const spec = `---- MODULE K ----
EXTENDS TLC
F(S) == [k \\in S |-> 1]
VARIABLES digits, under, fair, space, empty, merged, nested, sf, keyword, exponent, accent
Init == /\\ digits = F({"72", "dup:72"})
        /\\ under = F({"a", "_"})
        /\\ fair = F({"a", "WF_x"})
        /\\ space = F({"a", "a b"})
        /\\ empty = F({"a", ""})
        /\\ merged = [a |-> 1] @@ ("72" :> 1)
        /\\ nested = [r \\in {"a", "b"} |-> F({"c", "d:e"})]
        /\\ sf = F({"a", "SF_"})
        /\\ keyword = F({"a", "IF"})
        /\\ exponent = F({"a", "1e5"})
        /\\ accent = F({"a", "é"})
Next == UNCHANGED <<digits, under, fair, space, empty, merged, nested, sf, keyword, exponent, accent>>
Shown == digits = <<>>
====`;
  const { result, model } = check({ root: 'K', modules: { K: spec }, config: 'INIT Init\nNEXT Next\nINVARIANT Shown' });
  // as printed by TLC 2.19 and 1.8.0
  const want: Record<string, string> = {
    digits: '("72" :> 1 @@ "dup:72" :> 1)',
    under: '("a" :> 1 @@ "_" :> 1)',
    fair: '("a" :> 1 @@ "WF_x" :> 1)',
    space: '("a" :> 1 @@ "a b" :> 1)',
    empty: '("a" :> 1 @@ "" :> 1)',
    merged: '("a" :> 1 @@ "72" :> 1)',
    nested: '[a |-> ("c" :> 1 @@ "d:e" :> 1), b |-> ("c" :> 1 @@ "d:e" :> 1)]',
    sf: '[a |-> 1, SF_ |-> 1]',
    keyword: '[a |-> 1, IF |-> 1]',
    exponent: '[a |-> 1, 1e5 |-> 1]',
    accent: '[a |-> 1, é |-> 1]',
  };
  const state = result.trace![0].state;
  for (const [name, text] of Object.entries(want)) assert.equal(state[model.vars.findIndex(v => v.name === name)], text, name);
});

test('errors: unknown operator and missing constant', () => {
  assert.throws(() => check({ root: 'E', modules: { E: '---- MODULE E ----\nVARIABLE x\nInit == x = Foo\nNext == x\' = x\n====' }, config: 'INIT Init\nNEXT Next' }), /Unknown operator/);
  assert.throws(() => check({ root: 'E', modules: { E: '---- MODULE E ----\nCONSTANT C\nVARIABLE x\nInit == x = C\nNext == x\' = x\n====' }, config: 'INIT Init\nNEXT Next' }), /not assigned a value/);
});

test('simulate: random behaviours instead of the whole state space', () => {
  const input = { root: 'DieHard', modules: { DieHard: DIEHARD }, config: 'SPECIFICATION Spec\nINVARIANTS TypeOK NotSolved' };
  const a = check({ ...input, simulate: { traces: 2000, seed: 7 } });
  assert.equal(a.result.status, 'invariant');
  assert.equal(a.result.name, 'NotSolved');
  assert.deepEqual([a.result.mode, a.result.seed, a.result.aril, a.result.distinct, a.result.queue], ['simulate', 7, 0, -1, -1]);
  assert.ok(a.result.traces! >= 1 && a.result.traces! <= 2000 && a.result.generated > 1);
  // the trace starts in the initial state, ends in the violation, and every step is one of the actions
  const big = a.model.vars.findIndex(v => v.name === 'big'), small = a.model.vars.findIndex(v => v.name === 'small');
  const trace = a.result.trace!;
  assert.deepEqual([trace[0].action, trace[0].state[big], trace[0].state[small]], [null, '0', '0']);
  assert.equal(trace.at(-1)!.state[big], '4');
  const step: Record<string, (b: number, s: number) => [number, number]> = {
    FillSmall: b => [b, 3], FillBig: (_, s) => [5, s], EmptySmall: b => [b, 0], EmptyBig: (_, s) => [0, s],
    SmallToBig: (b, s) => [Math.min(b + s, 5), s - (Math.min(b + s, 5) - b)], BigToSmall: (b, s) => [b - (Math.min(b + s, 3) - s), Math.min(b + s, 3)],
  };
  for (let i = 1; i < trace.length; i++) {
    const prev = trace[i - 1].state, cur = trace[i].state;
    assert.deepEqual(step[trace[i].action!.name](Number(prev[big]), Number(prev[small])), [Number(cur[big]), Number(cur[small])]);
  }
  // the same seed repeats the run; without one, the seed used is reported
  assert.deepEqual(check({ ...input, simulate: { traces: 2000, seed: 7 } }).result, a.result);
  const free = check({ ...input, simulate: { traces: 2000 } }).result;
  assert.ok(Number.isSafeInteger(free.seed));
  assert.deepEqual(check({ ...input, simulate: { traces: 2000, seed: free.seed } }).result, free);

  // a model without errors: `true` generates the default 1000 behaviours of at most 100 steps
  const ok = check({ root: 'DieHard', modules: { DieHard: DIEHARD }, config: 'SPECIFICATION Spec\nINVARIANT TypeOK', simulate: true });
  assert.deepEqual([ok.result.status, ok.result.mode, ok.result.traces, ok.result.depth], ['ok', 'simulate', 1000, 101]);
  assert.ok(ok.result.generated > 100_000);
  const short = check({ root: 'DieHard', modules: { DieHard: DIEHARD }, config: 'SPECIFICATION Spec\nINVARIANT TypeOK', simulate: { traces: 3, depth: 2, seed: 1 } });
  assert.deepEqual([short.result.traces, short.result.depth], [3, 3]);
  // exhaustive results carry no simulation fields
  assert.equal(check(input).result.mode, undefined);
});
