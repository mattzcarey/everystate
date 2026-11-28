# everystate: benchmark and conformance status

Engines compared, one worker each, doing the same breadth-first check of the same model:

- **Rust**: `target/release/everystate` (native);
- **Rust/WASM (Node)**: the same core compiled to `wasm32-unknown-unknown`, run by `node wasm/cli.mjs`;
- **TLC**: Java TLC (`tla2tools.jar`, `-workers 1`).

All engines must report the same generated / distinct state counts (`counts agree` column).

## Against tla-ts and Java TLC (2026-11-27, everystate 0.4.1)

[tla-ts](https://github.com/aidenybai/tla-ts) is a TLC-compatible model checker written in TypeScript.
This section runs everystate 0.4.1 (native binary, default settings), tla-ts 0.0.10 (the npm package,
run by Node v22) and Java TLC 2026.11.06 (OpenJDK 21, `-XX:+UseParallelGC`) on the same models: the
three benchmark specifications of the tla-ts repository (Commit, Philosophers, Queue), the 12 models
of the table below, and the tlaplus/Examples models that the Examples manifests record at 5 s or less.

- Wall-clock seconds of the whole process (start-up, parsing and checking), one process at a time on
  the 4-core machine described below. Peak RSS is the largest of the runs.
- "faster than" is the other engine's time divided by everystate's.
- tla-ts and TLC get the same library path (the TLAPS and CommunityModules sources); everystate has
  those modules built in. All three run with the options the Examples CI uses.
- State counts agree on every row.
- The 4-core machine is the limit for the worker comparison: tla-ts publishes its own multi-worker
  figures for 8 workers on an Apple M4 Pro, which this does not reproduce. Here its times with
  `-workers 4` are about the same as with one.
- In the corpus table a model counts when the engine gives the result kind recorded in the manifest
  and, for a successful check, the recorded number of distinct states. The six models tla-ts does not
  get right in this setup end in an evaluation error or a false `ASSUME`; it was not investigated
  whether another configuration of tla-ts would run them.

### One worker (median of 3)

| model | distinct | everystate s | tla-ts s | TLC s | faster than tla-ts | faster than TLC | RSS MB everystate / tla-ts / TLC | counts agree |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| Commit | 282251 | 3.49 | 5.83 | 6.69 | 1.7x | 1.9x | 121 / 209 / 1042 | yes |
| Philosophers | 128889 | 0.79 | 1.75 | 2.01 | 2.2x | 2.6x | 51 / 152 / 374 | yes |
| Queue | 44044 | 0.08 | 0.52 | 0.89 | 6.7x | 11.6x | 23 / 127 / 164 | yes |
| TCommit | 34 | 0.00 | 0.29 | 0.60 | 61.4x | 128.8x | 13 / 102 / 108 | yes |
| ACP_SB_TLC | 54944 | 0.31 | 1.10 | 1.58 | 3.6x | 5.1x | 29 / 142 / 245 | yes |
| StaleShrinkV6Wait2x | 43348 | 0.26 | 1.01 | 1.55 | 3.9x | 5.9x | 29 / 140 / 267 | yes |
| Barriers | 29279 | 1.96 | 4.74 | 4.02 | 2.4x | 2.1x | 23 / 180 / 1030 | yes |
| SimpleRegular | 277726 | 3.24 | 5.22 | 5.15 | 1.6x | 1.6x | 163 / 234 / 1109 | yes |
| Paxos | 1207 | 0.72 | 4.31 | 1.81 | 6.0x | 2.5x | 53 / 136 / 360 | yes |
| VoteProof | 6962 | 5.28 | 10.61 | 11.23 | 2.0x | 2.1x | 19 / 169 / 1242 | yes |
| MCNanoMedium | 530587 | 13.39 | 18.52 | 18.65 | 1.4x | 1.4x | 618 / 1149 / 1339 | yes |
| MCBakery | 655200 | 7.29 | 16.34 | 10.65 | 2.2x | 1.5x | 215 / 686 / 1333 | yes |
| MCLamportMutex | 724274 | 10.48 | 21.57 | 14.18 | 2.1x | 1.4x | 533 / 339 / 1349 | yes |
| MCbtree | 374727 | 10.43 | 13.41 | 30.75 | 1.3x | 2.9x | 194 / 229 / 1355 | yes |
| GameOfLife | 65536 | 8.77 | 14.25 | 10.56 | 1.6x | 1.2x | 38 / 165 / 1247 | yes |

### Four workers (median of 3)

| model | distinct | everystate s | tla-ts s | TLC s | faster than tla-ts | faster than TLC | RSS MB everystate / tla-ts / TLC | counts agree |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| Commit | 282251 | 1.33 | 5.47 | 4.30 | 4.1x | 3.2x | 111 / 211 / 1032 | yes |
| SimpleRegular | 277726 | 1.52 | 5.26 | 4.10 | 3.5x | 2.7x | 152 / 237 / 1106 | yes |
| VoteProof | 6962 | 1.69 | 10.94 | 4.37 | 6.5x | 2.6x | 47 / 178 / 1267 | yes |
| MCNanoMedium | 530587 | 4.01 | 18.12 | 8.12 | 4.5x | 2.0x | 420 / 1149 / 1334 | yes |
| MCBakery | 655200 | 3.97 | 11.95 | 7.83 | 3.0x | 2.0x | 366 / 302 / 1331 | yes |
| MCLamportMutex | 724274 | 3.28 | 20.87 | 9.08 | 6.4x | 2.8x | 224 / 355 / 1356 | yes |
| MCbtree | 374727 | 3.88 | 14.30 | 11.71 | 3.7x | 3.0x | 387 / 231 / 1367 | yes |
| GameOfLife | 65536 | 2.46 | 13.81 | 4.29 | 5.6x | 1.7x | 71 / 166 / 1253 | yes |

### tlaplus/Examples, 122 models recorded at up to 5 s (one run each, 1 worker)

| engine | result and distinct count as recorded | total s, all models | total s, models all three get right |
|---|---:|---:|---:|
| everystate | 122 of 122 | 43.1 | 36.1 |
| tla-ts | 116 of 122 | 151.1 | 148.6 |
| tlc | 122 of 122 | 179.6 | 156.5 |

tla-ts differs on: FiniteMonotonic/MCCRDT (assumption failure); FiniteMonotonic/MCReplicatedLog (assumption failure); TLC/TestGraphs (error); YoYo/YoYoAllGraphs (error, 0 distinct); ewd998/EWD998ChanTrace (assumption failure); glowingRaccoon/product (error)

Reproduce with `node scripts/bench-vs.mjs --runs 3` (the paths are environment variables at the top of
the script); the raw runs are in `bench/vs.jsonl`.

## Result (2026-11-18, version 0.4.0)

Median wall-clock seconds of 3 runs of the whole process (start-up, parsing and checking), one worker
each, the runs strictly sequential with nothing else running (load average about 1). "Rust vs TLC" is
TLC's time divided by Rust's: above 1 means everystate is faster. It is faster than single-worker TLC
on every row, by 1.3x to 5.7x on the models that run long enough to measure (TCommit is start-up only).
The default engine is used: the compiled evaluator, no step cache.

| model | distinct | generated | Rust s | Rust/WASM (Node) s | TLC (1 worker) s | Rust states/s | TLC states/s | Rust vs TLC | RSS Rust MB | counts agree |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| TCommit (tiny (startup)) | 34 | 94 | 0.01 | 0.08 | 0.51 | 18,683 | 186 | 100.6x | 12 | yes |
| ACP_SB_TLC (sets, quantifiers) | 54944 | 218352 | 0.22 | 0.64 | 1.25 | 985,016 | 174,177 | 5.7x | 28 | yes |
| StaleShrinkV6Wait2x (records) | 43348 | 111445 | 0.22 | 0.69 | 1.23 | 515,009 | 90,618 | 5.7x | 28 | yes |
| Barriers (functions (PlusCal)) | 29279 | 104515 | 1.47 | 2.54 | 3.09 | 71,018 | 33,858 | 2.1x | 21 | yes |
| SimpleRegular (functions (PlusCal)) | 277726 | 1454776 | 2.77 | 6.77 | 4.33 | 525,405 | 335,618 | 1.6x | 178 | yes |
| Paxos (symmetry, sets of records) | 1207 | 13290 | 0.65 | 1.27 | 1.51 | 20,313 | 8,830 | 2.3x | 52 | yes |
| VoteProof (set heavy, quantifiers) | 6962 | 318877 | 4.21 | 8.28 | 9.87 | 75,820 | 32,314 | 2.3x | 16 | yes |
| MCNanoMedium (VIEW, records, sets) | 530587 | 1120079 | 10.89 | 24.62 | 15.07 | 102,895 | 74,324 | 1.4x | 616 | yes |
| MCBakery (functions (PlusCal)) | 655200 | 3403584 | 5.80 | 11.44 | 8.31 | 587,044 | 409,498 | 1.4x | 213 | yes |
| MCLamportMutex (functions of sequences) | 724274 | 2729079 | 8.51 | 20.85 | 11.74 | 320,512 | 232,554 | 1.4x | 532 | yes |
| MCbtree (function / set heavy) | 374727 | 2820091 | 8.45 | 17.13 | 25.76 | 333,916 | 109,457 | 3.1x | 193 | yes |
| GameOfLife (recursive operators, functions) | 65536 | 131072 | 6.93 | 13.43 | 8.99 | 18,911 | 14,584 | 1.3x | 36 | yes |

The raw per-run times are in `bench-last.log`. Machine, versions and commands are as described below;
the sections that follow are earlier measurements, kept for the history.

## Result (2026-11-14, after the performance pass)

Median wall-clock seconds of 3 runs of the whole process (start-up, parsing and checking).
"Rust vs TLC" is TLC's time divided by Rust's: above 1 means everystate is faster. It is faster than
single-worker TLC on every row.

| model | distinct | generated | Rust 0.2.0 s (before) | Rust s (after) | Rust/WASM (Node) s | TLC (1 worker) s | Rust states/s | TLC states/s | Rust vs TLC before | Rust vs TLC after | RSS Rust MB | counts agree |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| TCommit (tiny (startup)) | 34 | 94 | 0.01 | 0.01 | 0.08 | 0.63 | 7,626 | 150 | 76.5x | 51.0x | 12 | yes |
| ACP_SB_TLC (sets, quantifiers) | 54944 | 218352 | 0.40 | 0.33 | 0.73 | 1.43 | 658,700 | 152,281 | 4.2x | 4.3x | 28 | yes |
| StaleShrinkV6Wait2x (records) | 43348 | 111445 | 0.40 | 0.33 | 0.83 | 1.54 | 332,936 | 72,371 | 3.8x | 4.6x | 28 | yes |
| Barriers (functions (PlusCal)) | 29279 | 104515 | 2.15 | 2.10 | 3.16 | 3.64 | 49,857 | 28,745 | 1.9x | 1.7x | 20 | yes |
| SimpleRegular (functions (PlusCal)) | 277726 | 1454776 | 4.38 | 3.50 | 7.32 | 4.75 | 415,338 | 306,019 | 1.3x | 1.4x | 178 | yes |
| Paxos (symmetry, sets of records) | 1207 | 13290 | 2.62 | 0.75 | 1.37 | 1.69 | 17,735 | 7,860 | 0.6x | 2.3x | 52 | yes |
| VoteProof (set heavy, quantifiers) | 6962 | 318877 | 6.27 | 5.15 | 9.98 | 11.38 | 61,878 | 28,021 | 1.9x | 2.2x | 15 | yes |
| MCNanoMedium (VIEW, records, sets) | 530587 | 1120079 | 13.87 | 13.60 | 28.12 | 17.86 | 82,337 | 62,703 | 1.3x | 1.3x | 616 | yes |
| MCBakery (functions (PlusCal)) | 655200 | 3403584 | 9.32 | 7.98 | 13.49 | 9.24 | 426,394 | 368,306 | 1.1x | 1.2x | 212 | yes |
| MCLamportMutex (functions of sequences) | 724274 | 2729079 | 14.39 | 11.66 | 25.45 | 13.50 | 234,126 | 202,100 | 1.0x | 1.2x | 531 | yes |
| MCbtree (function / set heavy) | 374727 | 2820091 | 14.74 | 11.92 | 22.10 | 30.93 | 236,557 | 91,168 | 2.3x | 2.6x | 193 | yes |
| GameOfLife (recursive operators, functions) | 65536 | 131072 | 22.55 | 9.09 | 16.21 | 10.30 | 14,413 | 12,729 | 0.5x | 1.1x | 39 | yes |

- "before": the 0.2.0 binary (git HEAD before this pass), one run per model on the same machine on
  the same day. "Rust vs TLC before" is the ratio from the previous version of this table (2026-11-13).
- The raw per-run times are in `bench-last.log`.

### Machine and versions

- Intel Xeon @ 2.10 GHz, 4 cores (1 thread per core), 15 GB RAM, Linux 6.18 (Firecracker VM).
- rustc 1.97.0, release profile with `lto = "fat"`, `codegen-units = 1`, `panic = "abort"`, mimalloc (native only).
- WebAssembly: `wasm32-unknown-unknown`, same profile, standard allocator, run under Node v22.23.4.
- OpenJDK 21.0.12 with `-XX:+UseParallelGC`, TLC 2026.11.06 (`tla2tools.jar` in `refs/`).

**Load caveat.** The machine was shared: the load average was 0.7 at the start of the run (1.3 over
the preceding five minutes) on 4 cores. The benchmark itself ran strictly sequentially. Run-to-run
variation of one cell is up to about 10 % (see `bench-last.log`), so the 1.1x on GameOfLife and the
1.2x on MCBakery and MCLamportMutex are real but not large margins. A second complete run of the same
table half an hour earlier (same code except for the bound on the permutation memo) gave ratios
within 0.1x of these on every row that runs for more than two seconds. Peak RSS was measured in a
separate fourth run through `getrusage(RUSAGE_CHILDREN)`.

### Commands

```
npm run build                            # cargo build --release && wasm/build.sh
node scripts/bench.mjs --runs 3          # prints the table; progress and raw times go to stderr
```

Per model `bench.mjs` runs, with `cwd = refs/Examples` for the first two:

```
target/release/everystate -json -config <cfg> <spec>
node wasm/cli.mjs -config <cfg> <spec>
# cwd = directory of the spec, JAVA_TOOL_OPTIONS unset:
java -XX:+UseParallelGC -DTLA-Library=refs/tlapm/library:refs/CommunityModules/modules \
     -cp refs/tla2tools.jar tlc2.TLC -workers 1 -metadir <tmp> -config <cfg> <spec>
```

## The performance pass

Profiles first (callgrind instruction counts on the `profiling` cargo profile; `perf` is not
available here), then changes. What the profiles said:

- **Paxos** (0.6x before): 95 % of the instructions were in symmetry canonicalisation. Every
  generated state was permuted by all 143 permutations; the cost was permuting and re-sorting the
  set of messages, generic `compare`, a hash-map lookup per model value, and a thread-local access
  per model-value comparison.
- **GameOfLife** (0.5x before): nothing in the checker; all in the evaluator. `Sum(sc, points)`
  passed the function definition `sc` as an operator argument, and `f[x]` then built all of `sc`
  (36 CASE evaluations) to read one point; each application of a lazy function re-evaluated its
  domain expression; the constant `nbrs` set was rebuilt on every call of `score`.
- **MCBakery, MCLamportMutex, SimpleRegular, MCNanoMedium**: flat. 60-90 % is the tree walk
  (`eval`, `eval_app`, `enumerate` and their continuations), about 8 % the allocator, 5-16 % set
  membership and `compare` for the type invariants, 3-7 % fingerprinting. Identifier lookup in the
  linked contexts is only 3-5 %.

One line per optimisation, with what it bought (wall-clock of the named model on this machine, or
callgrind instructions of GameOfLife with N = 3):

| optimisation | effect |
|---|---|
| Symmetry: permutations as dense tables indexed by string id instead of hash maps; model-value comparison without thread-local access | Paxos 2.70 s -> 2.17 s |
| Symmetry: compare the cheapest variables first (by shallow size, which is the same for every state of an orbit), so most permutations are decided on a small function and the message set is never permuted | Paxos 2.17 s -> 1.75 s |
| Symmetry: memo of permuted compound values, keyed by (value hash, permutation) and confirmed by equality, bounded to 131072 entries | Paxos 1.75 s -> 0.64 s (0.7 s with the bound) |
| An operator parameter applied as a function (`Op(f, x) == f[x]`) is forced in keep-lazy mode, as TLC does: one point is computed, not the whole function. Also a correctness fix (`repro/LazyParam`) | GameOfLife 22.5 s -> 14.6 s |
| A lazy function evaluates its domain sets once | GameOfLife 14.6 s -> 13.1 s |
| A closed constant LET definition (no state, no free local name, only pure standard operators) is evaluated once per run; small filtered sets are stored enumerated | GameOfLife 13.1 s -> 11.9 s |
| Leaf fast paths in `eval`: state variable, constant, local bound to a plain value; scalar equality inline; tuples compared element-wise without recursion | GameOfLife 11.9 s -> 10.6 s (565 M -> 518 M instructions at N = 3) |
| Integer `+ - < > <= >=` computed inline instead of through the builtin call | 518 M -> 499 M |
| No memo for lazy functions that are not recursive; `f[x]` reads a state variable `f` directly | 499 M -> 477 M (9.4 s) |
| `CHOOSE x \in S : TRUE` returns the first element without binding | 477 M -> 468 M (8.9 s) |
| `S = {}` on an enumerated set without building an empty set | 468 M -> 447 M (8.7 s) |
| Scalar comparison inline in binary search; `f \in [D -> R]` compares the domain in place instead of building it as a set | SimpleRegular, MCBakery, MCLamportMutex: a few percent, within the noise when measured alone |

The mid rows moved by the generic items only: MCBakery 9.3 s -> 8.0 s, MCLamportMutex 14.4 s -> 11.7 s,
SimpleRegular 4.4 s -> 3.5 s, MCbtree 14.7 s -> 11.9 s, VoteProof 6.3 s -> 5.2 s, MCNanoMedium
13.9 s -> 13.6 s.

Tried without a measurable gain: the closed-LET cache alone did nothing for GameOfLife until the
filtered set was stored enumerated (a lazy filter keeps its context and was excluded from the
cache); interval fast paths in `for_bindings` and in function construction (earlier round).

**Not done.**

- *Slot-resolved identifiers.* The profiles put linked-context lookup at 3-5 %, so it would not
  have closed a row by itself; the leaf fast paths took the cheap part of it.
- *Avoiding a thunk per argument.* Literals and identifiers that are already bound are passed
  without a new thunk; other argument expressions still allocate one.
- *Compiling the AST to closures or bytecode.* This is what would move the flat rows (MCBakery,
  MCLamportMutex, MCNanoMedium, where the margin over TLC is 1.2-1.3x) substantially: per evaluated
  node the tree walk still costs 200-300 instructions including dispatch, result moves and
  reference counts.
- *Incremental fingerprints.* Compound values cache their hash, so an unchanged variable costs one
  addition per state already; fingerprinting is 3-7 %.

### Parallel BFS (`-workers N`): design note, not implemented

Values are `Rc`-based with `Cell` hash caches, the evaluator is a per-thread singleton, the AST
carries `Cell` / `RefCell` caches (resolution, levels, constant values, thunks), and string ids are
interned per thread in first-seen order, which also defines TLC's string ordering. Making all of
that `Arc` / atomic would slow the single-worker path (an estimate, not measured: 10-20 %) and is not
advisable. A sound design keeps the evaluator single-threaded and shares nothing but bytes:

1. One evaluator (interner, AST, caches) per worker thread, each parsing the spec itself.
2. A global string table (read-mostly lock) so that string ids, and with them value order and
   fingerprints, are the same in every worker; today fingerprints hash thread-local ids.
3. States cross threads in a serialized canonical form: a worker takes a serialized state from the
   shared queue, rebuilds its values locally, enumerates successors, fingerprints them, inserts into
   a sharded concurrent fingerprint set and pushes the new ones serialized.
4. Level-synchronized BFS (process one level in parallel, then a barrier), so that depth, the
   shortest counterexample and the state counts stay deterministic; parent pointers by fingerprint
   and trace reconstruction by re-execution, as TLC does.
5. Liveness needs the edge lists: per-worker buffers merged at the barrier. `TLCGet` / `TLCSet`
   registers, `Print` order and random choices become per-worker, as in TLC.
6. WebAssembly stays single-worker.

Cost: the serialization format, the global interner, id-independent fingerprints, the sharded set
and the driver; the evaluator is untouched. Scaling should be close to linear on evaluator-bound
models, less the (de)serialization per state.

## Conformance status

Real TLC is the arbiter. Everything below was run with the final binary unless noted.

| check | command | result |
|---|---|---|
| tlaplus/Examples manifest, runtime <= 5 s | `EVERYSTATE_CMD=target/release/everystate node scripts/conformance.mjs . --max-runtime 5 --timeout 120` from the Examples checkout | **122 / 122** |
| the same, runtime <= 60 s (incl. liveness) | `... --max-runtime 60 --timeout 600` | 161 / 161 (run before the last change of the performance pass, the bound on the permutation memo) |
| TLC `test-model` against live `tla2tools.jar` | `EVERYSTATE_CMD=target/release/everystate node scripts/diff-tlc.mjs <test-model>` | **384 / 414**, 4 skipped because TLC itself times out, 26 mismatches (below) |
| pstack statechart corpus through the Java shim | `EVERYSTATE_JAVA_CMD="target/release/everystate java" node scripts/statechart-corpus.mjs <scripts>` | **33 / 33** byte-identical |
| pretty-printer, 337 cases produced by Java | `node --experimental-strip-types --test test/pprint.test.ts` | all pass |
| community-module fixtures and upstream tests | `node test/community.mjs` | 21 / 21 |
| WebAssembly API (the six cases of `test/check.test.ts`) | `node --experimental-strip-types --test test/wasm.test.ts`, `bun test test/wasm.test.ts` | 6 / 6 each |

Notes on these runs:

- `scripts/conformance.mjs` passes `-Dtlc2.tool.impl.Tool.cdot=true` to the engine named by
  `EVERYSTATE_CMD`, as the Examples CI does for TLC on models with action composition: two Examples
  models assert that the property is set.
- `diff-tlc.mjs`: every TLC result comes from a fresh run of `tla2tools.jar` in this session (60 s
  limit, 2 jobs). The first complete run gave 383 with `pcal/Detlefs` timing out on the Rust side; the
  run with the final binary gave 384 with Detlefs passing. Detlefs needs 55-75 s here depending on
  load (60 s measured alone, TLC 38 s), so it sits on the 60 s limit and can go either way.
- The classification regex in `diff-tlc.mjs` was fixed: TLC 2026 prints "Temporal properties A and B
  were violated", which the old pattern did not recognise (five false mismatches).

### The 26 remaining `test-model` mismatches

| reason | count | specs | fixable? |
|---|---:|---|---|
| Result depends on a random seed (TLC's own counts differ from run to run) | 5 | `RandomElement`, `RandomElementXandY`, `RandomSubsetNext`, `SpanTreeRandom`, `Github648` | no |
| TLC bug reproduced by a test: strings are fingerprinted by their low bytes, so two distinct states collide | 3 | `Unicode*Fingerprint` | deliberately not: it would drop reachable states |
| Java class module override | 1 | `UserModuleOverride` | no |
| Labels and the full subexpression-selector syntax (`Op!lab(1)!:!++`, `!@`, `!<<`) | 4 | `suite/test206`, `test209`, `test219`, `test219a` | yes, parser and resolver work |
| Errors only SANY reports: non-Leibniz substitution, level of instantiation arguments, `HIDE` facts | 4 | `suite/test212`, `test213`, `test214`, `test217` | yes, semantic-analysis work |
| Suites of hundreds of assumptions on TLC's value internals (issue 1407): `[{} -> Nat] = {<<>>}`, equality and cardinality of non-enumerable sets, symbolic `kSubset`, fingerprints of symbolic sets | 3 | `EmptySetEqAssume` (about 190 of 443 fail), `ValueSemanticsAssume` (about 70 of 510), `KSubsetAssume` (at least 13 of 228) | yes, one rule at a time |
| TLC normalizes sets lazily, so a set mixing incomparable values is accepted until it is compared | 3 | `NormalizationAssume`, `NormalizationLiveness`, `NormalizationTLCSet` | needs unsorted set values; a design change |
| TLC checks safety-shaped temporal properties (`[](P => []Q)`) while it explores and reports a finite counterexample; everystate checks liveness after the search | 3 | `Github710b` (infinite state space, so everystate does not terminate), `Github710d`, `InitialLivenessEvaluationError` | needs the tableau product built during the search |

Fixed in this round, all confirmed against TLC: `VoteProof/MC` (AXIOM, step reference with
arguments), `cdot/*` (3), `PrintTraceException` (ALIAS), and the five regex false mismatches.

### Output that still differs from TLC 2026 by design

- A liveness violation is reported as "Temporal properties were violated." TLC 2026.11 names the
  violated properties ("Temporal property P was violated."). The banner claims TLC 2.19, whose text
  this is, and the statechart corpus requires exactly the old line (its `tlc.ts` matches it).
- TLC's warnings (symmetry with liveness, record field named like a variable, state-level PROPERTY) and
  the "Trace exploration spec path" line are not printed.

## Where everystate (Rust) follows TLC and the TypeScript engine does not

Each was checked against Java TLC; repro specs are in `repro/`
(`everystate repro/<Name>.tla`, `scripts/tlc.sh $PWD/repro/<Name>.tla <Name>.cfg`).

| repro | TLC and Rust | TypeScript engine |
|---|---|---|
| `LazyCup` | membership in a lazy union of `SUBSET (1..30)` is answered | fixed in `src/` meanwhile |
| `LazyUnion` | `UNION` of a non-enumerable set stays lazy | fixed in `src/` meanwhile |
| `LazyParam` | an operator parameter applied as a function is forced only at the point used | fixed in `src/` meanwhile |
| `MCBase` + `Base` | `Op <- Replacement` does not replace `Op` inside its own instance | fixed in `src/` meanwhile |
| `PrecConflict` | `SUBSET S \cup T` is a parse error ("Precedence conflict between ops ...") | accepted |
| `PrecConflict2` | `2 * -x` is a parse error: unary minus as right operand of an infix operator of precedence 13 or more | accepted |
| `StepRef` | a step reference with arguments, `<1>1!(v)`, parses | parse error |
| `AxiomSkip` | `AXIOM` is parsed and resolved but never evaluated; only `ASSUME` / `ASSUMPTION` are | evaluated, so the model fails |
| `Alias` | `ALIAS` is applied to every printed trace state: constructor field order, `_format`, `_ALIASEvalError`, the successor state for primed variables | `ALIAS` is ignored |
| (test-model `cdot/*`) | `\cdot` is an error unless `-Dtlc2.tool.impl.Tool.cdot=true` or `-cdot` is given | always on |
| (test-model `KSubsetAssume`, partly) | `kSubset(0, Nat)` is `{{}}`; k-subsets of one infinite base are ordered by k; a `kSubset` with millions of elements stays symbolic | enumerates or fails |

## Faster transitions (2026-11-18): data layout and evaluator structure, no result caches

Goal: actor-style specifications (replicas, a bag of messages, faults), where Feynman, a TypeScript model
checker with a cache of local steps, was 2 to 4 times faster. This pass makes each transition cheaper
by how values are built and looked up; it memoises nothing at run time.

What changed:

- **Bags and functions.** `(+)` and `(-)` merge the two sorted domains (a few elements against a bag:
  binary search and block copies) instead of a search per element and a re-sort; `make_fcn_from_pairs`
  does not sort sorted input; record comparison takes the scalar fast path per field and stops at once
  for the same shared value.
- **Fingerprints.** A state's fingerprint is `mix(sum over variables i of mix(word(value_i) xor (i+1)*K))`,
  the sum taken modulo 2^64, `mix` the splitmix64 finalizer, `word` a tagged scalar or the hash cached in a
  composite value. Strings and model values hash by their text, not by their intern number. Being a sum,
  a successor's fingerprint is its parent's with the terms of the changed variables replaced. It is 64 bits
  wide, as before, so the collision estimate printed at the end is computed as before.
- **Successors.** The variables of the successors of a state go into one reusable buffer; the fingerprint
  set is probed first and a state is allocated only when it is new. This applies when nothing else looks
  at a generated state (no CONSTRAINT, ACTION_CONSTRAINT, VIEW, SYMMETRY, action property, recorded graph);
  otherwise, and with `EVERYSTATE_ENGINE=classic`, every successor is allocated first, as before.
- **Evaluator.** No argument thunks for builtin operators reached by the enumerator; parameters bound
  without an argument vector; plain variables resolved without walking contexts; `UNCHANGED <<...>>` of
  unassigned variables is one copy, not a continuation per variable; a field of a record bound to a local
  name is passed as a value, not as a thunk; EXCEPT keys on the stack, no binding of `@` when the new
  value is a literal or a name.

Measured on the 4-core machine above, shared with other jobs (load average 2 to 3 throughout), so the unit
is CPU time (user + system) of the whole process, median of 5 runs, the builds run in turn within each
round (`scripts/bench-steps.py`; raw runs in `bench/steps-final.json.jsonl`). "before" is commit 31e8065.
Feynman (commit 80e674b, Bun) was measured on the same machine in the same hour
(`scripts/feynman-bench.ts`): for the larger models as a whole process, for the corpus configurations
in-process without start-up. Its own state count for LeaseLock is larger than the number of distinct TLA+
states (142,946 against 122,728); the table divides the TLA+ count by its time.

**The five larger models** (CPU seconds, median of 5)

| model | distinct | generated | before | after the evaluator step | final | final / before | RSS MB before / final | Feynman CPU s | states per CPU s: Feynman / before / final |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| OrSet-fixed-f1 | 129242 | 576193 | 1.73 | 1.45 | 1.40 | 0.81 | 105 / 108 | 1.46 | 88,373 / 74,620 / 92,382 |
| OrSet-fixed-f4 | 524832 | 2983987 | 7.65 | 6.32 | 6.29 | 0.82 | 385 / 394 | 3.62 | 145,025 / 68,614 / 83,386 |
| ReadRepair-fixed-f6 | 383579 | 2917394 | 7.56 | 5.50 | 5.49 | 0.73 | 226 / 235 | 2.55 | 150,183 / 50,765 / 69,894 |
| LostUpdate-fixed-f6 | 420646 | 2449693 | 6.12 | 4.57 | 4.61 | 0.75 | 225 / 231 | 2.45 | 171,836 / 68,744 / 91,246 |
| LeaseLock-fixed-f5 | 122728 | 732907 | 1.58 | 1.22 | 1.22 | 0.77 | 75 / 78 | 1.46 | 84,224 / 77,529 / 100,514 |
| **total** | | | 24.64 | 19.05 | 19.01 | 0.77 | | 11.54 | |

**The 11 Feynman corpus configurations with at least 5,000 states** (CPU seconds, median of 5)

| model | distinct | generated | before | after the evaluator step | final | final / before | RSS MB before / final | Feynman CPU s | states per CPU s: Feynman / before / final |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| LeaseLock-fixed-f1 | 15009 | 54229 | 0.13 | 0.11 | 0.11 | 0.80 | 17 / 18 | 0.12 | 121,056 / 113,705 / 141,594 |
| LeaseLock-buggy-f1 | 16318 | 56861 | 0.14 | 0.11 | 0.11 | 0.80 | 17 / 18 | 0.11 | 149,929 / 119,109 / 148,345 |
| OrSet-fixed-f0 | 39568 | 135877 | 0.48 | 0.39 | 0.41 | 0.86 | 41 / 44 | 0.26 | 149,417 / 82,952 / 96,273 |
| OrSet-fixed-f1 | 129242 | 576193 | 1.75 | 1.38 | 1.43 | 0.82 | 105 / 108 | 0.63 | 204,833 / 74,022 / 90,633 |
| OrSet-buggy-f1 | 7126 | 37008 | 0.08 | 0.06 | 0.07 | 0.81 | 14 / 14 | 0.02 | 285,143 / 89,075 / 109,631 |
| ReadRepair-fixed-f0 | 8972 | 39433 | 0.14 | 0.11 | 0.11 | 0.75 | 15 / 16 | 0.03 | 313,992 / 63,183 / 83,850 |
| ReadRepair-fixed-f1 | 37309 | 206097 | 0.70 | 0.48 | 0.47 | 0.67 | 31 / 32 | 0.12 | 309,940 / 53,375 / 79,720 |
| ReadRepair-buggy-f0 | 9332 | 40405 | 0.15 | 0.11 | 0.11 | 0.77 | 15 / 16 | 0.03 | 329,601 / 63,483 / 82,584 |
| ReadRepair-buggy-f1 | 38437 | 210309 | 0.66 | 0.48 | 0.49 | 0.74 | 31 / 32 | 0.13 | 303,219 / 57,974 / 78,124 |
| LostUpdate-fixed-f1 | 13926 | 35025 | 0.12 | 0.10 | 0.09 | 0.73 | 15 / 16 | 0.04 | 311,941 / 113,220 / 154,733 |
| LostUpdate-buggy-f1 | 22799 | 52425 | 0.18 | 0.14 | 0.14 | 0.80 | 21 / 22 | 0.07 | 325,951 / 128,084 / 160,556 |
| **total** | | | 4.52 | 3.46 | 3.53 | 0.78 | | 1.57 | |

**The 12 models of the table above** (CPU seconds, median of 5)

| model | distinct | generated | before | after the evaluator step | final | final / before | RSS MB before / final |
|---|---:|---:|---:|---:|---:|---:|---:|
| TCommit | 34 | 94 | 0.00 | 0.00 | 0.00 | 1.00 | 14 / 14 |
| ACP_SB_TLC | 54944 | 218352 | 0.36 | 0.34 | 0.34 | 0.95 | 27 / 28 |
| StaleShrinkV6Wait2x | 43348 | 111445 | 0.44 | 0.39 | 0.40 | 0.91 | 27 / 28 |
| Barriers | 29279 | 104515 | 2.46 | 2.43 | 2.46 | 1.00 | 19 / 20 |
| SimpleRegular | 277726 | 1454776 | 4.42 | 4.14 | 4.24 | 0.96 | 178 / 178 |
| Paxos | 1207 | 13290 | 0.80 | 0.76 | 0.77 | 0.97 | 51 / 52 |
| VoteProof | 6962 | 318877 | 7.14 | 6.79 | 6.83 | 0.96 | 15 / 15 |
| MCNanoMedium | 530587 | 1120079 | 18.83 | 17.91 | 18.02 | 0.96 | 615 / 615 |
| MCBakery | 655200 | 3403584 | 9.91 | 9.09 | 9.26 | 0.93 | 213 / 213 |
| MCLamportMutex | 724274 | 2729079 | 14.45 | 13.63 | 13.78 | 0.95 | 531 / 531 |
| MCbtree | 374727 | 2820091 | 15.42 | 14.93 | 14.97 | 0.97 | 193 / 192 |
| GameOfLife | 65536 | 131072 | 11.93 | 11.20 | 11.30 | 0.95 | 39 / 35 |
| **total** | | | 86.16 | 81.61 | 82.39 | 0.96 | |

Step by step, CPU seconds summed over each set (`bench/steps.json`, a separate series of 5 rounds):

| build | five larger models | 11 corpus configurations | 12 models of the table above |
|---|---:|---:|---:|
| before (31e8065) | 24.25 | 4.45 | 85.50 |
| bag merge, additive fingerprint, flat successors, first evaluator changes (3fcf9fc) | 20.43 | 3.80 | 85.03 |
| record comparison, bag updates by binary search, direct calls, UNCHANGED in one pass (153f501) | 18.92 | 3.52 | 81.38 |
| EXCEPT keys, named UNCHANGED tuples, estimator (af36110) | 18.80 | 3.50 | 83.14 |
| estimator moved off the hot path (final) | 19.01 | 3.53 | 82.39 |

(The last row is from the other series; in it the build of the third row measured 19.05, 3.46 and 81.61.)
Instructions executed (callgrind, deterministic), before and after: OrSet with no faults 3,197 M to
2,602 M (-19 %), ReadRepair with one fault 4,755 M to 3,525 M (-26 %), LostUpdate with one fault 815 M to
653 M (-20 %), LeaseLock with one fault 956 M to 770 M (-19 %).

**Where the time goes now** (share of instructions, OrSet / ReadRepair): walking expressions 30 % / 26 %;
the enumerator (conjunctions, UNCHANGED, assignment targets) 17 % / 19 %; operator application
(definitions, arguments, thunks, contexts) 9 % / 15 %; the allocator 13 % / 12 %; cloning and dropping
values 11 % / 12 %; value operations (comparison, bags, sets, functions) 10 % / 10 %; fingerprinting
6 % / 4 %; the checker's loop and fingerprint set 2 % / 3 %. One generated successor costs about 19,000
instructions on OrSet and 17,000 on ReadRepair, with about 30 and 25 allocations.

**The remaining gap to Feynman** in states per CPU second is 1.7x on OrSet (4 faults), 2.1x on ReadRepair,
1.9x on LostUpdate; everystate is ahead on LeaseLock. What remains is the tree walk itself, over half of
the instructions; allocation by layout (inline storage for short tuples, records and sets) would give about
3 %. Feynman is fast on these models because it does not evaluate at all in 99.3 to 99.99 % of its steps.

**How often a cache of local steps would hit.** `EVERYSTATE_CACHE_STATS=1` measures it without caching
anything: per action instance it notes what the evaluation reads (a variable, or one element for `f[k]`,
`DOMAIN f`, `x \in S`, `BagIn`, bag `(+)`/`(-)`, the `@` of an EXCEPT) and counts how often the same
(instance, bound values, reads) recurs. It is an upper bound (a value derived from part of a variable is
assumed to be used only as that variable's new value). `node scripts/cache-stats.mjs` tabulates it:

| models | estimated hit rate |
|---|---|
| the 11 corpus configurations with at least 5,000 states | 99.5 % to 99.96 % (OrSet f1: 1,321,006 evaluations, 1,964 keys) |
| all 125 corpus configurations | 99.64 % weighted by evaluations; 26 at 99 % or more, 38 between 95 and 99 %, 61 below 95 % (small models: few evaluations) |
| ACP_SB_TLC, Barriers, SimpleRegular, Paxos, MCBakery, MCLamportMutex, MCbtree | 99.0 % to 99.97 % |
| MCNanoMedium / StaleShrinkV6Wait2x / VoteProof | 93.7 % / 88.1 % / 82.8 % |
| GameOfLife (one action that reads the whole grid) | 0 % |
| 44 Examples models with at least 20,000 evaluations | 23 at 99 % or more, 9 between 95 and 99 %, 7 between 80 and 95 %, 5 below (MCCRDT 49 %, MCReplicatedLog 69 %, SlidingPuzzles, CoffeeCan, GameOfLife 0 %) |

**After merging parallel workers** (`main` at c1544c8): the fingerprint is the same in every thread
(string hashes are per-thread tables filled from the text), and the workers' expansion uses the same
flat path as the sequential loop. A third series on the same machine (`bench/steps-merged.json`, CPU
seconds summed, median of 5; this series ran on a faster host than the two above, compare within a row only):

| build | five larger models | 11 corpus configurations | 12 models of the table above |
|---|---:|---:|---:|
| before this pass (31e8065) | 19.17 | 3.55 | 65.40 |
| `main` with workers (c1544c8), 1 worker | 19.01 | 3.59 | 67.30 |
| merged, 1 worker | 15.02 | 2.75 | 63.16 |

No model of the 12 is slower than on `main` (Barriers 1.96 s to 2.00 s is within the noise; GameOfLife
9.11 s to 8.36 s, VoteProof 5.45 s to 5.32 s). With 4 workers (`bench/workers-ab.json`, wall seconds,
median of 3, `main` / merged): OrSet with 4 faults 2.16 / 1.90 (1 worker: 7.13 / 5.98), ReadRepair
2.07 / 1.61 (6.63 / 5.04), LostUpdate 1.64 / 1.38 (5.59 / 4.22), LeaseLock 0.47 / 0.40 (1.53 / 1.20):
the speed-up from 1 to 4 workers stays at 3.0 to 3.1 times.

## A compiled evaluator, and a bounded step cache as an experiment (2026-11-18)

Two switches. The compiled evaluator is the default from 0.4.0 (`EVERYSTATE_EVAL=tree` turns it off); the
step cache was off by default in 0.4.0 and is on by default after it (see the last section). The measurements below were taken with each selected explicitly.

- `EVERYSTATE_EVAL=compiled`: each top-level action and each invariant is turned, once
  before the search, into a tree of closures over a frame of slots (`src/compile.rs`). Identifiers are
  resolved to a state variable's index, a frame slot or a constant; definitions with value parameters are
  inlined, the parameters bound by name (an argument is evaluated where it is used, and kept for the rest
  of the call when it is a state-level expression, which is what the tree-walker's thunks do); the
  enumerator's work (which conjunct assigns which primed variable, which leave variables unchanged, where
  the branches are) is decided at compile time; `S \cup {e}`, `S \ {e}`, `B (+) SetToBag({e})` and
  `B (-) SetToBag({e})` update the set or bag without building the one-element value. Nothing is memoised
  across states. The tree-walker stays the reference: whatever the compiler does not handle is evaluated by
  it in a context rebuilt from the frame, an action that may reach an operator with an effect is not
  compiled at all, and when compiled code fails in any way its output for that action is discarded and
  the tree-walker evaluates the action again, so errors are the tree-walker's by construction. A plan that
  mostly falls back is switched off after 512 evaluations.
- `EVERYSTATE_STEP_CACHE=on` (default `off`; implies the compiled evaluator; `EVERYSTATE_STEP_CACHE_MB`,
  default 32): a cache of local steps (`src/stepcache.rs`). An entry holds, for one action instance, the
  values bound around it, everything its evaluation read of the state (a whole variable, one element
  `f[k]`, or whether a value is in a set or bag variable) and its successors as changes to the parent
  (unchanged, an element in or out of a set or bag, an EXCEPT at a path, or a value). A hit compares all of
  that in full. The table is direct-mapped with a fixed number of slots, every entry is charged its own
  size and that of every value it holds, an entry over 4 KB or over the budget is not stored, and a newer
  entry replaces the older one in its slot. With workers there is one table per worker (the budget is per
  worker). A unit whose hit rate over a window of 4096 lookups is under 75 % (50 % for the first window)
  is evaluated without the cache for a while, twice as long each time it fails again.

Same machine and method as above (CPU seconds, whole process, median of 5, the variants run in turn within
each round, load average 1.0; `bench/eval-cache-final.json`), Feynman measured in the same hour.

**The five larger models** (CPU seconds, median of 5; peak RSS in MB)

| model | distinct | tree | compiled | compiled + cache 32 MB | compiled / tree | RSS tree / compiled / cache | Feynman | states per CPU s: Feynman / tree / compiled / cache |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| OrSet-fixed-f1 | 129242 | 1.45 | 1.08 | 0.76 | 0.74 | 108 / 106 / 86 | 1.70 | 75,819 / 89,132 / 120,113 / 170,955 |
| OrSet-fixed-f4 | 524832 | 5.70 | 4.36 | 3.50 | 0.76 | 394 / 386 / 317 | 4.18 | 125,534 / 92,043 / 120,430 / 150,038 |
| ReadRepair-fixed-f6 | 383579 | 4.80 | 3.14 | 2.78 | 0.65 | 235 / 228 / 209 | 2.88 | 133,269 / 79,846 / 122,198 / 138,177 |
| LostUpdate-fixed-f6 | 420646 | 3.97 | 2.71 | 2.24 | 0.68 | 231 / 226 / 207 | 2.53 | 166,377 / 105,850 / 154,991 / 187,537 |
| LeaseLock-fixed-f5 | 122728 | 1.05 | 0.75 | 0.76 | 0.72 | 78 / 76 / 72 | 1.51 | 81,480 / 116,884 / 163,202 / 161,910 |
| **total** | | 16.98 | 12.04 | 10.03 | 0.71 | | 12.80 | |

**The 11 corpus configurations** (CPU seconds, median of 5; peak RSS in MB)

| model | distinct | tree | compiled | compiled + cache 32 MB | compiled / tree | RSS tree / compiled / cache | Feynman | states per CPU s: Feynman / tree / compiled / cache |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| LeaseLock-fixed-f1 | 15009 | 0.10 | 0.07 | 0.06 | 0.71 | 18 / 18 / 18 | 0.17 | 90,010 / 157,989 / 224,015 / 250,150 |
| LeaseLock-buggy-f1 | 16318 | 0.10 | 0.08 | 0.06 | 0.76 | 18 / 18 / 18 | 0.13 | 120,891 / 163,180 / 214,711 / 263,194 |
| OrSet-fixed-f0 | 39568 | 0.35 | 0.27 | 0.23 | 0.77 | 44 / 42 / 36 | 0.32 | 124,692 / 111,774 / 144,409 / 175,858 |
| OrSet-fixed-f1 | 129242 | 1.46 | 0.96 | 0.76 | 0.66 | 108 / 106 / 86 | 0.72 | 178,786 / 88,765 / 135,049 / 170,729 |
| OrSet-buggy-f1 | 7126 | 0.06 | 0.04 | 0.03 | 0.68 | 14 / 14 / 14 | 0.02 | 286,634 / 125,018 / 182,718 / 209,588 |
| ReadRepair-fixed-f0 | 8972 | 0.10 | 0.07 | 0.06 | 0.68 | 16 / 16 / 18 | 0.05 | 187,883 / 92,495 / 135,939 / 140,188 |
| ReadRepair-fixed-f1 | 37309 | 0.44 | 0.26 | 0.30 | 0.59 | 32 / 32 / 34 | 0.14 | 262,123 / 84,601 / 142,401 / 125,620 |
| ReadRepair-buggy-f0 | 9332 | 0.10 | 0.06 | 0.06 | 0.64 | 16 / 16 / 18 | 0.03 | 306,017 / 96,206 / 150,516 / 148,127 |
| ReadRepair-buggy-f1 | 38437 | 0.39 | 0.27 | 0.28 | 0.69 | 32 / 32 / 34 | 0.12 | 313,137 / 99,320 / 143,422 / 138,263 |
| LostUpdate-fixed-f1 | 13926 | 0.08 | 0.06 | 0.05 | 0.70 | 16 / 16 / 16 | 0.06 | 241,792 / 169,829 / 244,316 / 284,204 |
| LostUpdate-buggy-f1 | 22799 | 0.14 | 0.10 | 0.08 | 0.70 | 22 / 22 / 20 | 0.11 | 210,443 / 165,210 / 235,041 / 288,595 |
| **total** | | 3.30 | 2.23 | 1.97 | 0.67 | | 1.88 | |

**The 12 models of the first table** (CPU seconds, median of 5; peak RSS in MB)

| model | distinct | tree | compiled | compiled + cache 32 MB | compiled / tree | RSS tree / compiled / cache |
|---|---:|---:|---:|---:|---:|---:|
| TCommit | 34 | 0.01 | 0.01 | 0.01 | 1.00 | 13 / 13 / 13 |
| ACP_SB_TLC | 54944 | 0.34 | 0.30 | 0.28 | 0.89 | 28 / 28 / 28 |
| StaleShrinkV6Wait2x | 43348 | 0.34 | 0.28 | 0.30 | 0.84 | 28 / 28 / 30 |
| Barriers | 29279 | 2.06 | 1.86 | 1.90 | 0.90 | 20 / 20 / 22 |
| SimpleRegular | 277726 | 4.19 | 3.50 | 3.35 | 0.84 | 178 / 178 / 160 |
| Paxos | 1207 | 0.77 | 0.79 | 0.75 | 1.03 | 52 / 52 / 52 |
| VoteProof | 6962 | 5.67 | 5.53 | 5.61 | 0.98 | 16 / 16 / 18 |
| MCNanoMedium | 530587 | 15.34 | 15.16 | 14.81 | 0.99 | 616 / 616 / 617 |
| MCBakery | 655200 | 8.14 | 7.78 | 7.48 | 0.96 | 213 / 212 / 214 |
| MCLamportMutex | 724274 | 13.02 | 11.55 | 13.20 | 0.89 | 532 / 532 / 526 |
| MCbtree | 374727 | 12.39 | 11.17 | 12.04 | 0.90 | 193 / 193 / 185 |
| GameOfLife | 65536 | 9.07 | 9.05 | 9.09 | 1.00 | 36 / 36 / 37 |
| **total** | | 71.32 | 66.98 | 68.81 | 0.94 | |

**Cache budget** (CPU seconds, median of 5, a separate series): compiled, then the cache at 4 / 16 / 32 / 64 / 256 MB

| model | compiled | 4 MB | 16 MB | 32 MB | 64 MB | 256 MB |
|---|---:|---:|---:|---:|---:|---:|
| OrSet-fixed-f1 | 1.15 | 0.76 | 0.78 | 0.86 | 0.77 | 0.77 |
| OrSet-fixed-f4 | 4.64 | 3.65 | 3.46 | 3.34 | 3.42 | 3.44 |
| ReadRepair-fixed-f6 | 3.07 | 2.97 | 2.88 | 2.74 | 2.90 | 2.90 |
| LostUpdate-fixed-f6 | 2.81 | 2.27 | 2.21 | 2.30 | 2.15 | 2.23 |
| LeaseLock-fixed-f5 | 0.76 | 0.68 | 0.65 | 0.71 | 0.68 | 0.70 |

Per generated successor (callgrind): instructions and allocations, tree / compiled / compiled with the cache:
OrSet without faults 19,109 / 11,400 / 11,124 instructions and 27.8 / 15.0 / 13.1 allocations; ReadRepair with
one fault 17,036 / 9,198 / 9,274 and 24.5 / 9.4 / 10.1; LostUpdate with one fault 18,570 / 10,266 / 9,918 and
23.7 / 10.5 / 10.2. (On these small models the cache saves few instructions; its gain in CPU time on the
larger ones comes with a lower peak RSS, 317 MB against 386 MB on OrSet with 4 faults: a successor built
from a stored change shares more with its parent.)

What falls back in the compiled evaluator (evaluated by the tree-walker inside otherwise compiled code):
primed expressions other than `x' = e` / `x' \in S` / `UNCHANGED` on variables named directly; ENABLED,
`\cdot`, temporal operators; recursive operators and functions; operators passed as arguments, LAMBDA,
operator-valued parameters; instantiated definitions and substituted constants; subexpression selectors;
`f[x]` / `DOMAIN f` where `f` may be a function constructor (the tree-walker keeps it unevaluated);
function constructors with several bounds or over sets that are not enumerable; filters over sets that are
not explicit; `\A` in an action; `=>` and `\subseteq` in an action; conjuncts reached after every variable
is assigned. Fallback expressions per compiled evaluation on the 12 models: TCommit 0.35, ACP_SB_TLC 0.07, StaleShrinkV6Wait2x 0.52, Barriers 0.01, SimpleRegular 0.25, Paxos 5.8 (and
16 % of its evaluations by the tree-walker: plans switched off), VoteProof 0.79, MCNanoMedium 1.5 (33 % by the
tree-walker), MCBakery 0.00, MCLamportMutex 0.01 (4 % by the tree-walker), MCbtree 0.21 (2 %), GameOfLife:
its one action is switched off after 512 evaluations (99 % by the tree-walker). On OrSet and LostUpdate
there is no fallback at all, on ReadRepair 0.01 and on LeaseLock none. No compiled attempt had to be redone
by the tree-walker on any of these models.

The step cache on models where it cannot help (single runs, CPU seconds, compiled / with cache):
GameOfLife 9.05 / 9.09 (median of 5, 0 % hits), SlidingPuzzles 1.09 / 1.10 (median of 3; 4,096 lookups, no hit,
then the unit backs off), CoffeeCan100Beans 0.05 / 0.04 (16,384 lookups, no hit). Where the hit rate is
middling and the keys are large the cache costs time even with the back-off: MCLamportMutex 11.55 / 13.20
(+14 %), MCbtree 11.17 / 12.04 (+8 %).

## The step cache on by default (2026-11-19)

The step cache of the previous section is now on whenever the compiled evaluator is (`EVERYSTATE_STEP_CACHE=off`
turns it off; `EVERYSTATE_EVAL=tree` turns both off; `EVERYSTATE_STEP_CACHE=always` gives the cache to
every unit whether or not it pays, for testing). In the WebAssembly build it stays off: the decision below
needs a clock. The table is as before: fixed size, direct-mapped, 32 MB by default
(`EVERYSTATE_STEP_CACHE_MB`), one per worker, every hit compared in full.

What changed is how a unit (an action instance) gets the cache. The hit rate alone decided before, and that
was wrong both ways: a unit can hit 97 % of the time and still be dearer with the cache (MCLamportMutex,
MCbtree), and timing the unit alone misses most of the gain, which comes after the unit (a successor built
from a stored change shares values with its parent, so less is hashed, allocated and kept). So the cost is
measured, on the whole work per state:

- a unit first runs with the cache for 256 evaluations; if nothing could be stored in the first 32, or
  fewer than half of the 256 were hits, it is evaluated without the cache from then on (it is tried again
  after 4 million evaluations);
- then it is on trial: each state expanded is taken with or without the cache (a hash of the state's
  number decides, the same way for every unit on trial, so units tried together are judged on their joint
  effect), and the time from that expansion to the next is added to one of two means;
- the units get the cache when the mean with it is lower by 2.5 standard errors (looked at every 256
  states once there are 512 per side) or by one standard error after 4096 states per side; the trial ends
  without the cache when the mean with it is higher by 2.5 standard errors, higher at all after 1024 states
  per side, or not lower by one standard error after 4096;
- a unit with the cache goes on trial again after a million evaluations, or as soon as 4096 evaluations
  miss more than one time in five, and keeps the cache unless that trial goes against it; a unit without it
  is tried again after a million evaluations (or 16 times the length of its last trial, if that is more),
  later each time it fails again, up to 4 million.

No clock is read while no unit is on trial. A model too small for a trial (a few thousand states) runs
almost entirely without the cache. Because the decision depends on timing, which units have the cache can
differ from run to run; the states found, the counts and the traces do not (a hit yields exactly what the
evaluation would).

Same machine and method as above: CPU seconds of the whole process, median of 5, compiled without the cache
(`EVERYSTATE_STEP_CACHE=off`) and with it (the default) run in turn, one process at a time, load average 1.0
(`bench/cache-default.json`, `bench/examples-over-1s.json`, `bench/workers-cache.json`;
`scripts/bench-steps.py`, `scripts/bench-examples.py`, `scripts/bench-workers-ab.py`).

**The five larger models** (CPU seconds, median of 5; peak RSS in MB)

| model | distinct | compiled | compiled + cache | ratio | RSS compiled / cache |
|---|---:|---:|---:|---:|---:|
| OrSet-fixed-f1 | 129242 | 0.91 | 0.76 | 0.83 | 106 / 100 |
| OrSet-fixed-f4 | 524832 | 3.82 | 3.06 | 0.80 | 386 / 320 |
| ReadRepair-fixed-f6 | 383579 | 2.88 | 2.46 | 0.85 | 228 / 209 |
| LostUpdate-fixed-f6 | 420646 | 2.47 | 2.09 | 0.85 | 226 / 207 |
| LeaseLock-fixed-f5 | 122728 | 0.74 | 0.63 | 0.86 | 76 / 72 |
| **total** | | 10.81 | 9.00 | 0.833 | |

**The 11 corpus configurations** (CPU seconds, median of 5; peak RSS in MB)

| model | distinct | compiled | compiled + cache | ratio | RSS compiled / cache |
|---|---:|---:|---:|---:|---:|
| LeaseLock-fixed-f1 | 15009 | 0.07 | 0.06 | 0.88 | 18 / 18 |
| LeaseLock-buggy-f1 | 16318 | 0.07 | 0.06 | 0.91 | 18 / 18 |
| OrSet-fixed-f0 | 39568 | 0.26 | 0.26 | 1.00 | 42 / 44 |
| OrSet-fixed-f1 | 129242 | 0.93 | 0.76 | 0.82 | 106 / 88 |
| OrSet-buggy-f1 | 7126 | 0.04 | 0.03 | 0.85 | 14 / 14 |
| ReadRepair-fixed-f0 | 8972 | 0.06 | 0.06 | 1.05 | 16 / 16 |
| ReadRepair-fixed-f1 | 37309 | 0.23 | 0.26 | 1.14 | 32 / 34 |
| ReadRepair-buggy-f0 | 9332 | 0.06 | 0.06 | 1.03 | 16 / 16 |
| ReadRepair-buggy-f1 | 38437 | 0.25 | 0.25 | 1.00 | 32 / 34 |
| LostUpdate-fixed-f1 | 13926 | 0.05 | 0.05 | 0.87 | 16 / 16 |
| LostUpdate-buggy-f1 | 22799 | 0.09 | 0.07 | 0.80 | 22 / 20 |
| **total** | | 2.09 | 1.92 | 0.916 | |

**The 12 models of the first table** (CPU seconds, median of 5; peak RSS in MB)

| model | distinct | compiled | compiled + cache | ratio | RSS compiled / cache |
|---|---:|---:|---:|---:|---:|
| TCommit | 34 | 0.01 | 0.00 | 0.80 | 14 / 14 |
| ACP_SB_TLC | 54944 | 0.27 | 0.27 | 0.98 | 28 / 28 |
| StaleShrinkV6Wait2x | 43348 | 0.26 | 0.27 | 1.02 | 28 / 28 |
| Barriers | 29279 | 1.78 | 1.79 | 1.01 | 21 / 22 |
| SimpleRegular | 277726 | 3.22 | 3.02 | 0.94 | 178 / 179 |
| Paxos | 1207 | 0.71 | 0.68 | 0.96 | 52 / 52 |
| VoteProof | 6962 | 5.09 | 5.03 | 0.99 | 16 / 18 |
| MCNanoMedium | 530587 | 13.02 | 12.80 | 0.98 | 616 / 617 |
| MCBakery | 655200 | 6.87 | 6.87 | 1.00 | 213 / 214 |
| MCLamportMutex | 724274 | 9.78 | 10.13 | 1.04 | 532 / 533 |
| MCbtree | 374727 | 10.10 | 10.28 | 1.02 | 193 / 193 |
| GameOfLife | 65536 | 8.36 | 8.55 | 1.02 | 36 / 37 |
| **total** | | 59.46 | 59.68 | 1.004 | |

**Examples gate models over 1 s** (CPU seconds, median of 5, worst ratio first; peak RSS in MB)

| model | distinct | compiled | compiled + cache | ratio | RSS compiled / cache |
|---|---:|---:|---:|---:|---:|
| MCBinarySearch | 27953 | 0.92 | 0.95 | 1.035 | 120 / 122 |
| GameOfLife | 65536 | 8.49 | 8.65 | 1.019 | 36 / 37 |
| VoteProof | 6962 | 5.12 | 5.21 | 1.018 | 16 / 18 |
| MCCRDT | 25000 | 4.34 | 4.41 | 1.015 | 38 / 42 |
| Barriers | 29279 | 1.81 | 1.81 | 0.997 | 21 / 23 |
| YoYoAllGraphs | 26731 | 2.12 | 2.11 | 0.996 | 48 / 48 |
| MCQuicksort | 4548 | 2.61 | 2.59 | 0.995 | 15 / 17 |
| SpanTreeRandom | 65396 | 2.78 | 2.69 | 0.968 | 80 / 82 |
| SimpleRegular | 277726 | 3.31 | 3.10 | 0.937 | 178 / 178 |

**1 and 4 workers** (wall seconds / CPU seconds / peak RSS in MB, median of 5)

| model | 1 worker, compiled | 1 worker, cache | 4 workers, compiled | 4 workers, cache | wall 4 workers: cache / compiled |
|---|---:|---:|---:|---:|---:|
| OrSet-fixed-f4 | 3.91 / 3.88 / 386 | 3.15 / 3.12 / 317 | 1.34 / 4.49 / 261 | 1.33 / 4.45 / 267 | 0.99 |
| ReadRepair-fixed-f6 | 2.86 / 2.86 / 228 | 2.57 / 2.53 / 209 | 0.96 / 3.24 / 175 | 0.91 / 3.04 / 195 | 0.95 |
| LostUpdate-fixed-f6 | 2.72 / 2.69 / 226 | 2.14 / 2.13 / 208 | 0.82 / 2.80 / 156 | 0.74 / 2.45 / 156 | 0.90 |
| LeaseLock-fixed-f5 | 0.74 / 0.73 / 76 | 0.63 / 0.63 / 72 | 0.29 / 0.81 / 77 | 0.26 / 0.73 / 77 | 0.90 |
| MCBakery | 7.37 / 7.27 / 213 | 6.91 / 6.85 / 214 | 3.75 / 7.91 / 356 | 3.83 / 7.82 / 366 | 1.02 |
| SimpleRegular | 3.24 / 3.19 / 178 | 3.03 / 3.02 / 162 | 1.46 / 5.13 / 146 | 1.51 / 5.26 / 150 | 1.03 |
| VoteProof | 5.13 / 5.11 / 16 | 5.08 / 5.03 / 18 | 1.62 / 5.30 / 46 | 1.57 / 5.14 / 48 | 0.97 |

Single runs on this machine vary by about ±4 % and medians of 5 by about ±2 to 3 % (GameOfLife, where the
cache does nothing at all after the first 512 evaluations, reads between 0.99 and 1.02 from series to
series). The models that read above 1.02 in one of the tables were measured again alone, the two variants
alternating: MCLamportMutex 10.18 / 9.98 (0.98, 8 runs each), MCbtree 10.06 / 10.16 (1.01, 6 runs),
GameOfLife 8.69 / 8.64 (0.995, 8 runs), MCBinarySearch 0.93 / 0.95 (1.02, 10 runs), YoYoAllGraphs
2.10 / 2.10 (1.00, 10 runs). The configurations of the 11 that take under 0.1 s are below what this
measurement resolves.

Memory: the table is allocated per worker and touched only as entries are stored, so the bound with
`-workers 4` is 4 x 32 MB above the run without the cache; measured, peak RSS with 4 workers is between
equal and 20 MB higher (ReadRepair with 6 faults 175 -> 195 MB, MCBakery 356 -> 366 MB), and with one
worker it is lower on the actor models (OrSet with 4 faults 386 -> 320 MB) and within 4 MB elsewhere.
With 4 workers each worker measures its own units on its own share of the states, so the gain is smaller
than with one.
