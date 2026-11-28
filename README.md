# everystate

A TLA+ model checker with no Java dependency, written in Rust. It reads ordinary `.tla` specs and
TLC `.cfg` files, checks every reachable state, and reports results in TLC's format.

```text
> use everystate's formal verification skill to find race conditions in my amazing software

⏺ Write(Store.tla)
  // ... models load() and save() from store.ts

⏺ Bash(npx everystate Store.tla)

  Error: Invariant NoLostUpdates is violated.
  State 2: <Load("a")>   a read 0
  State 3: <Load("b")>   b read 0
  State 4: <Save("a")>   memory = 1
  State 5: <Save("b")>   memory = 1

⏺ Found a race. Two overlapping requests both load before either saves,
  so one update is lost. Fix: make load-and-save atomic.
```

(Condensed. The spec is [`examples/Store.tla`](examples/Store.tla); the skill is
[`skills/formal-verification`](skills/formal-verification/SKILL.md).)

- Safety and liveness checking, fairness, symmetry, `VIEW`, `ALIAS`.
- TLC-compatible text output, exit codes, `-tool` framing and `-dump`.
- Random simulation (`-simulate`) for models too large to enumerate, with seeded, reproducible runs.
- Trace conformance (`everystate conform`): check a log of the real system against the spec.
- Parallel search (`-workers N`) with results identical to one worker.
- A PlusCal translator (`everystate pcal`) with the Java translator's output, byte for byte.
- The standard and community modules are built in.
- One native binary, or WebAssembly for Node, Bun and workers.

## Install

```sh
npm install -g everystate     # prebuilt binary for Linux, macOS and Windows
brew install mattzcarey/tap/everystate
cargo install everystate      # or build from source
```

## Example

`examples/Counter.tla`:

```tla
---- MODULE Counter ----
EXTENDS Naturals
VARIABLE n

Init == n = 0
Next == n < 5 /\ n' = n + 1
Spec == Init /\ [][Next]_n

TypeOK   == n \in 0..5
NeverFour == n /= 4
====
```

`examples/Counter.cfg`:

```
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT NeverFour
CHECK_DEADLOCK FALSE
```

```sh
everystate examples/Counter.tla
```

```
Error: Invariant NeverFour is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
n = 0

State 2: <Next line 6, col 9 to line 6, col 27 of module Counter>
n = 1
...
State 5: <Next line 6, col 9 to line 6, col 27 of module Counter>
n = 4

5 states generated, 5 distinct states found, 0 states left on queue.
```

Exit status is 12, as with TLC.

### For scripts and agents

```sh
everystate -json examples/Counter.tla
```

```json
{"status":"invariant","name":"NeverFour","generated":5,"distinct":5,"queue":0,"depth":5,
 "trace":[{"action":null,"state":{"n":"0"}},{"action":"Next","state":{"n":"1"}}, ...]}
```

### From JavaScript (WebAssembly)

The npm package also exports the engine compiled to WebAssembly:

```ts
import { check } from 'everystate';

const { result } = check({
  root: 'Counter',
  modules: { Counter: tlaSource },
  config: 'SPECIFICATION Spec\nINVARIANT NeverFour\nCHECK_DEADLOCK FALSE',
});
result.status;   // 'invariant'
result.name;     // 'NeverFour'
```

`checkAsync` runs the same check in a worker with a large stack, for deeply recursive specs.
The WebAssembly build is about 2x slower than native and cannot use the file-based community
operators.

## Multiple workers

`-workers N` (or `-workers auto`, one per core) searches on N threads in the native binary. State
counts, depth, verdict and the counterexample are the same as with one worker. Operators whose
effect depends on exploration order (`Print`, `TLCSet`/`TLCGet` registers, `RandomElement`,
IOUtils, ...) are evaluated by the sequential search; if they occur repeatedly the run continues
with one worker and says so. Liveness checking, simulation and `conform` run on one thread, and
the WebAssembly build is single-threaded.

## Simulation

When a model is too large to enumerate, `everystate -simulate num=10000 Spec.tla` generates random
behaviours of up to `-depth` steps (default 100) and checks invariants, action properties, deadlock
and temporal properties on each, printing TLC's simulation output. A pass means only that no
generated behaviour violates a property. Without `num=` it runs until it finds an error, as TLC
does; with `-json` it stops after 1000 behaviours. Every run prints its seed; pass it back with
`-seed` to repeat the run exactly. From JavaScript:
`check({ root, modules, config, simulate: { traces: 10000, seed: 1 } })`.

Two differences from TLC: a deadlock is reported only for a state with no successor (TLC's
simulator also reports one when a `CONSTRAINT` excludes every successor), and a state predicate
given as `PROPERTY` is checked on the initial states (TLC's simulator skips it). Random choices
differ from Java TLC's, so the same seed gives a different run there.

## PlusCal

`everystate pcal` translates the PlusCal algorithm in a module with the output of the Java
translator (`pcal.trans` 1.12): the same TLA+, layout and checksums, the same `.old` backup and
`.cfg` handling, the same options (`-wf`, `-sf`, `-wfNext`, `-nof`, `-termination`, `-label`,
`-labelRoot`, `-lineWidth`, ... and the `PlusCal options (...)` line), in p-syntax and c-syntax.

```tla
---- MODULE Transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice = 10, bob = 10, money \in 1..20;
begin
  Withdraw: alice := alice - money;
  Deposit:  bob := bob + money;
  Check:    assert alice >= 0;
end algorithm *)
====
```

```sh
everystate pcal Transfer.tla     # writes the translation into Transfer.tla, and Transfer.cfg
everystate Transfer.tla          # "Failure of assertion at line 9, column 13."
```

When a module is model-checked and its algorithm or translation no longer matches the checksums
in the `\* BEGIN TRANSLATION` line, everystate prints TLC's warning; `everystate pcal --check
File.tla` reports the same without checking a model. From JavaScript,
`translatePlusCal(source, options)` translates the text of a module. `-spec` and `-myspec` are not
supported. `npm run conformance:pcal` compares the translator with the Java one.

## Check the code against the model

A pass verifies the model. To check that the running code behaves like it, log what the code does
and ask whether that run is a behaviour of the spec:

```sh
everystate conform -trace run.jsonl Charge.tla
```

```
{"state": {"sent": 0, "charges": 0}}
{"action": "Send", "state": {"sent": 1}}
{"action": "Handle", "state": {"charges": 2}}
```

Each line is a step: optionally the action, and whichever variables the code knows. The report
names the first line the spec does not allow, what it expected, and which steps were possible
there. Exit status 0 conforms, 20 does not (21 bad trace, 22 limit reached). `-hidden N` allows
unlogged steps, `-stutter` snapshots, `-behavior` prints a full matching behaviour, `-json`
structured output. From JavaScript: `conform({ root, modules, config, trace })`. Details are in
the [skill](skills/formal-verification/SKILL.md).

## Agent skill

[`skills/formal-verification`](skills/formal-verification/SKILL.md) teaches a coding agent to
model-check a design with everystate: choose the promise, model the steps, run the check, see it
fail, report the counterexample in the code's words. It comes with a worked example
(`example/Charge.tla`). Copy the folder into your agent's skills directory, for example
`.claude/skills/`.

## Options

```
everystate [options] SPEC[.tla]
  -config FILE     configuration file (default: SPEC.cfg)
  -deadlock        do not check for deadlock
  -json            one JSON result object
  -tool            TLC's machine-readable message framing
  -dump dot,actionlabels FILE   write the state graph
```

Exit status: 0 success, 10 assumption, 11 deadlock, 12 safety, 13 liveness, 150 parse error,
151 config error.

Environment: actions and invariants are compiled before the search, and a cache of local steps
reuses work between states that agree on what a step reads (a fixed-size table, 32 MB per worker,
`EVERYSTATE_STEP_CACHE_MB`; used only where it measures faster during the run). Results are the
same either way. `EVERYSTATE_STEP_CACHE=off` turns the cache off; `EVERYSTATE_EVAL=tree` uses the
tree-walking interpreter alone.

## How it is checked

Real TLC is the reference (details in [CONFORMANCE.md](CONFORMANCE.md)):

- [tlaplus/Examples](https://github.com/tlaplus/Examples), models up to 5 s: 122 of 122 match on
  result and exact state counts.
- TLC's own `test-model` suite, run side by side with `tla2tools.jar`: 383 of 414 match.
- pstack `statechart` corpus: 33 of 33 outputs byte-identical.

## Speed

Wall-clock seconds for the whole process on a 4-core Linux machine, median of 3, against Java TLC
and [tla-ts](https://github.com/aidenybai/tla-ts) 0.0.10 (run by Node). The first three models are
tla-ts's own benchmarks. All three checkers report the same state counts.

| Model | Distinct states | everystate | tla-ts | TLC |
|---|---:|---:|---:|---:|
| Commit | 282,251 | 3.49 | 5.83 | 6.69 |
| Philosophers | 128,889 | 0.79 | 1.75 | 2.01 |
| Queue | 44,044 | 0.08 | 0.52 | 0.89 |
| Paxos | 1,207 | 0.72 | 4.31 | 1.81 |
| MCBakery | 655,200 | 7.29 | 16.34 | 10.65 |
| MCLamportMutex | 724,274 | 10.48 | 21.57 | 14.18 |
| MCbtree | 374,727 | 10.43 | 13.41 | 30.75 |
| MCLamportMutex, 4 workers | 724,274 | 3.28 | 20.87 | 9.08 |
| MCbtree, 4 workers | 374,727 | 3.88 | 14.30 | 11.71 |
| 122 tlaplus/Examples models | | 43.1 | 151.1 | 179.6 |

With one worker everystate is 1.3x to 6.7x faster than tla-ts and 1.2x to 11.6x faster than TLC on
the 14 models that run long enough to measure, and uses less memory than TLC on all of them. All 15
models, four-worker results, memory and the method are in [BENCHMARK.md](BENCHMARK.md).

## Not supported

Disk-backed state storage (everything is in memory, so a few
million distinct states is the practical limit), Java module overrides, labels and subexpression selectors, and TLAPS proof checking (proofs
are parsed and skipped).

## Development

```sh
npm run build      # native binary and wasm/everystate.wasm
npm test           # WASM API, pretty-printer and community-module tests
```

Releases use [changesets](.changeset/README.md): add one with `npx changeset` in your pull request,
then merge the "Version Packages" pull request that appears. That bumps `package.json` and
`Cargo.toml`, and `.github/workflows/release.yml` builds the binaries and publishes to npm and
crates.io (trusted publishing, no tokens).

An earlier pure-TypeScript engine is in the git history at commit `e8c67ce` (npm `everystate@0.1.0`).

## License

MIT
