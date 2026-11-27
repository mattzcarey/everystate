#!/usr/bin/env node
// everystate against tla-ts (npm, run by Node) and Java TLC: same models, same machine, one process at a time.
//
// usage: node scripts/bench-vs.mjs [--runs 3] [--parts single,workers,corpus] [--out bench/vs.jsonl] [--only STR]
//
//   single   15 models, 1 worker: median wall seconds and peak RSS of the whole process
//   workers  the larger of those with 4 workers
//   corpus   every exhaustive model of tlaplus/Examples recorded at up to 5 s, one run per engine
//
// Results are appended to --out as they come, and a run found there is not repeated, so the script can be
// restarted. Paths: EXAMPLES (tlaplus/Examples), TLA_TS_BIN (node_modules/.bin/tla-ts), TLA_TS_BENCH (the
// benchmarks directory of the tla-ts repository), TLA2TOOLS, TLA_LIBRARY.
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
const here = path.resolve(import.meta.dirname, '..');
const env = (n, d) => process.env[n] ?? d;
const EX = env('EXAMPLES', '/home/user/refs/Examples');
const TT = env('TLA_TS_BENCH', '/home/user/refs/tla-ts/packages/tla-ts/benchmarks');
const TLA_TS = env('TLA_TS_BIN', '/home/user/refs/tla-ts-npm/node_modules/.bin/tla-ts');
const JAR = env('TLA2TOOLS', '/home/user/refs/tla2tools.jar') + ':' + env('TLA_DEPS', '/home/user/refs/CommunityModules-deps.jar');
const LIB = env('TLA_LIBRARY', '/home/user/refs/tlapm/library:/home/user/refs/CommunityModules/modules');
const args = process.argv.slice(2);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const RUNS = Number(opt('--runs', 3)), PARTS = opt('--parts', 'single,workers,corpus').split(','), ONLY = opt('--only', '');
const OUT = path.resolve(opt('--out', path.join(here, 'bench/vs.jsonl')));
const TIMEOUT = Number(opt('--timeout', 600));
// tla-ts takes library directories and Java properties only in its "java ... tlc2.TLC" form
const CDOT = '-Dtlc2.tool.impl.Tool.cdot=true'; // action composition, which the Examples CI enables
const ENGINES = {
  everystate: (w, c, s, x) => [path.join(here, 'target/release/everystate'), ...x, '-workers', String(w), '-config', c, s],
  'tla-ts': (w, c, s, x) => ['node', TLA_TS, '-cp', JAR, '-DTLA-Library=' + LIB, ...x, 'tlc2.TLC', '-workers', String(w), '-config', c, s],
  tlc: (w, c, s, x) => ['java', '-XX:+UseParallelGC', '-cp', JAR, '-DTLA-Library=' + LIB, ...x, 'tlc2.TLC', '-workers', String(w), '-config', c, s],
};
const ex = (c, s) => [path.join(EX, 'specifications', path.dirname(c)), path.basename(c), path.basename(s)];
const SINGLE = [
  [path.join(TT, 'commit'), 'Commit.cfg', 'Commit.tla'], [path.join(TT, 'philosophers'), 'Philosophers.cfg', 'Philosophers.tla'], [path.join(TT, 'queue'), 'Queue.cfg', 'Queue.tla'],
  ex('transaction_commit/TCommit.cfg', 'TCommit.tla'), ex('acp/ACP_SB_TLC.cfg', 'ACP_SB_TLC.tla'), ex('StaleViewShrink/StaleShrinkV6Wait2x.cfg', 'StaleShrink.tla'),
  ex('barriers/Barriers.cfg', 'Barriers.tla'), ex('TeachingConcurrency/SimpleRegular.cfg', 'SimpleRegular.tla'), ex('SimplifiedFastPaxos/Paxos.cfg', 'Paxos.tla'),
  ex('byzpaxos/VoteProof.cfg', 'VoteProof.tla'), ex('NanoBlockchain/MCNanoMedium.cfg', 'MCNano.tla'), ex('Bakery-Boulangerie/MCBakery.cfg', 'MCBakery.tla'),
  ex('lamport_mutex/MCLamportMutex.cfg', 'MCLamportMutex.tla'), ex('btree/MCbtree.cfg', 'MCbtree.tla'), ex('GameOfLife/GameOfLife.cfg', 'GameOfLife.tla'),
];
const WORKERS = ['Commit', 'SimpleRegular', 'VoteProof', 'MCNanoMedium', 'MCBakery', 'MCLamportMutex', 'MCbtree', 'GameOfLife'];

// one run: wall seconds and peak RSS (MB) through a small Python wrapper, which reads the child's rusage
const PY = `import subprocess,sys,time,resource,json
t=time.time()
try:
    p=subprocess.run(sys.argv[2:],capture_output=True,timeout=float(sys.argv[1]),errors='replace'); o=p.stdout+p.stderr; rc=p.returncode
except subprocess.TimeoutExpired as e:
    o=''; rc=None
print(json.dumps({'wall':time.time()-t,'rss':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss/1024,'rc':rc,'out':o[-6000:]}))`;
const done = new Map();
if (fs.existsSync(OUT)) for (const l of fs.readFileSync(OUT, 'utf8').split('\n')) if (l) { const r = JSON.parse(l); done.set(r.key, r); }
fs.mkdirSync(path.dirname(OUT), { recursive: true });
function run(part, engine, w, dir, cfg, spec, i, extra = []) {
  const key = [part, engine, w, path.resolve(dir, cfg), i].join('|');
  if (done.has(key)) return done.get(key);
  const p = spawnSync('python3', ['-c', PY, String(TIMEOUT), ...ENGINES[engine](w, cfg, spec, extra)], { cwd: dir, encoding: 'utf8', maxBuffer: 1 << 26, env: { ...process.env, JAVA_TOOL_OPTIONS: '' } });
  let r; try { r = JSON.parse(p.stdout); } catch { r = { wall: 0, rss: 0, rc: -1, out: p.stderr ?? '' }; }
  const num = re => { const m = [...r.out.matchAll(re)]; return m.length ? Number(m.at(-1)[1]) : null; };
  const rec = { key, part, engine, workers: w, model: path.basename(cfg, '.cfg'), wall: r.wall, rss: r.rss, rc: r.rc, distinct: num(/(\d+) distinct states found/g), generated: num(/(\d+) states generated/g),
    kind: r.rc === null ? 'timeout' : ({ 0: 'success', 10: 'assumption failure', 11: 'deadlock failure', 12: 'safety failure', 13: 'liveness failure' }[r.rc] ?? 'error') };
  fs.appendFileSync(OUT, JSON.stringify(rec) + '\n'); done.set(key, rec);
  process.stderr.write(`${part} ${rec.model} ${engine} w${w} #${i}: ${rec.wall.toFixed(2)}s ${rec.rss.toFixed(0)}MB distinct=${rec.distinct} ${rec.kind}\n`);
  return rec;
}
const median = a => { const s = [...a].sort((x, y) => x - y); return s[s.length >> 1]; };
const names = Object.keys(ENGINES);
function table(part, models, w) {
  console.log(`| model | distinct | everystate s | tla-ts s | TLC s | faster than tla-ts | faster than TLC | RSS MB everystate / tla-ts / TLC | counts agree |\n|---|---:|---:|---:|---:|---:|---:|---:|---|`);
  for (const [dir, cfg, spec] of models) {
    if (ONLY && !cfg.includes(ONLY)) continue;
    const r = {};
    for (const e of names) {
      const runs = []; for (let i = 0; i < RUNS; i++) { const x = run(part, e, w, dir, cfg, spec, i); runs.push(x); if (x.kind === 'timeout' || x.kind === 'error') break; }
      r[e] = { t: median(runs.map(x => x.wall)), rss: Math.max(...runs.map(x => x.rss)), d: runs[0].distinct, bad: runs.find(x => x.kind === 'timeout' || x.kind === 'error')?.kind };
    }
    const f = x => x.bad ?? x.t.toFixed(2), q = x => x.bad || r.everystate.bad ? 'n/a' : (x.t / r.everystate.t).toFixed(1) + 'x';
    const same = names.every(e => r[e].bad || r[e].d === r.everystate.d);
    console.log(`| ${cfg.replace('.cfg', '')} | ${r.everystate.d} | ${f(r.everystate)} | ${f(r['tla-ts'])} | ${f(r.tlc)} | ${q(r['tla-ts'])} | ${q(r.tlc)} | ${names.map(e => r[e].rss.toFixed(0)).join(' / ')} | ${same ? 'yes' : 'no: ' + names.map(e => r[e].d).join(' / ')} |`);
  }
}
if (PARTS.includes('single')) { console.log(`\n### One worker (median of ${RUNS})\n`); table('single', SINGLE, 1); }
if (PARTS.includes('workers')) { console.log(`\n### Four workers (median of ${RUNS})\n`); table('workers', SINGLE.filter(m => WORKERS.includes(m[1].replace('.cfg', ''))), 4); }
if (PARTS.includes('corpus')) {
  const secs = r => r === 'unknown' ? 1e9 : r.split(':').reduce((a, x) => a * 60 + Number(x), 0);
  const cases = [];
  for (const d of fs.readdirSync(path.join(EX, 'specifications')).sort()) {
    const mf = path.join(EX, 'specifications', d, 'manifest.json'); if (!fs.existsSync(mf)) continue;
    for (const mod of JSON.parse(fs.readFileSync(mf, 'utf8')).modules) for (const m of mod.models) {
      if (m.mode !== 'exhaustive search' || secs(m.runtime) > 5 || m.result === 'unknown') continue;
      if (ONLY && !m.path.includes(ONLY)) continue;
      cases.push({ dir: EX, cfg: path.join(EX, m.path), spec: path.join(EX, mod.path), exp: m }); // run as the Examples CI does: from the root
    }
  }
  const tot = Object.fromEntries(names.map(e => [e, { t: 0, ok: 0, wrong: [], common: 0 }]));
  for (const c of cases) {
    const rs = Object.fromEntries(names.map(e => [e, run('corpus', e, 1, c.dir, c.cfg, c.spec, 0, [CDOT])]));
    const good = r => r.kind === c.exp.result && (c.exp.distinctStates == null || c.exp.result !== 'success' || r.distinct === c.exp.distinctStates);
    for (const e of names) { tot[e].t += rs[e].wall; if (good(rs[e])) tot[e].ok++; else tot[e].wrong.push(`${path.relative(path.join(EX, 'specifications'), c.cfg).replace('.cfg', '')} (${rs[e].kind}${rs[e].distinct != null ? ', ' + rs[e].distinct + ' distinct' : ''})`); }
    if (names.every(e => good(rs[e]))) for (const e of names) tot[e].common += rs[e].wall;
  }
  console.log(`\n### tlaplus/Examples, ${cases.length} models recorded at up to 5 s (one run each, 1 worker)\n`);
  console.log('| engine | result and distinct count as recorded | total s, all models | total s, models all three get right |\n|---|---:|---:|---:|');
  for (const e of names) console.log(`| ${e} | ${tot[e].ok} of ${cases.length} | ${tot[e].t.toFixed(1)} | ${tot[e].common.toFixed(1)} |`);
  for (const e of names) if (tot[e].wrong.length) console.log(`\n${e} differs on: ${tot[e].wrong.join('; ')}`);
}
