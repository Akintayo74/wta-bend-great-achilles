// Compare the two point-model formulas on the same players (SPEC.md, Point
// model), and check the matchup entry point against the exact calculator.
//
// Run: node prep/compare.ts [--simulate] [--bits 20] [--seed 20261108]
//
// 1. For every pair of players in data/players.csv, the exact calculator
//    gives the chance the first wins a best-of-three match under each
//    formula, from the same whole-number chances that go into params.bend.
//    Prints how far apart the two formulas are, and writes every pair to
//    results/compare-<window end>.csv (not committed).
// 2. With --simulate, builds build/matchup and plays a few match-ups with
//    the published seed, checking that the engine read the right chances
//    from params.bend (A's serving to B, B's serving to A), that it agrees
//    with the exact calculator within 0.2 points, that no match is
//    unfinished, that swapping the players swaps the result, that a player
//    against herself is close to 50/50, and that a rerun is identical.

import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { match } from "./exact.ts";
import { type Method, METHODS } from "./model.ts";
import { build, PARAMS } from "./params.ts";

const arg = (name: string, dflt: number): number => {
  const i = process.argv.indexOf(`--${name}`);
  return i >= 0 ? Number(process.argv[i + 1]) : dflt;
};
const BITS = arg("bits", 20);
const SEED = arg("seed", 20261108);
const RUNS = 2 ** BITS;
const TOLERANCE = 0.2; // percentage points
const BIN = "build/matchup";

const { text, problems, inputs, chances } = build(readFileSync("data/players.csv", "utf8"), readFileSync("data/tour.csv", "utf8"));
if (!text || !inputs || !chances) {
  console.error(`inputs have problems:\n  ${problems.join("\n  ")}`);
  process.exit(1);
}
if (readFileSync(PARAMS, "utf8") !== text) {
  console.error(`${PARAMS} is out of date: run node prep/params.ts`);
  process.exit(1);
}
const ps = inputs.players;
const pct = (x: number, d = 1) => (100 * x).toFixed(d);

// 1. Every pair, both formulas, exactly.
type Pair = { i: number; j: number; win: Record<Method, number> };
const pairs: Pair[] = [];
for (let i = 0; i < ps.length; i++) {
  for (let j = i + 1; j < ps.length; j++) {
    const win = {} as Record<Method, number>;
    for (const m of METHODS) win[m] = match(chances[m][i][j] / 10000, chances[m][j][i] / 10000).winA;
    pairs.push({ i, j, win });
  }
}
// The favourite's chance under each formula (favourite by the additive one).
const fav = (p: Pair, m: Method) => (p.win.additive >= 0.5 ? p.win[m] : 1 - p.win[m]);
const gaps = pairs.map((p) => fav(p, "additive") - fav(p, "average"));
const mean = gaps.reduce((s, g) => s + g, 0) / gaps.length;
const byGap = [...pairs].sort((a, b) => (fav(b, "additive") - fav(b, "average")) - (fav(a, "additive") - fav(a, "average")));

mkdirSync("results", { recursive: true });
const file = `results/compare-${inputs.window.end}.csv`;
writeFileSync(
  file,
  ["player_a,player_b,average_a_serve,average_b_serve,additive_a_serve,additive_b_serve,average_a_wins,additive_a_wins"]
    .concat(pairs.map((p) => [ps[p.i].name, ps[p.j].name, chances.average[p.i][p.j], chances.average[p.j][p.i], chances.additive[p.i][p.j], chances.additive[p.j][p.i], p.win.average.toFixed(6), p.win.additive.toFixed(6)].join(",")))
    .join("\n") + "\n",
);

const line = (p: Pair) => {
  const [f, u] = p.win.additive >= 0.5 ? [ps[p.i], ps[p.j]] : [ps[p.j], ps[p.i]];
  return `${`${f.name} vs ${u.name}`.padEnd(42)} average ${pct(fav(p, "average")).padStart(5)}%   additive ${pct(fav(p, "additive")).padStart(5)}%`;
};
console.log(`${ps.length} players, ${pairs.length} pairs; tour serve average ${pct(Number(inputs.tour.n) / Number(inputs.tour.d), 2)}%\n`);
console.log(`The favourite's chance of winning the match (exact calculator):`);
console.log(`  additive minus average: ${pct(mean)} points on average, ${pct(Math.min(...gaps))} to ${pct(Math.max(...gaps))} points\n`);
console.log("Biggest gaps:");
for (const p of byGap.slice(0, 5)) console.log(`  ${line(p)}`);
console.log("Smallest gaps:");
for (const p of byGap.slice(-3)) console.log(`  ${line(p)}`);
console.log(`\nFirst two players in the list:\n  ${line(pairs[0])}`);
console.log(`\nEvery pair: ${file}`);

// 2. The engine on a few match-ups.
if (process.argv.includes("--simulate")) {
  const failures: string[] = [];
  execFileSync("bend", ["engine/matchup.bend", "-o", BIN], { stdio: "inherit" });
  const raw = (a: number, b: number, m: Method) => execFileSync(BIN, [String(SEED), String(BITS), ps[a].id, ps[b].id, m], { encoding: "utf8" });
  const parse = (out: string) => {
    const [head, row] = out.trim().split("\n");
    const v = row.split(",");
    return Object.fromEntries(head.split(",").map((k, i) => [k, v[i]]));
  };
  const n = ps.length;
  const picks: [number, number][] = [[0, 1], [0, n - 1], [Math.floor(n / 2), Math.floor(n / 2) + 1]];
  console.log(`\nEngine vs exact calculator, seed ${SEED}, 2^${BITS} matches each:`);
  const run = (a: number, b: number, m: Method) => {
    const t0 = Date.now();
    const s = parse(raw(a, b, m));
    const secs = (Date.now() - t0) / 1000;
    const [ca, cb] = [chances[m][a][b], chances[m][b][a]];
    if (+s.chance_a !== ca || +s.chance_b !== cb) failures.push(`${ps[a].id} vs ${ps[b].id} (${m}): engine used ${s.chance_a}/${s.chance_b}, params say ${ca}/${cb}`);
    const sim = +s.a_wins / RUNS;
    const exact = match(ca / 10000, cb / 10000).winA;
    const off = 100 * Math.abs(sim - exact);
    if (off > TOLERANCE) failures.push(`${ps[a].id} vs ${ps[b].id} (${m}): off by ${off.toFixed(3)} points`);
    if (+s.unfinished !== 0) failures.push(`${ps[a].id} vs ${ps[b].id} (${m}): ${s.unfinished} unfinished`);
    console.log(`  ${`${ps[a].name} vs ${ps[b].name}`.padEnd(40)} ${m.padEnd(8)} chances ${ca}/${cb}: sim ${pct(sim, 2)}%, exact ${pct(exact, 2)}%, off by ${off.toFixed(3)} (${secs.toFixed(1)} s)`);
    return sim;
  };
  for (const [a, b] of picks) for (const m of METHODS) run(a, b, m);
  const ab = run(0, 1, "additive");
  const ba = run(1, 0, "additive");
  if (100 * Math.abs(ab + ba - 1) > 2 * TOLERANCE) failures.push(`swapping players: ${pct(ab, 2)}% + ${pct(ba, 2)}% is not 100%`);
  const self = run(0, 0, "additive");
  if (100 * Math.abs(self - 0.5) > TOLERANCE) failures.push(`${ps[0].id} against herself: ${pct(self, 2)}%`);
  const again = raw(0, 1, "additive") === raw(0, 1, "additive");
  if (!again) failures.push("same seed gave different output");
  console.log(`  rerun with the same seed: ${again ? "identical" : "DIFFERENT"}`);
  if (failures.length > 0) {
    console.log(`\nFAILED:\n  ${failures.join("\n  ")}`);
    process.exit(1);
  }
  console.log("\nALL CHECKS PASS");
}
