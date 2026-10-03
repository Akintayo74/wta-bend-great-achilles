// Milestone 4 validation: the Bend simulator against the exact calculator.
//
// Run: node prep/validate.ts [--bits 20] [--seed 20261108]
//
// 1. The grid (SPEC.md, Outputs and validation): each player's serve point
//    chance is 40%, 45%, ... 75%, giving 64 match-ups, each played 2^bits
//    times. A match-up passes when the match-win chance and the share of
//    every set score are within 0.2 percentage points of the exact values,
//    and no match is unfinished.
// 2. Sanity cases: the same seed gives byte-identical output (again, and on
//    1 core instead of all); a 100% server never loses a set and a 0% server
//    never wins one; swapping the players swaps the result.
//
// Writes results/validation-<date>-seed<seed>.csv (not committed: only
// published runs are). Exits 1 if anything fails.

import { execFileSync } from "node:child_process";
import { mkdirSync, writeFileSync } from "node:fs";
import { match, setShares, SET_SCORE_NAMES } from "./exact.ts";

const arg = (name: string, dflt: number): number => {
  const i = process.argv.indexOf(`--${name}`);
  return i >= 0 ? Number(process.argv[i + 1]) : dflt;
};
const BITS = arg("bits", 20);
const SEED = arg("seed", 20261108);
const RUNS = 2 ** BITS;
const TOLERANCE = 0.2; // percentage points
const GRID = [4000, 4500, 5000, 5500, 6000, 6500, 7000, 7500];
const BIN = "build/simulate";

type SimRow = Record<string, number>;

function build() {
  mkdirSync("build", { recursive: true });
  execFileSync("bend", ["engine/simulate.bend", "-o", BIN], { stdio: "inherit" });
}

function simulateRaw(a: number, b: number, bits = BITS, extra: string[] = []): string {
  return execFileSync(BIN, [String(SEED), String(bits), String(a), String(b), ...extra], { encoding: "utf8" });
}

function parse(out: string): SimRow {
  const [head, line] = out.trim().split("\n");
  const keys = head.split(",");
  const vals = line.split(",").map(Number);
  return Object.fromEntries(keys.map((k, i) => [k, vals[i]]));
}

const pct = (x: number) => (100 * x).toFixed(2);
let failures: string[] = [];

console.log(`Simulator vs exact calculator: seed ${SEED}, 2^${BITS} = ${RUNS.toLocaleString("en")} matches per match-up\n`);
build();

// 1. The grid.
const rows: string[] = [["chance_a", "chance_b", "sim_win_a", "exact_win_a", "diff_win_pp", "worst_set_score", "worst_set_diff_pp", "unfinished", "seconds"].join(",")];
let worstWin = 0;
let worstSet = 0;
let totalSeconds = 0;
const simWin = new Map<string, number>();
for (const a of GRID) {
  for (const b of GRID) {
    const t0 = Date.now();
    const sim = parse(simulateRaw(a, b));
    const seconds = (Date.now() - t0) / 1000;
    totalSeconds += seconds;
    const exact = match(a / 10000, b / 10000);
    const winSim = sim.a_wins / RUNS;
    simWin.set(`${a},${b}`, winSim);
    const dWin = 100 * Math.abs(winSim - exact.winA);
    const totalSets = SET_SCORE_NAMES.reduce((s, n) => s + sim[n], 0);
    const exactShares = setShares(exact.setsPerMatch);
    let dSet = 0;
    let dSetName = "";
    for (const n of SET_SCORE_NAMES) {
      const d = 100 * Math.abs(sim[n] / totalSets - exactShares[n]);
      if (d > dSet) [dSet, dSetName] = [d, n];
    }
    worstWin = Math.max(worstWin, dWin);
    worstSet = Math.max(worstSet, dSet);
    if (dWin > TOLERANCE) failures.push(`${a} vs ${b}: match win off by ${dWin.toFixed(3)} points`);
    if (dSet > TOLERANCE) failures.push(`${a} vs ${b}: set score ${dSetName} off by ${dSet.toFixed(3)} points`);
    if (sim.unfinished !== 0) failures.push(`${a} vs ${b}: ${sim.unfinished} unfinished matches`);
    if (sim.other_sets !== 0) failures.push(`${a} vs ${b}: ${sim.other_sets} sets with an impossible score`);
    if (sim.a_wins + sim.b_wins + sim.unfinished !== RUNS) failures.push(`${a} vs ${b}: counts don't add up to ${RUNS}`);
    rows.push([a, b, winSim.toFixed(6), exact.winA.toFixed(6), dWin.toFixed(4), dSetName, dSet.toFixed(4), sim.unfinished, seconds.toFixed(2)].join(","));
    console.log(`  ${pct(a / 10000)}% vs ${pct(b / 10000)}%: A wins ${pct(winSim)}% (exact ${pct(exact.winA)}%), off by ${dWin.toFixed(3)}; worst set score ${dSetName} off by ${dSet.toFixed(3)}; ${seconds.toFixed(1)} s`);
  }
}
const date = new Date().toISOString().slice(0, 10);
mkdirSync("results", { recursive: true });
const file = `results/validation-${date}-seed${SEED}.csv`;
writeFileSync(file, rows.join("\n") + "\n");

// 2. Sanity cases.
const sanity: string[] = [];
const again = simulateRaw(6000, 5650);
const oneCore = simulateRaw(6000, 5650, BITS, ["--threads", "1"]);
const first = simulateRaw(6000, 5650);
const sameSeed = again === first && oneCore === first;
sanity.push(`same seed, rerun and on 1 core: ${sameSeed ? "identical" : "DIFFERENT"}`);
if (!sameSeed) failures.push("same seed gave different output");

const certain = parse(simulateRaw(10000, 5000, 16));
const bSets = SET_SCORE_NAMES.filter((n) => n.startsWith("b")).reduce((s, n) => s + certain[n], 0);
sanity.push(`100% server vs 50%: B won ${certain.b_wins} matches and ${bSets} sets (should be 0 and 0)`);
if (certain.b_wins !== 0 || bSets !== 0) failures.push("a 100% server lost a set");
const hopeless = parse(simulateRaw(0, 5000, 16));
const aSets = SET_SCORE_NAMES.filter((n) => n.startsWith("a")).reduce((s, n) => s + hopeless[n], 0);
sanity.push(`0% server vs 50%: A won ${hopeless.a_wins} matches and ${aSets} sets (should be 0 and 0)`);
if (hopeless.a_wins !== 0 || aSets !== 0) failures.push("a 0% server won a set");

let worstSwap = 0;
for (const a of GRID) for (const b of GRID) worstSwap = Math.max(worstSwap, 100 * Math.abs(simWin.get(`${a},${b}`)! + simWin.get(`${b},${a}`)! - 1));
sanity.push(`swapping players: A's chance in (x vs y) plus A's chance in (y vs x) is within ${worstSwap.toFixed(3)} points of 100%`);
if (worstSwap > 2 * TOLERANCE) failures.push(`swapping players: off by ${worstSwap.toFixed(3)} points`);

let worstEqual = 0;
for (const a of GRID) worstEqual = Math.max(worstEqual, 100 * Math.abs(simWin.get(`${a},${a}`)! - 0.5));
sanity.push(`equal players: within ${worstEqual.toFixed(3)} points of 50/50`);

console.log(`\nGrid: worst match-win gap ${worstWin.toFixed(3)} points, worst set-score gap ${worstSet.toFixed(3)} points (tolerance ${TOLERANCE}).`);
console.log(`Simulation time: ${totalSeconds.toFixed(1)} s for 64 x 2^${BITS} matches.`);
console.log(`Sanity:\n  ${sanity.join("\n  ")}`);
console.log(`Results: ${file}`);
if (failures.length > 0) {
  console.log(`\nFAILED:\n  ${failures.join("\n  ")}`);
  process.exit(1);
}
console.log("\nALL CHECKS PASS");
