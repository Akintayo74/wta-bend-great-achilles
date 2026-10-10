// The final run: the eight players in data/field.csv, played 2^20 times
// through the whole WTA Finals, plus every one of their 28 match-ups, then the
// numbers for the results page.
//
// Run: node prep/final.ts [--bits 20] [--seed 20261108] [--field data/field.csv] [--test]
//
// 1. Checks that engine/params.bend matches data/ and that every player in
//    the field has been checked by hand (SPEC.md, Inputs and data). --test
//    lifts the hand check, for trying things out; everything it writes is
//    then marked as a test.
// 2. Builds build/finals and build/matchup from the current sources.
// 3. Plays the tournament (seeded draw by lot in every run, or the real
//    groups if field.csv gives them) and the 28 match-ups.
// 4. Writes results/<date>-seed<seed>-finals.csv and -matchups.csv (only
//    published runs are committed: git add -f), and site/src/data/results.json
//    for the results page.

import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { readInputs } from "./model.ts";
import { readField, readFinals, readMatchup } from "./results.ts";

const arg = (name: string, dflt: number): number => {
  const i = process.argv.indexOf(`--${name}`);
  return i >= 0 ? Number(process.argv[i + 1]) : dflt;
};
const BITS = arg("bits", 20);
const SEED = arg("seed", 20261108);
const TEST = process.argv.includes("--test");
const FIELD = (() => {
  const i = process.argv.indexOf("--field");
  return i >= 0 ? process.argv[i + 1] : "data/field.csv";
})();
const RUNS = 2 ** BITS;
const METHOD = "additive";
const date = new Date().toISOString().slice(0, 10);
const run = (cmd: string, args: string[]) => execFileSync(cmd, args, { encoding: "utf8", maxBuffer: 1 << 26 });
const die = (lines: string[]) => {
  for (const l of lines) console.error(l);
  process.exit(1);
};

// 1. Inputs.
try {
  run("node", ["prep/params.ts", "--check"]);
} catch {
  die(["engine/params.bend is out of date with data/: run node prep/params.ts first"]);
}
const { inputs, problems } = readInputs(readFileSync("data/players.csv", "utf8"), readFileSync("data/tour.csv", "utf8"));
if (!inputs) die(problems);
const { field, problems: fieldProblems } = readField(readFileSync(FIELD, "utf8"), inputs!.players);
if (!field) die(fieldProblems);
const unchecked = field!.entries.filter((e) => !e.checked).map((e) => e.name);
if (unchecked.length > 0 && !TEST) {
  die([`Not yet checked by hand: ${unchecked.join(", ")}.`, "Add their checked_rpw and checked_dr to data/players.csv (or use --test to try things out)."]);
}

// 2. Build.
for (const b of ["finals", "matchup"]) {
  console.log(`Building build/${b} ...`);
  run("bend", [`engine/${b}.bend`, "-o", `build/${b}`]);
}

// 3. Play.
const ids = field!.entries.map((e) => e.id);
const extra = unchecked.length > 0 ? ["unchecked"] : [];
console.log(`Playing ${RUNS.toLocaleString("en")} tournaments (draw: ${field!.draw}) ...`);
let t = Date.now();
const finalsCsv = run("./build/finals", [String(SEED), String(BITS), field!.draw, ...ids, METHOD, ...extra]);
const { players, unfinished } = readFinals(finalsCsv, field!, RUNS);
console.log(`  done in ${((Date.now() - t) / 1000).toFixed(0)} s`);
console.log(`Playing the 28 match-ups, ${RUNS.toLocaleString("en")} times each ...`);
t = Date.now();
const matchupCsv: string[] = [];
const matchups = [];
for (let i = 0; i < 8; i++) {
  for (let j = i + 1; j < 8; j++) {
    const out = run("./build/matchup", [String(SEED), String(BITS), ids[i], ids[j], METHOD]);
    matchupCsv.push(matchupCsv.length === 0 ? out.trimEnd() : out.trimEnd().split("\n")[1]);
    matchups.push(readMatchup(out, RUNS));
  }
}
console.log(`  done in ${((Date.now() - t) / 1000).toFixed(0)} s`);

// 4. Write.
const tag = `${TEST ? "test-" : ""}${date}-seed${SEED}`;
mkdirSync("results", { recursive: true });
writeFileSync(`results/${tag}-finals.csv`, finalsCsv);
writeFileSync(`results/${tag}-matchups.csv`, matchupCsv.join("\n") + "\n");
let commit = "unknown";
try {
  commit = run("git", ["rev-parse", "--short", "HEAD"]).trim();
  if (run("git", ["status", "--porcelain", "--untracked-files=no"]).trim() !== "") commit += " (with uncommitted changes)";
} catch {}
const result = {
  test: TEST,
  allChecked: unchecked.length === 0,
  date, seed: SEED, bits: BITS, runs: RUNS, method: METHOD, draw: field!.draw, commit,
  window: inputs!.window,
  tourServe: Number(inputs!.tour.n) / Number(inputs!.tour.d),
  players: players.map((p) => {
    const q = inputs!.players.find((x) => x.name === p.name)!;
    return { ...p, serve: Number(q.serve.n) / Number(q.serve.d), ret: Number(q.ret.n) / Number(q.ret.d) };
  }),
  unfinished,
  matchups,
};
mkdirSync("site/src/data", { recursive: true });
writeFileSync("site/src/data/results.json", JSON.stringify(result, null, 2) + "\n");
console.log(`Wrote results/${tag}-finals.csv, results/${tag}-matchups.csv and site/src/data/results.json`);
const pct = (n: number) => ((100 * n) / RUNS).toFixed(1).padStart(5);
console.log("\nseed player          semis  final  title");
for (const p of [...players].sort((a, b) => b.titles - a.titles)) {
  console.log(`${String(p.seed).padStart(4)} ${p.name.padEnd(16)} ${pct(p.semifinals)}  ${pct(p.finals)}  ${pct(p.titles)}`);
}
if (unfinished > 0) console.log(`\n${unfinished} tournaments had a match hit the point cap and are counted as unfinished.`);
