// Tests for prep: the CSV reader, exact fractions and rounding, the Tennis
// Abstract rules, the point-model formulas, the refusal to write bad
// parameters, and the generated params.bend (checked by Bend itself).
//
// Run: node --test prep/*.test.ts

import { test } from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { copyFileSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { CsvError, formatCsv, parseCsv } from "./csv.ts";
import { parseDecimal, percent, ratio, toTenThousandths } from "./ratio.ts";
import { exclusion, type MatchRow, matchKey, playerTotals, readLeaderFile, readPlayerFile, tourTotals, windowStart } from "./tennisabstract.ts";
import { allChances, PLAYER_COLUMNS, readInputs, TOUR_COLUMNS } from "./model.ts";
import { build } from "./params.ts";

// ---------------------------------------------------------------------------
// CSV
// ---------------------------------------------------------------------------

test("csv: quoted fields, commas and quotes inside them, round trip", () => {
  const text = 'name,source\nA,"Tennis Abstract, 2026-10-04"\nB,"say ""hi"""\n';
  const { header, rows } = parseCsv(text);
  assert.deepEqual(header, ["name", "source"]);
  assert.deepEqual(rows, [{ name: "A", source: "Tennis Abstract, 2026-10-04" }, { name: "B", source: 'say "hi"' }]);
  assert.equal(formatCsv(header, rows), text);
});

test("csv: refuses ragged rows, stray quotes and repeated columns", () => {
  assert.throws(() => parseCsv("a,b\n1\n"), CsvError);
  assert.throws(() => parseCsv('a\nx"y\n'), CsvError);
  assert.throws(() => parseCsv('a\n"open\n'), CsvError);
  assert.throws(() => parseCsv("a,a\n1,2\n"), CsvError);
  assert.throws(() => parseCsv(""), CsvError);
});

test("csv: blank fields and CRLF line ends", () => {
  assert.deepEqual(parseCsv("a,b,c\r\n1,,3\r\n").rows, [{ a: "1", b: "", c: "3" }]);
});

// ---------------------------------------------------------------------------
// Exact fractions and rounding
// ---------------------------------------------------------------------------

test("rounding: nearest out of 10,000, an exact half goes up", () => {
  assert.equal(toTenThousandths(ratio(64005, 100000)), 6401n);
  assert.equal(toTenThousandths(ratio(640049999, 1000000000)), 6400n);
  assert.equal(toTenThousandths(ratio(64, 100)), 6400n);
  assert.equal(toTenThousandths(ratio(2, 3)), 6667n);
  assert.equal(toTenThousandths(ratio(1)), 10000n);
  assert.equal(toTenThousandths(ratio(0)), 0n);
  assert.equal(toTenThousandths(ratio(-1, 20000)), 0n); // -0.5 rounds up to 0
  assert.equal(toTenThousandths(ratio(-3, 20000)), -1n);
});

test("decimals are read exactly, and only plain decimals", () => {
  assert.deepEqual(parseDecimal("65.1"), ratio(651, 10));
  assert.deepEqual(parseDecimal(" 62 "), ratio(62));
  for (const bad of ["", "65.1%", "1e3", "6,5", "abc", "."]) assert.equal(parseDecimal(bad), null);
  assert.equal(percent(ratio(2, 3), 2), "66.67");
  assert.equal(percent(ratio(-1, 8), 1), "-12.5");
});

// ---------------------------------------------------------------------------
// Tennis Abstract files and rules
// ---------------------------------------------------------------------------

const row = (over: Partial<MatchRow> = {}): MatchRow => ({
  player: "Player A", date: "20260301", tourn: "Indian Wells", surf: "Hard", level: "PM", round: "R32",
  opp: "Player B", score: "6-4 6-4", pts: "60", fwon: "30", swon: "10", opts: "62", ofwon: "28", oswon: "8", ...over,
});

test("rules: which matches count", () => {
  const w = (m: MatchRow) => exclusion(m, "20251006", "20261004");
  assert.equal(w(row()), null);
  assert.equal(w(row({ round: "QF" })), null, "a quarter-final is not qualifying");
  assert.equal(w(row({ round: "RR", level: "F" })), null);
  assert.equal(w(row({ round: "Q2" })), "qualifying");
  assert.equal(w(row({ surf: "Clay" })), "not hard court");
  assert.equal(w(row({ date: "20251005" })), "outside the window");
  assert.equal(w(row({ date: "20251006" })), null);
  assert.equal(w(row({ date: "20261005" })), "outside the window");
  assert.equal(w(row({ level: "C" })), "not tour level (level C)");
  assert.equal(w(row({ level: "D" })), "not tour level (level D)");
  assert.equal(w(row({ level: "100" })), "not tour level (level 100)");
  assert.equal(w(row({ level: "I", tourn: "United Cup" })), "team event");
  assert.equal(w(row({ score: "6-1 RET" })), "retirement");
  assert.equal(w(row({ score: "W/O", pts: "" })), "walkover");
  assert.equal(w(row({ pts: "" })), "no stats");
  assert.equal(w(row({ fwon: "55" })), "stats don't add up");
});

test("window: 364 days ending on the snapshot date", () => {
  assert.equal(windowStart("2026-10-04"), "2025-10-06");
  assert.equal(windowStart("2026-03-01"), "2025-03-03");
  assert.throws(() => windowStart("2026-02-30"));
});

test("totals: serve and return points from one player's rows", () => {
  const t = playerTotals([row(), row({ pts: "40", fwon: "20", swon: "5", opts: "38", ofwon: "20", oswon: "6" })]);
  assert.deepEqual(t, { servePointsWon: 65, servePoints: 100, returnPointsWon: 26 + 12, returnPoints: 100, matches: 2 });
});

test("tour average: a match listed under both players counts once", () => {
  const a = row();
  const b = row({ player: "Player B", opp: "Player A", pts: "62", fwon: "28", swon: "8", opts: "60", ofwon: "30", oswon: "10" });
  assert.equal(matchKey(a), matchKey(b));
  assert.deepEqual(tourTotals([a, b]), { servePointsWon: 76, servePoints: 122, matches: 1 });
});

test("files are read as JSON, never run, and columns land in the right place", () => {
  const per = `var fullname = 'Player A';\nvar matchmx = [["20260301","Indian Wells","Hard","PM","W","5","3","","R32","6-4 6-4","3","Player B","20","","","R","20000101","170","USA","","90","4","2","60","40","30","10","6","2","3","1","3","62","41","28","8","4","1","4","2","","","",""]];\nvar other = 1;`;
  const [m] = readPlayerFile(per);
  assert.deepEqual([m.player, m.round, m.opp, m.pts, m.fwon, m.swon, m.opts, m.ofwon, m.oswon], ["Player A", "R32", "Player B", "60", "30", "10", "62", "28", "8"]);
  const lead = `var matchmx = [["20260301","Indian Wells","Hard","PM","W","Player A","5","3","","R32","6-4 6-4","3","Player B","20","","","R","2","20000101","170","USA","","0","0","2","0","90","4","2","60","40","30","10","6","2","3","1","3","62","41","28","8","4","1","4"]];`;
  const [l] = readLeaderFile(lead);
  assert.deepEqual([l.player, l.round, l.pts, l.fwon, l.swon, l.opts, l.ofwon, l.oswon], ["Player A", "R32", "60", "30", "10", "62", "28", "8"]);
  assert.throws(() => readPlayerFile("var fullname = 'X';\nvar matchmx = [[alert(1)]];"));
});

// ---------------------------------------------------------------------------
// The point model, on the spec's invented players
// ---------------------------------------------------------------------------
// A: 62% serve, 45% return; B: 58% serve, 42% return; tour average 56%
// (SPEC.md, Point model). As counts out of 1,000 points.

type P = { name: string; sw: string; sp: string; rw: string; rp: string; rpw?: string; dr?: string };
const playersCsv = (ps: P[]) =>
  formatCsv(PLAYER_COLUMNS, ps.map((p) => ({
    name: p.name, serve_points_won: p.sw, serve_points: p.sp, return_points_won: p.rw, return_points: p.rp, matches: "10",
    window_start: "2025-10-06", window_end: "2026-10-04", checked_rpw: p.rpw ?? "", checked_dr: p.dr ?? "", source: "test",
  })));
const tourCsv = (won = "560", pts = "1000") =>
  formatCsv(TOUR_COLUMNS, [{ surface: "Hard", serve_points_won: won, serve_points: pts, matches: "5", window_start: "2025-09-23", window_end: "2026-09-21", source: "test" }]);
const A: P = { name: "Player A", sw: "620", sp: "1000", rw: "450", rp: "1000" };
const B: P = { name: "Player B", sw: "580", sp: "1000", rw: "420", rp: "1000" };

const chancesOf = (ps: P[], tour = tourCsv()) => {
  const { inputs, problems } = readInputs(playersCsv(ps), tour);
  assert.deepEqual(problems, []);
  const r = allChances(inputs!);
  assert.deepEqual(r.problems, []);
  return r.chances!;
};

test("formulas: the spec's worked example (60.0/56.5 average, 64.0/57.0 additive)", () => {
  const c = chancesOf([A, B]);
  assert.deepEqual(c.average, [[(6200 + 5500) / 2, 6000], [5650, (5800 + 5800) / 2]]);
  assert.deepEqual(c.additive, [[6200 + 5500 - 5600, 6400], [5700, 5800 + 5800 - 5600]]);
});

test("formulas: the server's serve and the receiver's return, never the other way round", () => {
  // Make every number different, so a mix-up can't give the right answer.
  const X: P = { name: "X Server", sw: "700", sp: "1000", rw: "300", rp: "1000" };
  const Y: P = { name: "Y Receiver", sw: "500", sp: "1000", rw: "400", rp: "1000" };
  const c = chancesOf([X, Y]);
  assert.equal(c.additive[0][1], 7000 + 6000 - 5600); // X serving: X's serve, Y's return
  assert.equal(c.additive[1][0], 5000 + 7000 - 5600); // Y serving: Y's serve, X's return
  assert.equal(c.average[0][1], (7000 + 6000) / 2);
  assert.equal(c.average[1][0], (5000 + 7000) / 2);
});

test("formulas: combined exactly, rounded once", () => {
  // Serve 1/3, return 1/7, tour 1/2: 1/3 + (1 - 1/7) - 1/2 = 29/42 =
  // 0.690476... -> 6905. Rounding each input first would give
  // 3333 + 8571 - 5000 = 6904.
  const T: P = { name: "T One", sw: "1", sp: "3", rw: "1", rp: "7" };
  const c = chancesOf([T], tourCsv("1", "2"));
  assert.equal(c.additive[0][0], 6905);
});

test("refusal: impossible chances are listed, never clamped", () => {
  const strong: P = { name: "Strong One", sw: "990", sp: "1000", rw: "100", rp: "1000" };
  const weak: P = { name: "Weak One", sw: "10", sp: "1000", rw: "900", rp: "1000" };
  const { inputs } = readInputs(playersCsv([strong, weak]), tourCsv("0", "1000")); // 0.99 + 0.1 - 0 = 1.09
  const r = allChances(inputs!);
  assert.equal(r.chances, null);
  assert.ok(r.problems.some((p) => p.startsWith("additive: Strong One serving vs Weak One") && p.includes("above 100%")), r.problems.join("\n"));
  const r2 = allChances(readInputs(playersCsv([weak, strong]), tourCsv("990", "1000")).inputs!);
  assert.ok(r2.problems.some((p) => p.startsWith("additive: Weak One serving vs Strong One") && p.includes("below 0%")), r2.problems.join("\n"));
});

test("refusal: every bad input is reported, not just the first", () => {
  const bad = [
    { ...A, sw: "" },
    { ...B, rw: "1200" },
    { ...A, name: "Player A" }, // same name again
    { ...B, name: "Player C", sp: "0" },
    { ...B, name: "Player D", rpw: "42.0", dr: "1.50" }, // page gives SPW 72.0, data says 58.0
    { ...B, name: "Player E", rpw: "42%" },
  ];
  const { inputs, problems } = readInputs(playersCsv(bad), tourCsv());
  assert.equal(inputs, null);
  const want = ["serve_points_won is blank", "more return points won than played", "name appears twice", "serve_points is 0", "the page's RPW and DR give 72.0%", "checked_rpw must be a percentage"];
  for (const w of want) assert.ok(problems.some((p) => p.includes(w)), `missing: ${w}\n${problems.join("\n")}`);
});

test("hand check: within 0.5 points passes and marks the player checked", () => {
  // A: 62% serve, 45% return, so DR = 45 / 38 = 1.18 and the page's SPW is
  // 100 - 44.5 / 1.18 = 62.3.
  const { inputs, problems } = readInputs(playersCsv([{ ...A, rpw: "44.5", dr: "1.18" }, { ...B, rpw: "42.0" }]), tourCsv());
  assert.deepEqual(problems, []);
  assert.deepEqual(inputs!.players.map((p) => p.checked), [true, false]);
  assert.ok(readInputs(playersCsv([{ ...A, rpw: "45.6", dr: "1.20" }]), tourCsv()).problems.length === 1);
  assert.ok(readInputs(playersCsv([{ ...A, rpw: "45.0", dr: "1.30" }]), tourCsv()).problems.some((p) => p.includes("SPW from the data")));
  assert.ok(readInputs(playersCsv([{ ...A, dr: "1.18" }]), tourCsv()).problems.some((p) => p.includes("needs checked_rpw")));
});

test("refusal: mixed snapshots and a bad tour.csv", () => {
  const two = playersCsv([A]) + playersCsv([B]).split("\n")[1].replace("2026-10-04", "2026-11-02") + "\n";
  assert.ok(readInputs(two, tourCsv()).problems.some((p) => p.includes("different snapshots")));
  assert.ok(readInputs(playersCsv([A]), tourCsv("1200", "1000")).problems.some((p) => p.startsWith("tour.csv")));
});

// ---------------------------------------------------------------------------
// The generated params.bend
// ---------------------------------------------------------------------------

test("params: same inputs give byte-identical output", () => {
  const a = build(playersCsv([A, B]), tourCsv());
  const b = build(playersCsv([A, B]), tourCsv());
  assert.ok(a.text);
  assert.equal(a.text, b.text);
  assert.ok(a.text!.includes("Sim.Chance{6400, {==}}"));
});

test("params: nothing is built from bad inputs", () => {
  const r = build(playersCsv([{ ...A, sw: "" }]), tourCsv());
  assert.equal(r.text, null);
  assert.ok(r.problems.length > 0);
});

// Bend reads a generated file, and refuses one with a chance above 10,000.
test("params: Bend accepts the generated file and rejects an out-of-range chance", () => {
  const dir = mkdtempSync(join(tmpdir(), "params-"));
  for (const f of ["sim.bend", "scoring.bend"]) copyFileSync(`engine/${f}`, join(dir, f));
  const text = build(playersCsv([A, B, { ...B, name: "Player Bee" }]), tourCsv()).text!;
  writeFileSync(join(dir, "params.bend"), text);
  const out = execFileSync("bend", [join(dir, "params.bend"), "--check-only"], { encoding: "utf8" });
  assert.match(out, /ALL PROOFS CHECK/);

  writeFileSync(join(dir, "params.bend"), text.replace("Sim.Chance{6400, {==}}", "Sim.Chance{10001, {==}}"));
  assert.throws(() => execFileSync("bend", [join(dir, "params.bend"), "--check-only"], { encoding: "utf8", stdio: "pipe" }));
});
