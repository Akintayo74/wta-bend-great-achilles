// Turn a committed snapshot (data/raw/<date>/) into the counts in
// data/players.csv and the tour average in data/tour.csv.
//
// Run: node prep/collect.ts [data/raw/<date>]     (default: the newest)
//
// Player names, their order, and the hand-typed checked_rpw / checked_dr
// columns in data/players.csv are kept; every other column is rewritten from
// the snapshot. Prints, for each player, the matches counted and why the
// others were left out.

import { existsSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { formatCsv, parseCsv, type Row } from "./csv.ts";
import { PLAYER_COLUMNS, TOUR_COLUMNS } from "./model.ts";
import { percent, ratio } from "./ratio.ts";
import { compact, exclusion, type MatchRow, playerSlug, playerTotals, tourTotals } from "./tennisabstract.ts";

const dir = process.argv[2] ?? `data/raw/${readdirSync("data/raw").filter((d) => /^\d{4}-\d{2}-\d{2}$/.test(d)).sort().at(-1)}`;
if (!existsSync(`${dir}/manifest.csv`)) {
  console.error(`no snapshot in ${dir} (run prep/fetch.ts first)`);
  process.exit(1);
}

const read = (f: string) => parseCsv(readFileSync(f, "utf8")).rows;
const manifest = new Map(read(`${dir}/manifest.csv`).map((r) => [r.file, r]));
const extract = read(`${dir}/players.csv`) as unknown as MatchRow[];
const tourExtract = read(`${dir}/tour.csv`) as unknown as MatchRow[];
const existing = parseCsv(readFileSync("data/players.csv", "utf8")).rows;

const sourceOf = (file: string): Row => {
  const m = manifest.get(file);
  if (!m) throw new Error(`${file} is not in ${dir}/manifest.csv`);
  return m;
};
const describe = (m: Row) => `Tennis Abstract jsmatches/${m.file} read ${m.read_on} sha256:${m.sha256.slice(0, 16)}`;

// Count the reasons matches were left out, for the report.
function split(rows: MatchRow[], start: string, end: string) {
  const kept: MatchRow[] = [];
  const left: Record<string, number> = {};
  for (const m of rows) {
    const why = exclusion(m, compact(start), compact(end));
    if (why === null) kept.push(m);
    else left[why] = (left[why] ?? 0) + 1;
  }
  return { kept, left };
}
const showLeft = (left: Record<string, number>) =>
  Object.entries(left).map(([k, v]) => `${v} ${k}`).join(", ") || "none";

// --- players ---
const out: Row[] = [];
console.log(`Snapshot ${dir}\n`);
console.log("player                     matches   SPW (points)        RPW (points)       left out");
for (const p of existing) {
  const file = `${playerSlug(p.name)}.js`;
  const m = sourceOf(file);
  const { kept, left } = split(extract.filter((r) => r.player === p.name), m.window_start, m.window_end);
  const t = playerTotals(kept);
  out.push({
    name: p.name,
    serve_points_won: String(t.servePointsWon), serve_points: String(t.servePoints),
    return_points_won: String(t.returnPointsWon), return_points: String(t.returnPoints),
    matches: String(t.matches), window_start: m.window_start, window_end: m.window_end,
    checked_rpw: p.checked_rpw ?? "", checked_dr: p.checked_dr ?? "",
    source: describe(m),
  });
  const pc = (a: number, b: number) => (b === 0 ? "  -  " : percent(ratio(a, b), 1));
  console.log(
    `${p.name.padEnd(26)} ${String(t.matches).padStart(4)}    ${pc(t.servePointsWon, t.servePoints).padStart(5)}% (${String(t.servePoints).padStart(5)})   ${pc(t.returnPointsWon, t.returnPoints).padStart(5)}% (${String(t.returnPoints).padStart(5)})   ${showLeft(left)}`,
  );
}
writeFileSync("data/players.csv", formatCsv(PLAYER_COLUMNS, out));

// --- tour average ---
const lm = sourceOf("leadersource_wta.js");
const { kept, left } = split(tourExtract, lm.window_start, lm.window_end);
const tt = tourTotals(kept);
writeFileSync(
  "data/tour.csv",
  formatCsv(TOUR_COLUMNS, [{
    surface: "Hard", serve_points_won: String(tt.servePointsWon), serve_points: String(tt.servePoints),
    matches: String(tt.matches), window_start: lm.window_start, window_end: lm.window_end, source: describe(lm),
  }]),
);
console.log(`\nTour average (hard, ${lm.window_start} to ${lm.window_end}): ${percent(ratio(tt.servePointsWon, tt.servePoints), 2)}% of ${tt.servePoints} serve points in ${tt.matches} matches`);
console.log(`  rows left out: ${showLeft(left)}`);
console.log("\nWrote data/players.csv and data/tour.csv. Next: node prep/params.ts");
