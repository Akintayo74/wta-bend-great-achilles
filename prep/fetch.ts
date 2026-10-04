// Download a snapshot of Tennis Abstract data and write the trimmed extracts
// that get committed.
//
// Run: node prep/fetch.ts [--date YYYY-MM-DD]     (default: today, UTC)
//
// 1. For every player named in data/players.csv, downloads
//    https://www.tennisabstract.com/jsmatches/<FirstLast>.js, plus the
//    leaderboard file leadersource_wta.js (for the tour average), into
//    data/downloads/<date>/. Those full files are not committed. A file
//    already there is reused, so a re-run doesn't download again.
// 2. Writes data/raw/<date>/:
//      players.csv   every hard-court match of each player in the 52 weeks
//                    ending on <date>, before the other filters, so what
//                    prep/collect.ts leaves out stays visible
//      tour.csv      every hard-court row of the leaderboard file in its own
//                    latest 52 weeks
//      manifest.csv  each downloaded file: address, date read, size, SHA-256
//                    and its latest match
//
// Then run prep/collect.ts to turn the extracts into data/players.csv counts
// and data/tour.csv.

import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { formatCsv, parseCsv } from "./csv.ts";
import { compact, EXTRACT_COLUMNS, iso, type MatchRow, playerFileName, playerSlug, readLeaderFile, readPlayerFile, windowStart } from "./tennisabstract.ts";

const BASE = "https://www.tennisabstract.com/jsmatches/";

const arg = (name: string): string | undefined => {
  const i = process.argv.indexOf(`--${name}`);
  return i >= 0 ? process.argv[i + 1] : undefined;
};
const date = arg("date") ?? new Date().toISOString().slice(0, 10);
const start = windowStart(date);

const names = parseCsv(readFileSync("data/players.csv", "utf8")).rows.map((r) => r.name);
if (names.length === 0) {
  console.error("data/players.csv names no players");
  process.exit(1);
}

const downloads = `data/downloads/${date}`;
const raw = `data/raw/${date}`;
mkdirSync(downloads, { recursive: true });
mkdirSync(raw, { recursive: true });

// Download with curl (it follows the machine's proxy settings), one file at a
// time with a pause between, to be gentle on a one-person website.
function download(file: string): string {
  const path = `${downloads}/${file}`;
  if (!existsSync(path)) {
    execFileSync("curl", ["-sSf", "--max-time", "60", "-o", path, BASE + file]);
    execFileSync("sleep", ["1"]);
  }
  return readFileSync(path, "utf8");
}

const sha256 = (s: string) => createHash("sha256").update(s).digest("hex");
const latest = (rows: MatchRow[]) => rows.reduce((a, m) => (m.date > a ? m.date : a), "");

const manifest: Record<string, string>[] = [];
const note = (file: string, src: string, rows: MatchRow[], ws: string, we: string) =>
  manifest.push({
    file, url: BASE + file, read_on: date, bytes: String(Buffer.byteLength(src)), sha256: sha256(src),
    latest_match: iso(latest(rows)), window_start: ws, window_end: we,
  });

// Players.
const playerRows: MatchRow[] = [];
let failed = false;
for (const name of names) {
  const file = `${playerSlug(name)}.js`;
  const src = download(file);
  const inFile = playerFileName(src);
  if (inFile !== name) {
    console.error(`${file} is for ${inFile}, not ${name}`);
    failed = true;
    continue;
  }
  const rows = readPlayerFile(src);
  note(file, src, rows, start, date);
  playerRows.push(...rows.filter((m) => m.surf === "Hard" && m.date >= compact(start) && m.date <= compact(date)));
}
if (failed) process.exit(1);

// The tour average: the leaderboard file's own latest 52 weeks (it lags).
const leaderSrc = download("leadersource_wta.js");
const leaderRows = readLeaderFile(leaderSrc);
const tourEnd = iso(latest(leaderRows));
const tourStart = windowStart(tourEnd);
note("leadersource_wta.js", leaderSrc, leaderRows, tourStart, tourEnd);
const tourRows = leaderRows.filter((m) => m.surf === "Hard" && m.date >= compact(tourStart) && m.date <= compact(tourEnd));

writeFileSync(`${raw}/players.csv`, formatCsv(EXTRACT_COLUMNS, playerRows));
writeFileSync(`${raw}/tour.csv`, formatCsv(EXTRACT_COLUMNS, tourRows));
writeFileSync(`${raw}/manifest.csv`, formatCsv(Object.keys(manifest[0]), manifest));

console.log(`Snapshot ${date}: ${names.length} players, window ${start} to ${date}`);
console.log(`  ${playerRows.length} hard-court player rows -> ${raw}/players.csv`);
console.log(`  ${tourRows.length} hard-court leaderboard rows, ${tourStart} to ${tourEnd} -> ${raw}/tour.csv`);
console.log(`Next: node prep/collect.ts ${raw}`);
