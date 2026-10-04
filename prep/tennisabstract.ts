// Reading Tennis Abstract's data files, and the rules for which matches count.
//
// Two kinds of file, both a JavaScript array of matches called `matchmx`:
//   jsmatches/<FirstLast>.js       one player's matches (no player column)
//   jsmatches/leadersource_wta.js  every match of the current top 50, one
//                                   row per (top-50 player, match)
// The array is read as JSON, never run as code.
//
// Rules (SPEC.md, Inputs and data, decided in milestone 5): hard courts;
// tour-level main draw including Slams and the Finals; no qualifying, team
// events, WTA 125s or ITF events; no retirements, walkovers or matches
// without stats; tournament date inside the window.

// One match from one player's side, trimmed to what prep needs. This is also
// the row format of the committed extracts in data/raw/<date>/.
export type MatchRow = {
  player: string;
  date: string; // YYYYMMDD, the tournament's start date
  tourn: string;
  surf: string;
  level: string;
  round: string;
  opp: string;
  score: string;
  pts: string; // the player's serve points
  fwon: string; // first-serve points won
  swon: string; // second-serve points won
  opts: string; // the opponent's serve points
  ofwon: string;
  oswon: string;
};

export const EXTRACT_COLUMNS: (keyof MatchRow)[] = ["player", "date", "tourn", "surf", "level", "round", "opp", "score", "pts", "fwon", "swon", "opts", "ofwon", "oswon"];

// Column names in each file kind, as Tennis Abstract's own pages list them.
const PLAYER_HEAD = ["date", "tourn", "surf", "level", "wl", "rank", "seed", "entry", "round", "score", "max", "opp", "orank", "oseed", "oentry", "ohand", "obday", "oht", "ocountry", "oactive", "time", "aces", "dfs", "pts", "firsts", "fwon", "swon", "games", "saved", "chances", "oaces", "odfs", "opts", "ofirsts", "ofwon", "oswon", "ogames", "osaved", "ochances"];
const LEADER_HEAD = ["date", "tourn", "surf", "level", "wl", "player", "rank", "seed", "entry", "round", "score", "max", "opp", "orank", "oseed", "oentry", "ohand", "obh", "obday", "oht", "ocountry", "oactive", "tbw", "tbl", "setw", "setl", "time", "aces", "dfs", "pts", "firsts", "fwon", "swon", "games", "saved", "chances", "oaces", "odfs", "opts", "ofirsts", "ofwon", "oswon", "ogames", "osaved", "ochances"];

export class FormatError extends Error {}

// The text of the array literal assigned to `var matchmx`, found by matching
// brackets (strings are skipped, so a "]" inside a name can't end it early).
function arrayText(src: string): string {
  const at = src.indexOf("var matchmx");
  if (at < 0) throw new FormatError("no `var matchmx` in the file");
  const start = src.indexOf("[", at);
  let depth = 0;
  let inString = false;
  for (let i = start; i < src.length; i++) {
    const c = src[i];
    if (inString) {
      if (c === "\\") i++;
      else if (c === '"') inString = false;
    } else if (c === '"') inString = true;
    else if (c === "[") depth++;
    else if (c === "]" && --depth === 0) return src.slice(start, i + 1);
  }
  throw new FormatError("the matchmx array never closes");
}

function readArray(src: string, width: number): string[][] {
  let rows: unknown;
  try {
    rows = JSON.parse(arrayText(src));
  } catch (e) {
    if (e instanceof FormatError) throw e;
    throw new FormatError(`matchmx is not plain JSON: ${(e as Error).message}`);
  }
  if (!Array.isArray(rows)) throw new FormatError("matchmx is not an array");
  return rows.map((r, k) => {
    if (!Array.isArray(r) || r.length < width || !r.every((x) => typeof x === "string")) {
      throw new FormatError(`match ${k + 1}: expected at least ${width} text fields`);
    }
    return r as string[];
  });
}

function pick(head: string[], r: string[], player: string): MatchRow {
  const get = (k: string) => r[head.indexOf(k)];
  return {
    player,
    date: get("date"), tourn: get("tourn"), surf: get("surf"), level: get("level"), round: get("round"),
    opp: get("opp"), score: get("score"),
    pts: get("pts"), fwon: get("fwon"), swon: get("swon"), opts: get("opts"), ofwon: get("ofwon"), oswon: get("oswon"),
  };
}

// The full name in a per-player file (`var fullname = 'Aryna Sabalenka';`).
export function playerFileName(src: string): string {
  const m = /var fullname\s*=\s*'([^']*)'/.exec(src);
  if (!m) throw new FormatError("no `var fullname` in the file");
  return m[1];
}

export function readPlayerFile(src: string): MatchRow[] {
  const name = playerFileName(src);
  return readArray(src, PLAYER_HEAD.length).map((r) => pick(PLAYER_HEAD, r, name));
}

export function readLeaderFile(src: string): MatchRow[] {
  return readArray(src, LEADER_HEAD.length).map((r) => pick(LEADER_HEAD, r, r[LEADER_HEAD.indexOf("player")]));
}

// Tennis Abstract's file name for a player: her name without spaces.
export const playerSlug = (name: string): string => name.replace(/[^A-Za-z]/g, "");

// ---------------------------------------------------------------------------
// Which matches count
// ---------------------------------------------------------------------------

// Tournament levels in Tennis Abstract's codes. G Slam, PM WTA 1000, P WTA
// 500, I WTA 250, F the Finals, W a recently added tour-level match (so far
// only "WTA Beijing" 2026, before Tennis Abstract files it under its usual
// code). Left out: C (WTA 125), D (BJK Cup), O (Olympics), numbers (ITF).
export const TOUR_LEVELS = new Set(["G", "PM", "P", "I", "F", "W"]);

// Why a match is left out, or null if it counts.
export function exclusion(m: MatchRow, start: string, end: string): string | null {
  if (m.surf !== "Hard") return "not hard court";
  if (m.date < start || m.date > end) return "outside the window";
  if (!TOUR_LEVELS.has(m.level)) return `not tour level (level ${m.level || "blank"})`;
  if (/United Cup/i.test(m.tourn)) return "team event";
  if (/^Q\d$/.test(m.round)) return "qualifying"; // Q1-Q3, not QF
  if (/W\/O/.test(m.score)) return "walkover";
  if (/RET|DEF|ABD/.test(m.score)) return "retirement";
  const nums = [m.pts, m.fwon, m.swon, m.opts, m.ofwon, m.oswon];
  if (nums.some((x) => !/^\d+$/.test(x))) return "no stats";
  if (+m.pts === 0 || +m.opts === 0) return "no stats";
  if (+m.fwon + +m.swon > +m.pts || +m.ofwon + +m.oswon > +m.opts) return "stats don't add up";
  return null;
}

// ---------------------------------------------------------------------------
// Dates
// ---------------------------------------------------------------------------

// YYYY-MM-DD <-> YYYYMMDD, and the first day of a 364-day window ending on
// `end` (both ends included): 2026-10-04 -> 2025-10-06.
export const compact = (iso: string) => iso.replaceAll("-", "");
export const iso = (c: string) => `${c.slice(0, 4)}-${c.slice(4, 6)}-${c.slice(6, 8)}`;
export function windowStart(endIso: string): string {
  const d = new Date(`${endIso}T00:00:00Z`);
  if (Number.isNaN(d.getTime()) || d.toISOString().slice(0, 10) !== endIso) throw new RangeError(`not a date: ${endIso}`);
  d.setUTCDate(d.getUTCDate() - 363);
  return d.toISOString().slice(0, 10);
}

// ---------------------------------------------------------------------------
// Totals
// ---------------------------------------------------------------------------

export type Totals = {
  servePointsWon: number;
  servePoints: number;
  returnPointsWon: number;
  returnPoints: number;
  matches: number;
};

// One player's totals over the matches that count. `rows` are her own rows.
export function playerTotals(rows: MatchRow[]): Totals {
  const t: Totals = { servePointsWon: 0, servePoints: 0, returnPointsWon: 0, returnPoints: 0, matches: 0 };
  for (const m of rows) {
    t.servePointsWon += +m.fwon + +m.swon;
    t.servePoints += +m.pts;
    t.returnPointsWon += +m.opts - +m.ofwon - +m.oswon;
    t.returnPoints += +m.opts;
    t.matches++;
  }
  return t;
}

// A match seen from either side has the same key, so a match between two
// top-50 players (listed once under each) is counted once.
export const matchKey = (m: MatchRow) => [m.date, m.tourn, m.round, ...[m.player, m.opp].sort()].join("|");

// Serve points over both players of every distinct match: the tour average.
export function tourTotals(rows: MatchRow[]): { servePointsWon: number; servePoints: number; matches: number } {
  const seen = new Set<string>();
  let won = 0;
  let pts = 0;
  for (const m of rows) {
    const k = matchKey(m);
    if (seen.has(k)) continue;
    seen.add(k);
    won += +m.fwon + +m.swon + +m.ofwon + +m.oswon;
    pts += +m.pts + +m.opts;
  }
  return { servePointsWon: won, servePoints: pts, matches: seen.size };
}
