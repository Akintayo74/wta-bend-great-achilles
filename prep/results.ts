// The final run's pieces that don't touch files or processes: reading the
// field, turning it into a draw for build/finals, and turning the engine's
// CSV output into the numbers the results page shows.
//
// data/field.csv lists the eight players in Race to the Finals order (seed 1
// first), by their names in data/players.csv. The group column is blank until
// the real draw is made (then the engine draws groups by lot in every run,
// rulebook VI.B.3), or A/B for every player once it is known.

import { parseCsv } from "./csv.ts";
import type { Player } from "./model.ts";

export const FIELD_COLUMNS = ["seed", "name", "group"];

export type Entry = { seed: number; name: string; id: string; group: "A" | "B" | ""; checked: boolean };
export type Field = { entries: Entry[]; draw: string }; // draw: "seeded" or eight letters A/B

// The field, or every problem with it.
export function readField(text: string, players: Player[]): { field: Field | null; problems: string[] } {
  const problems: string[] = [];
  let rows;
  try {
    const csv = parseCsv(text);
    if (csv.header.join(",") !== FIELD_COLUMNS.join(",")) return { field: null, problems: [`field.csv: columns must be ${FIELD_COLUMNS.join(",")}`] };
    rows = csv.rows;
  } catch (e) {
    return { field: null, problems: [`field.csv: ${(e as Error).message}`] };
  }
  if (rows.length !== 8) problems.push(`field.csv: needs exactly 8 players, found ${rows.length}`);
  const entries: Entry[] = [];
  rows.forEach((r, i) => {
    const where = `field.csv row ${i + 2}`;
    if (r.seed !== String(i + 1)) problems.push(`${where}: seeds must be 1 to 8 in order, got "${r.seed}"`);
    const p = players.find((q) => q.name === r.name.trim());
    if (!p) problems.push(`${where}: "${r.name}" is not in data/players.csv`);
    if (entries.some((e) => e.name === r.name.trim())) problems.push(`${where}: "${r.name}" appears twice`);
    const g = r.group.trim().toUpperCase();
    if (g !== "" && g !== "A" && g !== "B") problems.push(`${where}: group must be A, B or blank, got "${r.group}"`);
    entries.push({ seed: i + 1, name: r.name.trim(), id: p?.id ?? "", group: g as Entry["group"], checked: p?.checked ?? false });
  });
  const groups = entries.map((e) => e.group);
  let draw = "seeded";
  if (groups.some((g) => g !== "")) {
    if (groups.some((g) => g === "")) problems.push("field.csv: give a group for all eight players or for none");
    else if (groups.filter((g) => g === "A").length !== 4) problems.push("field.csv: each group needs four players");
    else draw = groups.join("");
  }
  return problems.length > 0 ? { field: null, problems } : { field: { entries, draw }, problems };
}

export type PlayerResult = Entry & { semifinals: number; finals: number; titles: number };

// build/finals output: one row per seed, in seed order.
export function readFinals(text: string, field: Field, runs: number): { players: PlayerResult[]; unfinished: number } {
  const { rows } = parseCsv(text);
  if (rows.length !== 8) throw new Error(`build/finals printed ${rows.length} rows, expected 8`);
  const players = field.entries.map((e, i) => {
    const r = rows[i];
    if (r.seed_no !== String(e.seed) || r.player !== e.id) throw new Error(`build/finals row ${i + 1} is ${r.player}, expected ${e.id}`);
    return { ...e, semifinals: +r.semifinals, finals: +r.finals, titles: +r.titles };
  });
  const unfinished = +rows[0].unfinished;
  // Every finished tournament has one champion, two finalists, four semifinalists.
  const done = runs - unfinished;
  const sum = (k: "semifinals" | "finals" | "titles") => players.reduce((a, p) => a + p[k], 0);
  if (sum("titles") !== done || sum("finals") !== 2 * done || sum("semifinals") !== 4 * done) {
    throw new Error(`build/finals totals don't add up: ${sum("titles")} titles, ${sum("finals")} finals, ${sum("semifinals")} semifinals for ${done} finished runs`);
  }
  return { players, unfinished };
}

export type Matchup = { a: string; b: string; chanceA: number; chanceB: number; aWins: number; bWins: number; unfinished: number };

// One build/matchup output (header and one row).
export function readMatchup(text: string, runs: number): Matchup {
  const { rows } = parseCsv(text);
  if (rows.length !== 1) throw new Error(`build/matchup printed ${rows.length} rows, expected 1`);
  const r = rows[0];
  const m = { a: r.player_a, b: r.player_b, chanceA: +r.chance_a, chanceB: +r.chance_b, aWins: +r.a_wins, bWins: +r.b_wins, unfinished: +r.unfinished };
  if (m.aWins + m.bWins + m.unfinished !== runs) throw new Error(`build/matchup ${m.a} v ${m.b}: wins don't add up to ${runs}`);
  return m;
}
