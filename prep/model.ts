// The point model: from data/players.csv and data/tour.csv to every point
// chance, as whole numbers out of 10,000.
//
// For a server s and a receiver r (SPEC.md, Point model):
//   average:  (serve_s + (1 - return_r)) / 2
//   additive:  serve_s + (1 - return_r) - tour serve average
// where serve_s = serve points won / serve points, and so on. The sums are
// done in exact fractions and rounded once, at the end, to the nearest whole
// number out of 10,000 (an exact half goes up). A chance outside 0% to 100%
// is a problem to report, never clamped (law L1).
//
// Nothing here is shared with the Bend engine or with the exact calculator.

import { parseCsv } from "./csv.ts";
import { add, cmp, half, ONE, parseDecimal, percent, type Ratio, ratio, sub, toTenThousandths, ZERO } from "./ratio.ts";

export const PLAYER_COLUMNS = ["name", "serve_points_won", "serve_points", "return_points_won", "return_points", "matches", "window_start", "window_end", "checked_spw", "checked_rpw", "source"];
export const TOUR_COLUMNS = ["surface", "serve_points_won", "serve_points", "matches", "window_start", "window_end", "source"];

// How far (in percentage points) a computed SPW or RPW may be from the one
// typed from the player's page.
export const CHECK_TOLERANCE = ratio(1, 2);

export type Player = {
  name: string;
  id: string; // the name in Bend: her surname, e.g. Sabalenka
  serve: Ratio; // share of serve points won
  ret: Ratio; // share of return points won
  servePoints: number;
  returnPoints: number;
  matches: number;
  checked: boolean; // SPW and RPW typed from her page, and they agree
  source: string;
};

export type Inputs = {
  players: Player[];
  tour: Ratio; // tour serve average
  tourPoints: number;
  tourMatches: number;
  window: { start: string; end: string }; // the players' window
  tourWindow: { start: string; end: string };
};

export type Method = "average" | "additive";
export const METHODS: Method[] = ["average", "additive"];

const isCount = (s: string) => /^\d+$/.test(s);
const isDate = (s: string) => /^\d{4}-\d{2}-\d{2}$/.test(s) && !Number.isNaN(Date.parse(`${s}T00:00:00Z`));

// Her name in Bend: the last word of her name, letters only ("Bouzas
// Maneiro" -> "Maneiro"); if two players share it, the whole name.
function makeIds(names: string[]): string[] {
  const cap = (w: string) => w.charAt(0).toUpperCase() + w.slice(1);
  const last = names.map((n) => cap(n.trim().split(/\s+/).at(-1)!.replace(/[^A-Za-z]/g, "")));
  return names.map((n, i) =>
    last.filter((x) => x === last[i]).length > 1 ? n.split(/\s+/).map((w) => cap(w.replace(/[^A-Za-z]/g, ""))).join("") : last[i],
  );
}

// Read and check both files. Returns every problem found, not just the first.
export function readInputs(playersText: string, tourText: string): { inputs: Inputs | null; problems: string[] } {
  const problems: string[] = [];
  const say = (where: string, what: string) => problems.push(`${where}: ${what}`);

  // --- tour.csv ---
  let tour: Ratio | null = null;
  let tourPoints = 0;
  let tourMatches = 0;
  let tourWindow = { start: "", end: "" };
  try {
    const { header, rows } = parseCsv(tourText);
    if (header.join(",") !== TOUR_COLUMNS.join(",")) say("tour.csv", `columns must be ${TOUR_COLUMNS.join(",")}`);
    else {
      const hard = rows.filter((r) => r.surface === "Hard");
      if (hard.length !== 1) say("tour.csv", `needs exactly one Hard row, found ${hard.length}`);
      else {
        const r = hard[0];
        if (!isCount(r.serve_points_won) || !isCount(r.serve_points) || +r.serve_points === 0) say("tour.csv", "serve points must be whole numbers, points above 0");
        else if (+r.serve_points_won > +r.serve_points) say("tour.csv", "more serve points won than played");
        else {
          tour = ratio(BigInt(r.serve_points_won), BigInt(r.serve_points));
          tourPoints = +r.serve_points;
        }
        if (!isCount(r.matches)) say("tour.csv", "matches must be a whole number");
        tourMatches = +r.matches;
        if (!isDate(r.window_start) || !isDate(r.window_end)) say("tour.csv", "window dates must be YYYY-MM-DD");
        if (r.source.trim() === "") say("tour.csv", "source is blank");
        tourWindow = { start: r.window_start, end: r.window_end };
      }
    }
  } catch (e) {
    say("tour.csv", (e as Error).message);
  }

  // --- players.csv ---
  const players: Player[] = [];
  const windows = new Set<string>();
  try {
    const { header, rows } = parseCsv(playersText);
    if (header.join(",") !== PLAYER_COLUMNS.join(",")) say("players.csv", `columns must be ${PLAYER_COLUMNS.join(",")}`);
    else if (rows.length === 0) say("players.csv", "no players");
    else {
      const ids = makeIds(rows.map((r) => r.name));
      const seen = new Set<string>();
      rows.forEach((r, k) => {
        const where = `players.csv line ${k + 2} (${r.name || "no name"})`;
        const before = problems.length;
        if (r.name.trim() === "") say(where, "name is blank");
        if (seen.has(r.name)) say(where, "name appears twice");
        seen.add(r.name);
        if (!/^[A-Z][A-Za-z]*$/.test(ids[k])) say(where, `can't make a Bend name from "${r.name}"`);
        for (const c of ["serve_points_won", "serve_points", "return_points_won", "return_points", "matches"]) {
          if (r[c] === "") say(where, `${c} is blank`);
          else if (!isCount(r[c])) say(where, `${c} must be a whole number, got "${r[c]}"`);
        }
        if (problems.length === before) {
          if (+r.serve_points === 0) say(where, "serve_points is 0");
          if (+r.return_points === 0) say(where, "return_points is 0");
          if (+r.serve_points_won > +r.serve_points) say(where, "more serve points won than played");
          if (+r.return_points_won > +r.return_points) say(where, "more return points won than played");
        }
        if (!isDate(r.window_start) || !isDate(r.window_end)) say(where, "window dates must be YYYY-MM-DD");
        windows.add(`${r.window_start} to ${r.window_end}`);
        if (r.source.trim() === "") say(where, "source is blank");
        if (problems.length !== before) return;

        const serve = ratio(BigInt(r.serve_points_won), BigInt(r.serve_points));
        const ret = ratio(BigInt(r.return_points_won), BigInt(r.return_points));
        // The hand check against her Tennis Abstract page.
        let checked = true;
        for (const [col, value, label] of [["checked_spw", serve, "SPW"], ["checked_rpw", ret, "RPW"]] as const) {
          if (r[col].trim() === "") {
            checked = false;
            continue;
          }
          const typed = parseDecimal(r[col]);
          if (typed === null || cmp(typed, ZERO) < 0 || cmp(typed, ratio(100)) > 0) {
            say(where, `${col} must be a percentage such as 62.4, got "${r[col]}"`);
            continue;
          }
          const computed = ratio(value.n * 100n, value.d);
          const gap = sub(computed, typed);
          const off = cmp(gap, ZERO) < 0 ? ratio(-gap.n, gap.d) : gap;
          if (cmp(off, CHECK_TOLERANCE) > 0) {
            say(where, `${label} from the data is ${percent(value, 1)}%, the page says ${r[col]}% (more than 0.5 points apart)`);
          }
        }
        players.push({
          name: r.name, id: ids[k], serve, ret, servePoints: +r.serve_points, returnPoints: +r.return_points,
          matches: +r.matches, checked, source: r.source,
        });
      });
      if (windows.size > 1) say("players.csv", `players come from different snapshots: ${[...windows].join("; ")}`);
    }
  } catch (e) {
    say("players.csv", (e as Error).message);
  }

  if (problems.length > 0 || tour === null) return { inputs: null, problems };
  const [start, end] = [...windows][0].split(" to ");
  return { inputs: { players, tour, tourPoints, tourMatches, window: { start, end }, tourWindow }, problems };
}

// The server's chance of winning a point, as an exact fraction.
export function exactChance(method: Method, server: Player, receiver: Player, tour: Ratio): Ratio {
  const edge = add(server.serve, sub(ONE, receiver.ret)); // serve_s + (1 - return_r)
  return method === "average" ? half(edge) : sub(edge, tour);
}

// chances[method][i][j]: player i serving to player j, out of 10,000.
export type Chances = Record<Method, number[][]>;

// Every chance for both methods, or the list of those outside 0% to 100%.
export function allChances(inp: Inputs): { chances: Chances | null; problems: string[] } {
  const problems: string[] = [];
  const chances = {} as Chances;
  for (const method of METHODS) {
    chances[method] = inp.players.map((s) =>
      inp.players.map((r) => {
        const x = exactChance(method, s, r, inp.tour);
        if (cmp(x, ZERO) < 0 || cmp(x, ONE) > 0) {
          problems.push(`${method}: ${s.name} serving vs ${r.name} = ${percent(x, 2)}% (${cmp(x, ZERO) < 0 ? "below 0%" : "above 100%"})`);
          return -1;
        }
        return Number(toTenThousandths(x));
      }),
    );
  }
  return problems.length > 0 ? { chances: null, problems } : { chances, problems };
}
