// The exact calculator: the chance of every outcome of a best-of-three match,
// worked out by going backwards through every possible score.
//
// This is the independent check on the Bend simulator (SPEC.md, Outputs and
// validation). It must never share code with the engine: it is written from
// the tennis rules in SPEC.md, not from engine/*.bend, so a mistake in one is
// unlikely to be repeated in the other.
//
// Probabilities here are ordinary decimals (0.6 = 60%). The "whole numbers out
// of 10,000" rule is for the Bend engine only.

export type Side = "A" | "B";

export const other = (s: Side): Side => (s === "A" ? "B" : "A");

// The 14 possible set scores, as games for A and games for B, in the order
// the simulator prints them (a60 ... a76, b60 ... b76).
export const SET_SCORES: ReadonlyArray<readonly [number, number]> = [
  [6, 0], [6, 1], [6, 2], [6, 3], [6, 4], [7, 5], [7, 6],
  [0, 6], [1, 6], [2, 6], [3, 6], [4, 6], [5, 7], [6, 7],
];

export const SET_SCORE_NAMES = ["a60", "a61", "a62", "a63", "a64", "a75", "a76", "b60", "b61", "b62", "b63", "b64", "b75", "b76"];

// Chance that the server wins a game, winning each point with chance p.
// Counted backwards from every score (x points to y); from 3-3 on, the game
// is a race to be two points clear: the server wins two in a row with
// chance p^2, the receiver with q^2, otherwise it is back to deuce.
export function holdChance(p: number): number {
  const q = 1 - p;
  const deuce = p * p + q * q === 0 ? 0.5 : (p * p) / (p * p + q * q);
  const memo = new Map<string, number>();
  const win = (x: number, y: number): number => {
    if (x >= 4 && x - y >= 2) return 1;
    if (y >= 4 && y - x >= 2) return 0;
    if (x >= 3 && y >= 3 && x === y) return deuce;
    const key = `${x},${y}`;
    const hit = memo.get(key);
    if (hit !== undefined) return hit;
    const v = p * win(x + 1, y) + q * win(x, y + 1);
    memo.set(key, v);
    return v;
  };
  return win(0, 0);
}

// Who serves point number i (from 0) of a tiebreak that `first` starts: one
// point, then two each.
export function tiebreakServer(first: Side, i: number): Side {
  if (i === 0) return first;
  return Math.floor((i - 1) / 2) % 2 === 0 ? other(first) : first;
}

// Chance that A wins a tiebreak to `target` points that `first` starts. pa and
// pb are A's and B's chances of winning a point on their own serve.
export function tiebreakChance(pa: number, pb: number, first: Side, target: number): number {
  const pointA = (i: number): number => (tiebreakServer(first, i) === "A" ? pa : 1 - pb);
  const memo = new Map<string, number>();
  const win = (x: number, y: number): number => {
    if (x >= target && x - y >= 2) return 1;
    if (y >= target && y - x >= 2) return 0;
    if (x === y && x >= target - 1) {
      // Level at target-1 or more: an even number of points has been played,
      // so the next two are one on each player's serve. A must win both to
      // win; losing both loses; otherwise level again.
      const i = x + y;
      const both = pointA(i) * pointA(i + 1);
      const none = (1 - pointA(i)) * (1 - pointA(i + 1));
      return both + none === 0 ? 0.5 : both / (both + none);
    }
    const key = `${x},${y}`;
    const hit = memo.get(key);
    if (hit !== undefined) return hit;
    const p = pointA(x + y);
    const v = p * win(x + 1, y) + (1 - p) * win(x, y + 1);
    memo.set(key, v);
    return v;
  };
  return win(0, 0);
}

// The chance of each final score of a set that `first` serves first, as a
// map from "a-b" to probability. Games alternate serve; at 6-6 there is a
// tiebreak to `target`, started by whoever would serve game 13.
export function setScores(pa: number, pb: number, first: Side, target: number): Map<string, number> {
  const holdA = holdChance(pa);
  const holdB = holdChance(pb);
  const out = new Map<string, number>();
  const add = (k: string, v: number) => out.set(k, (out.get(k) ?? 0) + v);
  // Forward through the scores, carrying the chance of reaching each one.
  let layer = new Map<string, number>([["0,0", 1]]);
  for (let played = 0; played < 12; played++) {
    const next = new Map<string, number>();
    for (const [key, prob] of layer) {
      const [a, b] = key.split(",").map(Number);
      const server = played % 2 === 0 ? first : other(first);
      const aWinsGame = server === "A" ? holdA : 1 - holdB;
      for (const [na, nb, pr] of [[a + 1, b, aWinsGame], [a, b + 1, 1 - aWinsGame]] as const) {
        const reach = prob * pr;
        if (reach === 0) continue;
        if ((na >= 6 && na - nb >= 2) || (nb >= 6 && nb - na >= 2)) add(`${na}-${nb}`, reach);
        else next.set(`${na},${nb}`, (next.get(`${na},${nb}`) ?? 0) + reach);
      }
    }
    layer = next;
  }
  // Only 6-6 is left after 12 games.
  const sixAll = layer.get("6,6") ?? 0;
  const tb = tiebreakChance(pa, pb, first, target);
  add("7-6", sixAll * tb);
  add("6-7", sixAll * (1 - tb));
  return out;
}

export type MatchResult = {
  winA: number; // chance A wins the match
  // Expected number of sets per match ending in each score, keyed a60 .. b76.
  setsPerMatch: Record<string, number>;
};

// Best of three: A's chance of winning, and how often each set score is
// expected, with `first` serving the first game of the match. After each set
// the serve carries on alternating, the tiebreak counting as one game.
export function matchWithFirst(pa: number, pb: number, first: Side, target = 7, finalTarget = 7): MatchResult {
  const setsPerMatch: Record<string, number> = Object.fromEntries(SET_SCORE_NAMES.map((n) => [n, 0]));
  let winA = 0;
  const nameOf = (a: number, b: number): string => {
    const i = SET_SCORES.findIndex(([x, y]) => x === a && y === b);
    if (i < 0) throw new Error(`impossible set score ${a}-${b}`);
    return SET_SCORE_NAMES[i];
  };
  const go = (setsA: number, setsB: number, server: Side, prob: number) => {
    if (setsA === 2) { winA += prob; return; }
    if (setsB === 2) return;
    const deciding = setsA === 1 && setsB === 1;
    for (const [key, p] of setScores(pa, pb, server, deciding ? finalTarget : target)) {
      const [a, b] = key.split("-").map(Number);
      setsPerMatch[nameOf(a, b)] += prob * p;
      const nextServer = (a + b) % 2 === 0 ? server : other(server);
      if (a > b) go(setsA + 1, setsB, nextServer, prob * p);
      else go(setsA, setsB + 1, nextServer, prob * p);
    }
  };
  go(0, 0, first, 1);
  return { winA, setsPerMatch };
}

// The same, with the first server chosen by a fair coin toss.
export function match(pa: number, pb: number, target = 7, finalTarget = 7): MatchResult {
  const a = matchWithFirst(pa, pb, "A", target, finalTarget);
  const b = matchWithFirst(pa, pb, "B", target, finalTarget);
  const setsPerMatch: Record<string, number> = {};
  for (const n of SET_SCORE_NAMES) setsPerMatch[n] = (a.setsPerMatch[n] + b.setsPerMatch[n]) / 2;
  return { winA: (a.winA + b.winA) / 2, setsPerMatch };
}

// Each set score's share of all sets played (each row sums to 1).
export function setShares(setsPerMatch: Record<string, number>): Record<string, number> {
  const total = SET_SCORE_NAMES.reduce((s, n) => s + setsPerMatch[n], 0);
  return Object.fromEntries(SET_SCORE_NAMES.map((n) => [n, setsPerMatch[n] / total]));
}
