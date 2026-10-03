// Tests for the exact calculator.   Run: node --test prep/*.test.ts
import { test } from "node:test";
import assert from "node:assert/strict";
import { holdChance, match, matchWithFirst, setScores, tiebreakChance, tiebreakServer, SET_SCORE_NAMES } from "./exact.ts";

const close = (x: number, y: number, eps = 1e-12) => assert.ok(Math.abs(x - y) < eps, `${x} vs ${y}`);

test("a 50% server holds half the time", () => close(holdChance(0.5), 0.5));

test("hold chance matches the textbook closed form", () => {
  for (const p of [0.4, 0.55, 0.6, 0.75]) {
    const q = 1 - p;
    const closed = p ** 4 * (1 + 4 * q + 10 * q * q) + 20 * p ** 3 * q ** 3 * (p * p / (1 - 2 * p * q));
    close(holdChance(p), closed);
  }
});

test("tiebreak serve pattern: A, B, B, A, A, B, B", () => {
  assert.deepEqual([0, 1, 2, 3, 4, 5, 6].map((i) => tiebreakServer("A", i)), ["A", "B", "B", "A", "A", "B", "B"]);
});

test("equal players: tiebreak and match are 50/50", () => {
  close(tiebreakChance(0.6, 0.6, "A", 7), 0.5);
  close(match(0.62, 0.62).winA, 0.5);
});

test("certain servers: a 100% server never loses a set", () => {
  const m = match(1, 0.5);
  close(m.winA, 1);
  for (const n of SET_SCORE_NAMES.filter((n) => n.startsWith("b"))) close(m.setsPerMatch[n], 0);
});

test("set score chances add up to 1", () => {
  let total = 0;
  for (const v of setScores(0.6, 0.55, "B", 7).values()) total += v;
  close(total, 1);
});

test("swapping players swaps the result", () => {
  close(match(0.6, 0.55).winA + match(0.55, 0.6).winA, 1);
});

// Newton and Keller (2005): with independent points, who serves first does
// not change the chance of winning a match.
test("who serves first does not change the match chance", () => {
  close(matchWithFirst(0.66, 0.52, "A").winA, matchWithFirst(0.66, 0.52, "B").winA);
});

// SPEC.md, Point model: A 62% serve / 45% return, B 58% / 42%, tour average 56%.
test("reproduces the spec's worked example (67.7% average, 81.6% additive)", () => {
  const [sA, rA, sB, rB, tour] = [0.62, 0.45, 0.58, 0.42, 0.56];
  const avg = match((sA + (1 - rB)) / 2, (sB + (1 - rA)) / 2).winA;
  const add = match(sA + (1 - rB) - tour, sB + (1 - rA) - tour).winA;
  assert.equal((avg * 100).toFixed(1), "67.7");
  assert.equal((add * 100).toFixed(1), "81.6");
});
