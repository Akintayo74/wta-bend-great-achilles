// Tests for prep/results.ts: reading data/field.csv into a draw, and checking
// the engine's output before it reaches the results page.
//
// Run: node --test prep/*.test.ts

import { test } from "node:test";
import assert from "node:assert/strict";
import type { Player } from "./model.ts";
import { ratio } from "./ratio.ts";
import { readField, readFinals, readMatchup } from "./results.ts";

const NAMES = ["Aryna Sabalenka", "Elena Rybakina", "Iga Swiatek", "Coco Gauff", "Jessica Pegula", "Amanda Anisimova", "Mirra Andreeva", "Madison Keys", "Belinda Bencic"];
const players: Player[] = NAMES.map((name, i) => ({
  name, id: name.split(" ")[1], serve: ratio(6, 10), ret: ratio(4, 10),
  servePoints: 1000, returnPoints: 1000, matches: 40, checked: i < 2, source: "test",
}));
const field = (groups: string[] = Array(8).fill(""), names = NAMES.slice(0, 8)) =>
  "seed,name,group\n" + names.map((n, i) => `${i + 1},${n},${groups[i] ?? ""}`).join("\n") + "\n";

test("field: blank groups give the seeded draw, with ids and check marks", () => {
  const { field: f, problems } = readField(field(), players);
  assert.deepEqual(problems, []);
  assert.equal(f!.draw, "seeded");
  assert.deepEqual(f!.entries.map((e) => e.id), ["Sabalenka", "Rybakina", "Swiatek", "Gauff", "Pegula", "Anisimova", "Andreeva", "Keys"]);
  assert.deepEqual(f!.entries.map((e) => e.checked), [true, true, false, false, false, false, false, false]);
});

test("field: known groups become the draw letters (lower case accepted)", () => {
  const { field: f, problems } = readField(field("A b B a A B B A".split(" ")), players);
  assert.deepEqual(problems, []);
  assert.equal(f!.draw, "ABBAABBA");
});

test("field: refuses bad fields and says why", () => {
  const bad = (text: string, needle: string) => {
    const { field: f, problems } = readField(text, players);
    assert.equal(f, null);
    assert.ok(problems.some((p) => p.includes(needle)), `expected "${needle}" in ${JSON.stringify(problems)}`);
  };
  bad("seed,name\n", "columns must be");
  bad(field(undefined, NAMES.slice(0, 7)), "exactly 8 players");
  bad(field(undefined, [...NAMES.slice(0, 7), "Venus Williams"]), "not in data/players.csv");
  bad(field(undefined, [...NAMES.slice(0, 7), "Aryna Sabalenka"]), "appears twice");
  bad(field("A B B A A B B".split(" ")), "all eight players or for none");
  bad(field("A A A A A B B B".split(" ")), "four players");
  bad(field("A B B A A B B C".split(" ")), "group must be A, B or blank");
  bad(field().replace("2,Elena", "3,Elena"), "seeds must be 1 to 8 in order");
});

const f = readField(field(), players).field!;
const finals = (rows: number[][], unfinished = 0) =>
  "seed_no,player,semifinals,finals,titles,unfinished\n" +
  f.entries.map((e, i) => `${e.seed},${e.id},${rows[i].join(",")},${unfinished}`).join("\n") + "\n";
// 10 runs: each player's semifinals, finals, titles. Totals 40, 20, 10.
const good = [[8, 6, 4], [7, 5, 3], [6, 3, 1], [5, 2, 1], [5, 2, 1], [4, 1, 0], [3, 1, 0], [2, 0, 0]];

test("finals: reads the counts in seed order", () => {
  const { players: ps, unfinished } = readFinals(finals(good), f, 10);
  assert.equal(unfinished, 0);
  assert.deepEqual(ps.map((p) => [p.semifinals, p.finals, p.titles]), good);
  assert.equal(ps[0].name, "Aryna Sabalenka");
});

test("finals: totals must add up, allowing for unfinished runs", () => {
  assert.throws(() => readFinals(finals(good), f, 11), /don't add up/);
  // One run unfinished: 9 titles, 18 finals, 36 semifinals.
  const short = good.map((r) => [...r]);
  short[0] = [4, 4, 3];
  assert.equal(readFinals(finals(short, 1), f, 10).unfinished, 1);
  const wrongTitles = good.map((r) => [...r]);
  wrongTitles[7][2] = 1;
  assert.throws(() => readFinals(finals(wrongTitles), f, 10), /don't add up/);
});

test("finals: refuses rows out of order or missing", () => {
  const swapped = finals(good).split("\n");
  [swapped[1], swapped[2]] = [swapped[2], swapped[1]];
  assert.throws(() => readFinals(swapped.join("\n"), f, 10), /expected Sabalenka/);
  assert.throws(() => readFinals(finals(good).split("\n").slice(0, 8).join("\n") + "\n", f, 10), /7 rows/);
});

test("matchup: reads one row and checks it adds up", () => {
  const head = "player_a,player_b,chance_a,chance_b,a_wins,b_wins,unfinished\n";
  assert.deepEqual(readMatchup(head + "Sabalenka,Keys,6600,5900,70,30,0\n", 100), {
    a: "Sabalenka", b: "Keys", chanceA: 6600, chanceB: 5900, aWins: 70, bWins: 30, unfinished: 0,
  });
  assert.throws(() => readMatchup(head + "Sabalenka,Keys,6600,5900,70,29,0\n", 100), /don't add up/);
  assert.throws(() => readMatchup(head, 100), /0 rows/);
});
