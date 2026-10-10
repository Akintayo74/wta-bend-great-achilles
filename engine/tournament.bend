# tournament.bend: groups, standings and knockouts.
#
# Milestone 6. Laws L15-L19 and L28-L30 are in LAWS.bend and proven in
# PROOF.bend.
#
# The standings code follows the shape of the rule in LAWS.bend step by step.
# That is deliberate: Bend compares unfinished computations by the names of
# the functions they are stuck in, so a proof that two functions agree goes
# helper by helper, and matching shapes keep those proofs short.
#
# The rules come from the 2026 WTA Rulebook, Section VI.B, copied into
# data/rules/wta-finals-2026.txt.

import Base
import ./scoring.bend as S
import ./sim.bend as Sim
import ./params.bend as P

# ---------------------------------------------------------------------------
# The field and the groups
# ---------------------------------------------------------------------------

# The eight players, in Race to the Finals order: p1 is seed 1. Seeds are the
# numbers 1 to 8 everywhere below. `m` is the point model (SPEC.md, decision 6).
type Field is Data:
  Field{m: P.Method, p1: P.Player, p2: P.Player, p3: P.Player, p4: P.Player, p5: P.Player, p6: P.Player, p7: P.Player, p8: P.Player}

# A group of four, by seed, in draw order.
type Group is Data:
  Group{s1: Nat, s2: Nat, s3: Nat, s4: Nat}

# How the groups are made: by the seeded draw (rulebook VI.B.3), or given
# (the real groups once the draw has happened, or a what-if).
type Draw is Data:
  Seeded{}
  Fixed{a: Group, b: Group}

# A place in a group's draw order: the player in s1 is at P1, and so on.
type Pos is Data:
  P1{}
  P2{}
  P3{}
  P4{}

# ---------------------------------------------------------------------------
# Round robin and standings
# ---------------------------------------------------------------------------

# One finished match: who won (A is the first-named player) and the set
# scores, most recent first, A's games first (as in scoring.bend).
type Finished is Data:
  Finished{winner: S.Side, sets: List<&2, S.Score>}

# A group's six matches. rXY is the match between the players at PX and PY,
# with the one at PX as player A.
type RoundRobin is Data:
  RoundRobin{r12: Finished, r13: Finished, r14: Finished, r23: Finished, r24: Finished, r34: Finished}

# Final places in a group, 1 to 4, of the players at P1, P2, P3 and P4.
type Places is Data:
  Places{p1: Nat, p2: Nat, p3: Nat, p4: Nat}

# ---------------------------------------------------------------------------
# Knockouts and the whole event
# ---------------------------------------------------------------------------

# The semifinal lines, by seed (rulebook VI.B.4.c). The first semifinal is
# line 1 against line 2, the second line 3 against line 4.
type Semis is Data:
  Semis{line1: Nat, line2: Nat, line3: Nat, line4: Nat}

# How one simulated tournament ended. Complete: every match was finished, with the
# groups, their results, the semifinal lines and results, the two finalists,
# the final and the champion. Unfinished: some match hit the 1,000-point cap
# (L27), so the run is not counted as anyone's.
type Outcome is Data:
  Complete{ga: Group, gb: Group, ra: RoundRobin, rb: RoundRobin, semis: Semis, sf1: Finished, sf2: Finished, finalist1: Nat, finalist2: Nat, final: Finished, champion: Nat}
  Unfinished{}

# A number for each seed.
type Counts is Data:
  Counts{s1: Nat, s2: Nat, s3: Nat, s4: Nat, s5: Nat, s6: Nat, s7: Nat, s8: Nat}

# The totals over many tournaments: titles, finals reached and semifinals
# reached by each seed, and unfinished runs.
type Tally is Data:
  Tally{titles: Counts, finals: Counts, semis: Counts, unfinished: Nat}

# ---------------------------------------------------------------------------
# The seeded draw: L15
# ---------------------------------------------------------------------------

# Rulebook VI.B.3.b: seed 1 in group A and seed 2 in group B; of seeds 3 and
# 4, the one drawn first goes into group A and the other into group B; the
# same for 5 and 6, and for 7 and 8. Each lot is True when the
# lower-numbered seed of the pair is drawn first.
def Draw.seeded(+l34: Bool, +l56: Bool, +l78: Bool) -> Group & Group:
  (Group{1n, S.Match.choose(l34, 3n, 4n), S.Match.choose(l56, 5n, 6n), S.Match.choose(l78, 7n, 8n)}, Group{2n, S.Match.choose(l34, 4n, 3n), S.Match.choose(l56, 6n, 5n), S.Match.choose(l78, 8n, 7n)})

# ---------------------------------------------------------------------------
# Standings: L16, L17, L28
# ---------------------------------------------------------------------------

# A player's round-robin record: wins, sets won and lost, games won and lost.
type Record is Data:
  Record{wins: Nat, sets_won: Nat, sets_lost: Nat, games_won: Nat, games_lost: Nat}

def Standings.games_for(s: S.Side, sc: S.Score) -> Nat:
  match s sc:
    case S.A{} S.Score{a, _}:
      a
    case S.B{} S.Score{_, b}:
      b

# The games player s won in a list of sets.
def Standings.games_won(+s: S.Side, done: List<&2, S.Score>) -> Nat:
  match done:
    case Nil{}:
      0n
    case Con{sc, rest}:
      Nat.add(Standings.games_for(s, sc), Standings.games_won(s, rest))

# What one match adds to the record of the player on side s.
def Standings.entry(+s: S.Side, r: Finished) -> Record:
  match r:
    case Finished{w, +sets}:
      Record{S.Match.count(S.Match.same(w, s), 0n), S.Match.sets_won(s, sets), S.Match.sets_won(S.Side.other(s), sets), Standings.games_won(s, sets), Standings.games_won(S.Side.other(s), sets)}

def Standings.plus(x: Record, y: Record) -> Record:
  match x y:
    case Record{a1, b1, c1, d1, e1} Record{a2, b2, c2, d2, e2}:
      Record{Nat.add(a1, a2), Nat.add(b1, b2), Nat.add(c1, c2), Nat.add(d1, d2), Nat.add(e1, e2)}

def Standings.plus3(x: Record, y: Record, z: Record) -> Record:
  Standings.plus(x, Standings.plus(y, z))

# The record of the player at position x, over her three matches.
def Standings.record(x: Pos, rr: RoundRobin) -> Record:
  match x rr:
    case P1{} RoundRobin{r12, r13, r14, _, _, _}:
      Standings.plus3(Standings.entry(S.A{}, r12), Standings.entry(S.A{}, r13), Standings.entry(S.A{}, r14))
    case P2{} RoundRobin{r12, _, _, r23, r24, _}:
      Standings.plus3(Standings.entry(S.B{}, r12), Standings.entry(S.A{}, r23), Standings.entry(S.A{}, r24))
    case P3{} RoundRobin{_, r13, _, r23, _, r34}:
      Standings.plus3(Standings.entry(S.B{}, r13), Standings.entry(S.B{}, r23), Standings.entry(S.A{}, r34))
    case P4{} RoundRobin{_, _, r14, _, r24, r34}:
      Standings.plus3(Standings.entry(S.B{}, r14), Standings.entry(S.B{}, r24), Standings.entry(S.B{}, r34))

def Standings.wins_of(r: Record) -> Nat:
  match r:
    case Record{w, _, _, _, _}:
      w

def Standings.wins(x: Pos, rr: RoundRobin) -> Nat:
  Standings.wins_of(Standings.record(x, rr))

# Compares w1 / (w1 + l1) with w2 / (w2 + l2) exactly, by cross-multiplying.
def Standings.share_cmp(+w1: Nat, l1: Nat, +w2: Nat, l2: Nat) -> Cmp:
  Nat.cmp(Nat.mul(w1, Nat.max(1n, Nat.add(w2, l2))), Nat.mul(w2, Nat.max(1n, Nat.add(w1, l1))))

def Standings.set_cmp.go(y: Record, x: Record) -> Cmp:
  match y x:
    case Record{_, +yw, yl, _, _} Record{_, +xw, xl, _, _}:
      Standings.share_cmp(yw, yl, xw, xl)

def Standings.game_cmp.go(y: Record, x: Record) -> Cmp:
  match y x:
    case Record{_, _, _, +yw, yl} Record{_, _, _, +xw, xl}:
      Standings.share_cmp(yw, yl, xw, xl)

def Standings.set_cmp(+y: Pos, +x: Pos, +rr: RoundRobin) -> Cmp:
  Standings.set_cmp.go(Standings.record(y, rr), Standings.record(x, rr))

def Standings.game_cmp(+y: Pos, +x: Pos, +rr: RoundRobin) -> Cmp:
  Standings.game_cmp.go(Standings.record(y, rr), Standings.record(x, rr))

def Standings.won_as(s: S.Side, r: Finished) -> Bool:
  match r:
    case Finished{w, _}:
      S.Match.same(w, s)

# Head-to-head: did the player at y beat the player at x?
def Standings.beat(y: Pos, x: Pos, rr: RoundRobin) -> Bool:
  match y x rr:
    case P1{} P2{} RoundRobin{r, _, _, _, _, _}:
      Standings.won_as(S.A{}, r)
    case P2{} P1{} RoundRobin{r, _, _, _, _, _}:
      Standings.won_as(S.B{}, r)
    case P1{} P3{} RoundRobin{_, r, _, _, _, _}:
      Standings.won_as(S.A{}, r)
    case P3{} P1{} RoundRobin{_, r, _, _, _, _}:
      Standings.won_as(S.B{}, r)
    case P1{} P4{} RoundRobin{_, _, r, _, _, _}:
      Standings.won_as(S.A{}, r)
    case P4{} P1{} RoundRobin{_, _, r, _, _, _}:
      Standings.won_as(S.B{}, r)
    case P2{} P3{} RoundRobin{_, _, _, r, _, _}:
      Standings.won_as(S.A{}, r)
    case P3{} P2{} RoundRobin{_, _, _, r, _, _}:
      Standings.won_as(S.B{}, r)
    case P2{} P4{} RoundRobin{_, _, _, _, r, _}:
      Standings.won_as(S.A{}, r)
    case P4{} P2{} RoundRobin{_, _, _, _, r, _}:
      Standings.won_as(S.B{}, r)
    case P3{} P4{} RoundRobin{_, _, _, _, _, r}:
      Standings.won_as(S.A{}, r)
    case P4{} P3{} RoundRobin{_, _, _, _, _, r}:
      Standings.won_as(S.B{}, r)
    case _ _ _:
      False{}

def Standings.seed(x: Pos, g: Group) -> Nat:
  match x g:
    case P1{} Group{s, _, _, _}:
      s
    case P2{} Group{_, s, _, _}:
      s
    case P3{} Group{_, _, s, _}:
      s
    case P4{} Group{_, _, _, s}:
      s

# The Race to the Finals Leaderboard: the better (lower) seed ranks higher.
def Standings.race(+y: Pos, +x: Pos, +g: Group) -> Bool:
  Nat.is_lt(Standings.seed(y, g), Standings.seed(x, g))

def Standings.decide(c: Cmp, level: Bool) -> Bool:
  match c:
    case GT{}:
      True{}
    case LT{}:
      False{}
    case EQ{}:
      level

def Standings.either(c: Bool, yes: Bool, no: Bool) -> Bool:
  match c:
    case True{}:
      yes
    case False{}:
      no

# y against x when y, x and k are tied on wins (rulebook VI.B.4.b.iv): set
# percentage; if y and x are level and k is not, head-to-head; if all three
# are level, game percentage the same way; then the Race.
def Standings.three_way(+y: Pos, +x: Pos, +k: Pos, +g: Group, +rr: RoundRobin) -> Bool:
  Standings.decide(Standings.set_cmp(y, x, rr), Standings.either(Cmp.is_eq(Standings.set_cmp(k, x, rr)), Standings.decide(Standings.game_cmp(y, x, rr), Standings.either(Cmp.is_eq(Standings.game_cmp(k, x, rr)), Standings.race(y, x, g), Standings.beat(y, x, rr))), Standings.beat(y, x, rr)))

def Standings.tied(z_tied: Bool, w_tied: Bool, +y: Pos, +x: Pos, +z: Pos, +w: Pos, +g: Group, +rr: RoundRobin) -> Bool:
  match z_tied w_tied:
    case False{} False{}:
      Standings.beat(y, x, rr)
    case True{} False{}:
      Standings.three_way(y, x, z, g, rr)
    case False{} True{}:
      Standings.three_way(y, x, w, g, rr)
    case True{} True{}:
      Standings.race(y, x, g)

# Does the player at y finish above the player at x? z and w are the other
# two.
def Standings.ahead(+y: Pos, +x: Pos, +z: Pos, +w: Pos, +g: Group, +rr: RoundRobin) -> Bool:
  Standings.decide(Nat.cmp(Standings.wins(y, rr), Standings.wins(x, rr)), Standings.tied(Nat.is_eq(Standings.wins(z, rr), Standings.wins(x, rr)), Nat.is_eq(Standings.wins(w, rr), Standings.wins(x, rr)), y, x, z, w, g, rr))

# The place of the player at x: 1 plus the number of players above her.
def Standings.place(+x: Pos, +y: Pos, +z: Pos, +w: Pos, +g: Group, +rr: RoundRobin) -> Nat:
  S.Match.count(Standings.ahead(y, x, z, w, g, rr), S.Match.count(Standings.ahead(z, x, y, w, g, rr), S.Match.count(Standings.ahead(w, x, y, z, g, rr), 1n)))

# A group's final places (L16, L17, L28).
def Standings.places(+g: Group, +rr: RoundRobin) -> Places:
  Places{Standings.place(P1{}, P2{}, P3{}, P4{}, g, rr), Standings.place(P2{}, P1{}, P3{}, P4{}, g, rr), Standings.place(P3{}, P1{}, P2{}, P4{}, g, rr), Standings.place(P4{}, P1{}, P2{}, P3{}, g, rr)}

# ---------------------------------------------------------------------------
# Knockouts: L19
# ---------------------------------------------------------------------------

# The seed placed n-th in a group.
def Knockout.at_place(+n: Nat, g: Group, pl: Places) -> Nat:
  match g pl:
    case Group{s1, s2, s3, s4} Places{p1, p2, p3, _}:
      S.Match.choose(Nat.is_eq(p1, n), s1, S.Match.choose(Nat.is_eq(p2, n), s2, S.Match.choose(Nat.is_eq(p3, n), s3, s4)))

# The semifinal lines (rulebook VI.B.4.c): A's winner on line 1, B's
# runner-up on line 2, A's runner-up on line 3, B's winner on line 4.
def Knockout.semis(+ga: Group, +pa: Places, +gb: Group, +pb: Places) -> Semis:
  Semis{Knockout.at_place(1n, ga, pa), Knockout.at_place(2n, gb, pb), Knockout.at_place(2n, ga, pa), Knockout.at_place(1n, gb, pb)}

def Knockout.on_line(n: Nat, sm: Semis) -> Nat:
  match n sm:
    case 1n Semis{l, _, _, _}:
      l
    case 2n Semis{_, l, _, _}:
      l
    case 3n Semis{_, _, l, _}:
      l
    case _ Semis{_, _, _, l}:
      l

def Knockout.seed_of_side(s: S.Side, a: Nat, b: Nat) -> Nat:
  match s:
    case S.A{}:
      a
    case S.B{}:
      b

# The seed who won match r, played between seeds a (as A) and b.
def Knockout.winner_of(r: Finished, a: Nat, b: Nat) -> Nat:
  match r:
    case Finished{w, _}:
      Knockout.seed_of_side(w, a, b)

# ---------------------------------------------------------------------------
# One tournament: L18, L29
# ---------------------------------------------------------------------------
# Random-number slots: group A's matches 0-5 (P1-P2, P1-P3, P1-P4, P2-P3,
# P2-P4, P3-P4), group B's 6-11, the semifinals 12 and 13, the final 14, and
# the three draw lots 15-17.

def Event.pick8(n: Nat, p1: P.Player, p2: P.Player, p3: P.Player, p4: P.Player, p5: P.Player, p6: P.Player, p7: P.Player, p8: P.Player) -> P.Player:
  match n:
    case 1n:
      p1
    case 2n:
      p2
    case 3n:
      p3
    case 4n:
      p4
    case 5n:
      p5
    case 6n:
      p6
    case 7n:
      p7
    case _:
      p8

# The player with seed n.
def Event.player(n: Nat, f: Field) -> P.Player:
  match f:
    case Field{_, p1, p2, p3, p4, p5, p6, p7, p8}:
      Event.pick8(n, p1, p2, p3, p4, p5, p6, p7, p8)

def Event.method(f: Field) -> P.Method:
  match f:
    case Field{m, _, _, _, _, _, _, _, _}:
      m

# Seed `server`'s chance of winning a point on her serve against `receiver`.
def Event.chance(+f: Field, server: Nat, receiver: Nat) -> Sim.Chance:
  P.Serve.chance(Event.method(f), Event.player(server, f), Event.player(receiver, f))

def Event.done_of(m: S.Match) -> List<&2, S.Score>:
  match m:
    case S.Match{_, done, _}:
      done

def Event.finished(o: Sim.Outcome) -> Maybe<Finished>:
  match o:
    case Sim.Won{w, m}:
      Some{Finished{w, Event.done_of(m)}}
    case Sim.Unfinished{_}:
      None{}

# The match between seeds x (as player A) and y, in `slot`, with its own coin
# toss for the first server.
def Event.match_at(+fmt: S.Format, +f: Field, +seed: U32, +run: U32, +slot: U32, +x: Nat, +y: Nat) -> Maybe<Finished>:
  Event.finished(Sim.Match.simulate(fmt, Event.chance(f, x, y), Event.chance(f, y, x), seed, run, slot, Sim.Rng.coin(seed, run, slot)))

def Event.all6(a: Maybe<Finished>, b: Maybe<Finished>, c: Maybe<Finished>, d: Maybe<Finished>, e: Maybe<Finished>, h: Maybe<Finished>) -> Maybe<RoundRobin>:
  match a b c d e h:
    case Some{r12} Some{r13} Some{r14} Some{r23} Some{r24} Some{r34}:
      Some{RoundRobin{r12, r13, r14, r23, r24, r34}}
    case _ _ _ _ _ _:
      None{}

# A group's six matches, in slots base to base+5.
def Event.group_play(+fmt: S.Format, +f: Field, +seed: U32, +run: U32, +base: U32, g: Group) -> Maybe<RoundRobin>:
  match g:
    case Group{+s1, +s2, +s3, +s4}:
      Event.all6(Event.match_at(fmt, f, seed, run, base, s1, s2), Event.match_at(fmt, f, seed, run, (base + 1 : U32), s1, s3), Event.match_at(fmt, f, seed, run, (base + 2 : U32), s1, s4), Event.match_at(fmt, f, seed, run, (base + 3 : U32), s2, s3), Event.match_at(fmt, f, seed, run, (base + 4 : U32), s2, s4), Event.match_at(fmt, f, seed, run, (base + 5 : U32), s3, s4))

# A lot: True when the coin in `slot` lands for player A.
def Event.lot(seed: U32, run: U32, slot: U32) -> Bool:
  S.Match.same(Sim.Rng.coin(seed, run, slot), S.A{})

def Event.groups(d: Draw, +seed: U32, +run: U32) -> Group & Group:
  match d:
    case Seeded{}:
      Draw.seeded(Event.lot(seed, run, 15), Event.lot(seed, run, 16), Event.lot(seed, run, 17))
    case Fixed{a, b}:
      (a, b)

def Event.finish(+ga: Group, +gb: Group, +ra: RoundRobin, +rb: RoundRobin, +sm: Semis, +r1: Finished, +r2: Finished, +f1: Nat, +f2: Nat, fr: Maybe<Finished>) -> Outcome:
  match fr:
    case Some{+r}:
      Complete{ga, gb, ra, rb, sm, r1, r2, f1, f2, r, Knockout.winner_of(r, f1, f2)}
    case None{}:
      Unfinished{}

def Event.final_stage(+fmt: S.Format, +f: Field, +seed: U32, +run: U32, +ga: Group, +gb: Group, +ra: RoundRobin, +rb: RoundRobin, +sm: Semis, +r1: Finished, +r2: Finished, +f1: Nat, +f2: Nat) -> Outcome:
  Event.finish(ga, gb, ra, rb, sm, r1, r2, f1, f2, Event.match_at(fmt, f, seed, run, 14, f1, f2))

def Event.after_semis(+fmt: S.Format, +f: Field, +seed: U32, +run: U32, +ga: Group, +gb: Group, +ra: RoundRobin, +rb: RoundRobin, +sm: Semis, s1: Maybe<Finished>, s2: Maybe<Finished>) -> Outcome:
  match s1 s2:
    case Some{+r1} Some{+r2}:
      Event.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, Knockout.winner_of(r1, Knockout.on_line(1n, sm), Knockout.on_line(2n, sm)), Knockout.winner_of(r2, Knockout.on_line(3n, sm), Knockout.on_line(4n, sm)))
    case _ _:
      Unfinished{}

def Event.semis_stage(+fmt: S.Format, +f: Field, +seed: U32, +run: U32, +ga: Group, +gb: Group, +ra: RoundRobin, +rb: RoundRobin, +sm: Semis) -> Outcome:
  Event.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Event.match_at(fmt, f, seed, run, 12, Knockout.on_line(1n, sm), Knockout.on_line(2n, sm)), Event.match_at(fmt, f, seed, run, 13, Knockout.on_line(3n, sm), Knockout.on_line(4n, sm)))

def Event.after_groups(+fmt: S.Format, +f: Field, +seed: U32, +run: U32, +ga: Group, +gb: Group, xa: Maybe<RoundRobin>, xb: Maybe<RoundRobin>) -> Outcome:
  match xa xb:
    case Some{+ra} Some{+rb}:
      Event.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, Knockout.semis(ga, Standings.places(ga, ra), gb, Standings.places(gb, rb)))
    case _ _:
      Unfinished{}

def Event.after_draw(+fmt: S.Format, +f: Field, +seed: U32, +run: U32, gs: Group & Group) -> Outcome:
  match gs:
    case (+ga, +gb):
      Event.after_groups(fmt, f, seed, run, ga, gb, Event.group_play(fmt, f, seed, run, 0, ga), Event.group_play(fmt, f, seed, run, 6, gb))

# One simulated tournament: run number `run` of the simulation with seed
# `seed`.
def Event.play(+fmt: S.Format, +f: Field, d: Draw, +seed: U32, +run: U32) -> Outcome:
  Event.after_draw(fmt, f, seed, run, Event.groups(d, seed, run))

# ---------------------------------------------------------------------------
# Counting many tournaments: L30
# ---------------------------------------------------------------------------

def Event.no_counts() -> Counts:
  Counts{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# 1 for seed n, 0 for everyone else.
def Event.one(n: Nat) -> Counts:
  match n:
    case 1n:
      Counts{1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}
    case 2n:
      Counts{0n, 1n, 0n, 0n, 0n, 0n, 0n, 0n}
    case 3n:
      Counts{0n, 0n, 1n, 0n, 0n, 0n, 0n, 0n}
    case 4n:
      Counts{0n, 0n, 0n, 1n, 0n, 0n, 0n, 0n}
    case 5n:
      Counts{0n, 0n, 0n, 0n, 1n, 0n, 0n, 0n}
    case 6n:
      Counts{0n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}
    case 7n:
      Counts{0n, 0n, 0n, 0n, 0n, 0n, 1n, 0n}
    case 8n:
      Counts{0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n}
    case _:
      Counts{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

def Event.add_counts(x: Counts, y: Counts) -> Counts:
  match x y:
    case Counts{x1, x2, x3, x4, x5, x6, x7, x8} Counts{y1, y2, y3, y4, y5, y6, y7, y8}:
      Counts{Nat.add(x1, y1), Nat.add(x2, y2), Nat.add(x3, y3), Nat.add(x4, y4), Nat.add(x5, y5), Nat.add(x6, y6), Nat.add(x7, y7), Nat.add(x8, y8)}

def Event.add(x: Tally, y: Tally) -> Tally:
  match x y:
    case Tally{xt, xf, xs, xu} Tally{yt, yf, ys, yu}:
      Tally{Event.add_counts(xt, yt), Event.add_counts(xf, yf), Event.add_counts(xs, ys), Nat.add(xu, yu)}

# What one tournament adds to the totals.
def Event.count(o: Outcome) -> Tally:
  match o:
    case Complete{_, _, _, _, +sm, _, _, f1, f2, _, c}:
      Tally{Event.one(c), Event.add_counts(Event.one(f1), Event.one(f2)), Event.add_counts(Event.add_counts(Event.one(Knockout.on_line(1n, sm)), Event.one(Knockout.on_line(2n, sm))), Event.add_counts(Event.one(Knockout.on_line(3n, sm)), Event.one(Knockout.on_line(4n, sm)))), 0n}
    case Unfinished{}:
      Tally{Event.no_counts(), Event.no_counts(), Event.no_counts(), 1n}

# The totals for the 2^d tournaments in block `prefix`, that is, runs
# prefix*2^d to prefix*2^d + 2^d - 1. Block `prefix` splits into blocks
# 2*prefix and 2*prefix+1, which run in parallel.
def Event.tally(+d: Nat, +fmt: S.Format, +f: Field, +draw: Draw, +seed: U32, +prefix: U32) -> Tally:
  match d:
    case 0n:
      Event.count(Event.play(fmt, f, draw, seed, prefix))
    case 1n+p:
      x y = Event.tally(p, fmt, f, draw, seed, (prefix * 2 + 0 : U32)) Event.tally(p, fmt, f, draw, seed, (prefix * 2 + 1 : U32))
      Event.add(x, y)
