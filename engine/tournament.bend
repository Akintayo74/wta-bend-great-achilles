# tournament.bend: groups, standings and knockouts.
#
# Milestone 6. Interface only for now: the types and the functions the laws
# in LAWS.bend talk about (L15-L19, L28-L30), with ?TODO bodies. The code is
# written once the owner has approved the laws.
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
# The functions the laws are about (to be written after approval)
# ---------------------------------------------------------------------------

# The seeded draw (L15). Each lot is True when the lower-numbered seed of the
# pair is drawn first, and so goes into group A.
def Draw.seeded(l34: Bool, l56: Bool, l78: Bool) -> Group & Group:
  ?TODO

# A group's final places (L16, L17, L28).
def Standings.places(g: Group, rr: RoundRobin) -> Places:
  ?TODO

# The semifinal lines from the two groups' places (L19).
def Knockout.semis(ga: Group, pa: Places, gb: Group, pb: Places) -> Semis:
  ?TODO

# One simulated tournament: run number `run` of the simulation with seed
# `seed` (L18, L29).
def Event.play(fmt: S.Format, f: Field, d: Draw, seed: U32, run: U32) -> Outcome:
  ?TODO

# The totals for the 2^d tournaments in block `prefix`, split across cores as
# Sim.Run.tally does (L30).
def Event.tally(d: Nat, fmt: S.Format, f: Field, draw: Draw, seed: U32, prefix: U32) -> Tally:
  ?TODO
