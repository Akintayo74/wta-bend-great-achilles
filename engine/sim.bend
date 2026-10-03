# sim.bend: counter-based random numbers and the run loop.
#
# Milestone 4. Laws L1, L14, L26 and L27 are in LAWS.bend.
# INTERFACE ONLY (draft for owner review): the types are final, the function
# bodies are ?TODO until the laws are approved.

import Base
import ./scoring.bend as S

# ---------------------------------------------------------------------------
# Point chances
# ---------------------------------------------------------------------------

# A point chance out of 10,000 (60% = 6000), carrying proof that it is at most
# 10,000. The only way to get one is Chance.make, which checks the number, so
# the simulator can't be handed an out-of-range chance (L1).
type Chance is Data:
  Chance{p: U32, ok: {U32.is_le(p, 10000) == True{} : Bool}}

# The number inside a chance.
def Chance.value(c: Chance) -> U32:
  ?TODO

# Checks a number read from the input: Some chance if it is at most 10,000,
# None otherwise. Out-of-range numbers are rejected, never clamped.
def Chance.make(p: U32) -> Maybe<Chance>:
  ?TODO

# ---------------------------------------------------------------------------
# Random numbers
# ---------------------------------------------------------------------------
# Counter-based: every random number is computed from where it is used (seed,
# run number, match slot, point number), not from the number before it. So no
# two runs share state, and runs can be done in any order on any core.

# The random number, 0 to 9,999, for point k of the match in `slot` of run
# `run`. (In milestone 4 a run is one match, in slot 0. Tournaments in
# milestone 6 use one slot per match.)
def Rng.roll(seed: U32, run: U32, slot: U32, k: U32) -> U32:
  ?TODO

# The coin toss for who serves first in the match in `slot` of run `run`. It
# uses its own draw, separate from the point draws.
def Rng.coin(seed: U32, run: U32, slot: U32) -> S.Side:
  ?TODO

# ---------------------------------------------------------------------------
# One point, one match
# ---------------------------------------------------------------------------

# The match after one simulated point. `ca` and `cb` are A's and B's chances
# of winning a point on their own serve; `roll` is the random number.
def Point.simulate(fmt: S.Format, ca: Chance, cb: Chance, m: S.Match, roll: U32) -> S.Match:
  ?TODO

# How a simulated match ended: won (with the final state, for the set scores),
# or still unfinished when the 1,000 points ran out.
type Outcome is Data:
  Won{winner: S.Side, m: S.Match}
  Unfinished{m: S.Match}

# Simulate the match in `slot` of run `run`, with `first` serving first.
def Match.simulate(fmt: S.Format, ca: Chance, cb: Chance, seed: U32, run: U32, slot: U32, first: S.Side) -> Outcome:
  ?TODO

# One run of milestone 4: a single match in slot 0, first server by coin toss.
def Run.single(fmt: S.Format, ca: Chance, cb: Chance, seed: U32, run: U32) -> Outcome:
  ?TODO

# ---------------------------------------------------------------------------
# Counting many runs
# ---------------------------------------------------------------------------

# How often each set score happened. aXY counts sets A won X-Y, bXY sets B won
# X-Y. `other` counts any other score; by L9 it is always 0.
type SetCounts is Data:
  SetCounts{a60: Nat, a61: Nat, a62: Nat, a63: Nat, a64: Nat, a75: Nat, a76: Nat, b60: Nat, b61: Nat, b62: Nat, b63: Nat, b64: Nat, b75: Nat, b76: Nat, other: Nat}

# The totals over many runs: matches won by A and by B, unfinished matches, and
# the set scores of the finished matches.
type Tally is Data:
  Tally{a: Nat, b: Nat, unfinished: Nat, sets: SetCounts}

# The totals for the 2^d runs in block `prefix`, that is, runs
# prefix*2^d to prefix*2^d + 2^d - 1. Block `prefix` splits into blocks
# 2*prefix and 2*prefix+1, which run in parallel.
# The whole simulation is Run.tally(d, ..., 0).
def Run.tally(d: Nat, fmt: S.Format, ca: Chance, cb: Chance, seed: U32, prefix: U32) -> Tally:
  ?TODO
