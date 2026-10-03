# sim.bend: counter-based random numbers and the run loop.
#
# Milestone 4. Laws L1, L14, L26 and L27 are in LAWS.bend and proven in
# PROOF.bend.

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
  match c:
    case Chance{p, _}:
      p

# Matching on the check's answer tells the type checker which way it went, so
# in the True branch `ok` is exactly the proof a Chance needs.
def Chance.make.go(+p: U32, fits: Bool, ok: {U32.is_le(p, 10000) == fits : Bool}) -> Maybe<Chance>:
  match fits:
    case True{}:
      Some{Chance{p, ok}}
    case False{}:
      None{}

# Checks a number read from the input: Some chance if it is at most 10,000,
# None otherwise. Out-of-range numbers are rejected, never clamped.
def Chance.make(+p: U32) -> Maybe<Chance>:
  Chance.make.go(p, U32.is_le(p, 10000), {==})

# ---------------------------------------------------------------------------
# Random numbers
# ---------------------------------------------------------------------------
# Counter-based: every random number is computed from where it is used (seed,
# run number, match slot, point number), not from the number before it. So no
# two runs share state, and runs can be done in any order on any core.
#
# The scrambling function is "lowbias32" (Chris Wellons, 2018): shifts, XORs
# and two multiplications that turn nearby inputs into unrelated outputs.
# Bend has only 32-bit integers, so everything here is 32-bit and wraps
# around on overflow.

def Rng.mix(+x: U32) -> U32:
  +a = (x .^. (x >> 16n) : U32)
  +b = (a * 2146121005 : U32)
  +c = (b .^. (b >> 15n) : U32)
  +d = (c * 2221713035 : U32)
  (d .^. (d >> 16n) : U32)

# The key of one match: the seed, run number and slot, each mixed in turn.
# Adding a different odd constant at each step keeps (seed, run, slot) =
# (1, 2, 3) and (2, 1, 3) apart.
def Rng.key(seed: U32, run: U32, slot: U32) -> U32:
  +a = Rng.mix((seed + 2654435769 : U32))
  +b = Rng.mix((a + run : U32))
  Rng.mix((b + (slot * 2246822519 : U32) : U32))

# Point k of a match: its key plus k steps of the golden-ratio constant,
# mixed, then reduced to 0-9,999. (2^32 is not a multiple of 10,000, so the
# numbers 0-7,295 come up 429,497 times in 2^32 and the rest 429,496 times: a
# bias of at most 0.00005 percentage points.)
def Rng.from_key(key: U32, k: U32) -> U32:
  U32.mod(Rng.mix((key + (k * 2654435769 : U32) : U32)), 10000)

# The random number, 0 to 9,999, for point k of the match in `slot` of run
# `run`. (In milestone 4 a run is one match, in slot 0. Tournaments in
# milestone 6 use one slot per match.)
def Rng.roll(seed: U32, run: U32, slot: U32, k: U32) -> U32:
  Rng.from_key(Rng.key(seed, run, slot), k)

def Rng.side(top_half: Bool) -> S.Side:
  match top_half:
    case True{}:
      S.A{}
    case False{}:
      S.B{}

# The coin toss for who serves first in the match in `slot` of run `run`. It
# uses its own draw, separate from the point draws.
def Rng.coin(seed: U32, run: U32, slot: U32) -> S.Side:
  Rng.side(U32.is_lt(Rng.mix((Rng.key(seed, run, slot) .^. 1431655765 : U32)), 2147483648))

# ---------------------------------------------------------------------------
# One point, one match
# ---------------------------------------------------------------------------

# The server's point chance.
def Point.chance(server: S.Side, pa: U32, pb: U32) -> U32:
  match server:
    case S.A{}:
      pa
    case S.B{}:
      pb

def Point.pick(server_won: Bool, +server: S.Side) -> S.Side:
  match server_won:
    case True{}:
      server
    case False{}:
      S.Side.other(server)

# Who wins the point: the server when the roll is below her chance.
def Point.winner(+server: S.Side, pa: U32, pb: U32, roll: U32) -> S.Side:
  Point.pick(U32.is_lt(roll, Point.chance(server, pa, pb)), server)

# The match after one simulated point, with the chances as plain numbers.
def Point.apply(+fmt: S.Format, pa: U32, pb: U32, +m: S.Match, roll: U32) -> S.Match:
  S.Match.point(fmt, m, Point.winner(S.Match.server(m), pa, pb, roll))

# The match after one simulated point. `ca` and `cb` are A's and B's chances
# of winning a point on their own serve; `roll` is the random number.
def Point.simulate(+fmt: S.Format, ca: Chance, cb: Chance, +m: S.Match, roll: U32) -> S.Match:
  Point.apply(fmt, Chance.value(ca), Chance.value(cb), m, roll)

# How a simulated match ended: won (with the final state, for the set scores),
# or still unfinished when the 1,000 points ran out.
type Outcome is Data:
  Won{winner: S.Side, m: S.Match}
  Unfinished{m: S.Match}

# Play up to `fuel` points, numbered k, k+1, ...; `w` is who has won the
# match so far. Stops as soon as the match is won.
def Match.loop(fuel: Nat, w: Maybe<S.Side>, +fmt: S.Format, +pa: U32, +pb: U32, +key: U32, +k: U32, +m: S.Match) -> S.Match:
  match fuel:
    case 0n:
      m
    case 1n+p:
      match w:
        case Some{_}:
          m
        case None{}:
          +next = Point.apply(fmt, pa, pb, m, Rng.from_key(key, k))
          Match.loop(p, S.Match.winner(fmt, next), fmt, pa, pb, key, U32.inc(k), next)

def Match.report.go(w: Maybe<S.Side>, m: S.Match) -> Outcome:
  match w:
    case Some{x}:
      Won{x, m}
    case None{}:
      Unfinished{m}

def Match.report(+fmt: S.Format, +m: S.Match) -> Outcome:
  Match.report.go(S.Match.winner(fmt, m), m)

# The point cap (SPEC.md, Simulation).
def Match.cap() -> Nat:
  1000n

# Simulate the match in `slot` of run `run`, with `first` serving first.
def Match.simulate(+fmt: S.Format, ca: Chance, cb: Chance, seed: U32, run: U32, slot: U32, +first: S.Side) -> Outcome:
  Match.report(fmt, Match.loop(Match.cap(), S.Match.winner(fmt, S.Match.start(first)), fmt, Chance.value(ca), Chance.value(cb), Rng.key(seed, run, slot), 0, S.Match.start(first)))

# One run of milestone 4: a single match in slot 0, first server by coin toss.
def Run.single(fmt: S.Format, ca: Chance, cb: Chance, +seed: U32, +run: U32) -> Outcome:
  Match.simulate(fmt, ca, cb, seed, run, 0, Rng.coin(seed, run, 0))

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

def Run.add_sets(x: SetCounts, y: SetCounts) -> SetCounts:
  match x y:
    case SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} SetCounts{y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}:
      SetCounts{Nat.add(x1, y1), Nat.add(x2, y2), Nat.add(x3, y3), Nat.add(x4, y4), Nat.add(x5, y5), Nat.add(x6, y6), Nat.add(x7, y7), Nat.add(x8, y8), Nat.add(x9, y9), Nat.add(x10, y10), Nat.add(x11, y11), Nat.add(x12, y12), Nat.add(x13, y13), Nat.add(x14, y14), Nat.add(x15, y15)}

def Run.add(x: Tally, y: Tally) -> Tally:
  match x y:
    case Tally{xa, xb, xu, xs} Tally{ya, yb, yu, ys}:
      Tally{Nat.add(xa, ya), Nat.add(xb, yb), Nat.add(xu, yu), Run.add_sets(xs, ys)}

def Run.no_sets() -> SetCounts:
  SetCounts{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

def Run.is_score(+a: Nat, +b: Nat, x: Nat, y: Nat) -> Nat:
  S.Match.count(Bool.and(Nat.is_eq(a, x), Nat.is_eq(b, y)), 0n)

# Is x-y a finished set score with the first player winning: 6-0 to 6-4, 7-5
# or 7-6?
def Run.score_ok(+w: Nat, +l: Nat) -> Bool:
  Bool.or(Bool.and(Nat.is_eq(w, 6n), Nat.is_le(l, 4n)), Bool.and(Nat.is_eq(w, 7n), Bool.or(Nat.is_eq(l, 5n), Nat.is_eq(l, 6n))))

# One finished set, counted under its score.
def Run.one_set(sc: S.Score) -> SetCounts:
  match sc:
    case S.Score{+a, +b}:
      SetCounts{Run.is_score(a, b, 6n, 0n), Run.is_score(a, b, 6n, 1n), Run.is_score(a, b, 6n, 2n), Run.is_score(a, b, 6n, 3n), Run.is_score(a, b, 6n, 4n), Run.is_score(a, b, 7n, 5n), Run.is_score(a, b, 7n, 6n), Run.is_score(a, b, 0n, 6n), Run.is_score(a, b, 1n, 6n), Run.is_score(a, b, 2n, 6n), Run.is_score(a, b, 3n, 6n), Run.is_score(a, b, 4n, 6n), Run.is_score(a, b, 5n, 7n), Run.is_score(a, b, 6n, 7n), S.Match.count(Bool.not(Bool.or(Run.score_ok(a, b), Run.score_ok(b, a))), 0n)}

def Run.set_scores(done: List<&2, S.Score>) -> SetCounts:
  match done:
    case Nil{}:
      Run.no_sets()
    case Con{sc, rest}:
      Run.add_sets(Run.one_set(sc), Run.set_scores(rest))

# What one run adds to the totals.
def Run.count(o: Outcome) -> Tally:
  match o:
    case Won{w, m}:
      match w m:
        case S.A{} S.Match{_, done, _}:
          Tally{1n, 0n, 0n, Run.set_scores(done)}
        case S.B{} S.Match{_, done, _}:
          Tally{0n, 1n, 0n, Run.set_scores(done)}
    case Unfinished{_}:
      Tally{0n, 0n, 1n, Run.no_sets()}

# The totals for the 2^d runs in block `prefix`, that is, runs
# prefix*2^d to prefix*2^d + 2^d - 1. Block `prefix` splits into blocks
# 2*prefix and 2*prefix+1, which run in parallel.
# The whole simulation is Run.tally(d, ..., 0).
def Run.tally(+d: Nat, +fmt: S.Format, +ca: Chance, +cb: Chance, +seed: U32, +prefix: U32) -> Tally:
  match d:
    case 0n:
      Run.count(Run.single(fmt, ca, cb, seed, prefix))
    case 1n+p:
      x y = Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)) Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 1 : U32))
      Run.add(x, y)
