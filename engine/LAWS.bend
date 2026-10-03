# LAWS.bend: the rules the engine must never break (SPEC.md, Laws L1-L19).
#
# STATUS: Approved by the owner, milestone 2 (game layer: L2-L5, L20).
# Still to come, with their layers: L1 (point chances, milestone 4 or 5)
# and L6-L19 (tiebreak, set, match, simulation, tournament).
# Once merged to main, this file is locked; see CLAUDE.md.
#
# How to read a law:
#
#   law name:
#     for x: T            "for every possible x of type T ..."
#     for h: {P}          "... assuming P holds ..."
#     {lhs == rhs : T}    "... lhs always equals rhs."
#
# Bend accepts a law only when engine/PROOF.bend contains a proof of it: a def
# with the same name. A law is a claim about every possible input, not a test
# of a few, so `for n: Nat` covers deuce after 1 point, after 10, and after a
# million.
#
# Scores are raw point counts (see scoring.bend): 0, 1, 2, 3 points are love,
# 15, 30, 40; 3-3 is deuce (40-40); 4-3 is advantage to the player with 4.

import Base
import ./scoring.bend as S

# ---------------------------------------------------------------------------
# The game rule, written once, straight from SPEC.md
# ---------------------------------------------------------------------------
# These two defs are part of the locked spec, not of the engine. The laws
# below compare the engine against them.

# A player with x points has won the game against an opponent with y points
# when she has at least 4 points and leads by at least 2.
def Rule.game_won(+x: Nat, y: Nat) -> Bool:
  Bool.and(Nat.is_ge(x, 4n), Nat.is_ge(x, Nat.add(y, 2n)))

def Rule.pick(a_won: Bool, b_won: Bool) -> Maybe<S.Side>:
  match a_won b_won:
    case True{} _:
      Some{S.A{}}
    case False{} True{}:
      Some{S.B{}}
    case False{} False{}:
      None{}

# The winner of a game at a points to b, by the rule above, if anyone.
def Rule.game_winner(+a: Nat, +b: Nat) -> Maybe<S.Side>:
  Rule.pick(Rule.game_won(a, b), Rule.game_won(b, a))

# ---------------------------------------------------------------------------
# Examples: the rule above, checked on familiar scores
# ---------------------------------------------------------------------------
# These pin down Rule.game_winner itself, so a slip in it can't hide.

# 40-15 is not yet a game.
law ex_40_15_is_not_over:
  {Rule.game_winner(3n, 1n) == None{} : Maybe<S.Side>}

# Winning the next point from 40-15 wins the game.
law ex_game_from_40_15:
  {Rule.game_winner(4n, 1n) == Some{S.A{}} : Maybe<S.Side>}

# Advantage (4-3) is not yet a game.
law ex_advantage_is_not_over:
  {Rule.game_winner(4n, 3n) == None{} : Maybe<S.Side>}

# Two points clear after deuce (3-5) is a game to player B.
law ex_game_to_b_after_deuce:
  {Rule.game_winner(3n, 5n) == Some{S.B{}} : Maybe<S.Side>}

# ---------------------------------------------------------------------------
# Game layer: L2-L5
# ---------------------------------------------------------------------------

# L2. A game ends only when one player has at least 4 points and leads by 2.
# The engine's verdict on any score agrees with the rule, for every score.
law L2_game_winner_follows_rule:
  for +a: Nat
  for +b: Nat
  {S.Game.winner(S.Game{a, b}) == Rule.game_winner(a, b) : Maybe<S.Side>}

# L3. At any tie of 3-3 (40-40) or higher, the game is not over.
# 3n+n is "3 plus n": as n runs over every Nat, this is 3-3, 4-4, 5-5, ...
law L3_deuce_is_not_over:
  for n: Nat
  {S.Game.winner(S.Game{3n+n, 3n+n}) == None{} : Maybe<S.Side>}

# L4. From a 1-point lead at 4-3 or higher, the next point either wins the game
# or returns it to deuce. Four laws: either player ahead, either player
# winning the point.

# A has advantage and wins the point: game to A.
law L4_advantage_a_converted:
  for n: Nat
  {S.Game.winner(S.Game.point(S.Game{4n+n, 3n+n}, S.A{})) == Some{S.A{}} : Maybe<S.Side>}

# A has advantage and B wins the point: back to deuce (a tie, so L3 says the
# game goes on).
law L4_advantage_a_lost:
  for n: Nat
  {S.Game.point(S.Game{4n+n, 3n+n}, S.B{}) == S.Game{4n+n, 4n+n} : S.Game}

# B has advantage and wins the point: game to B.
law L4_advantage_b_converted:
  for n: Nat
  {S.Game.winner(S.Game.point(S.Game{3n+n, 4n+n}, S.B{})) == Some{S.B{}} : Maybe<S.Side>}

# B has advantage and A wins the point: back to deuce.
law L4_advantage_b_lost:
  for n: Nat
  {S.Game.point(S.Game{3n+n, 4n+n}, S.A{}) == S.Game{4n+n, 4n+n} : S.Game}

# L5. Once a game is won, further points do not change it.
law L5_won_game_is_final:
  for +g: S.Game
  for -w: S.Side
  for won: {S.Game.winner(g) == Some{w} : Maybe<S.Side>}
  for s: S.Side
  {S.Game.point(g, s) == g : S.Game}

# ---------------------------------------------------------------------------
# Game layer: L20 (added to SPEC.md in milestone 2)
# ---------------------------------------------------------------------------

# L20. While a game is in progress, each point is added to the player who won
# it. Without this, an engine that credited points to the wrong player (or
# not at all) would still satisfy L2-L5: they only constrain who has won and
# that a won game stays won.
law L20_live_point_goes_to_a:
  for a: Nat
  for b: Nat
  for live: {S.Game.winner(S.Game{a, b}) == None{} : Maybe<S.Side>}
  {S.Game.point(S.Game{a, b}, S.A{}) == S.Game{1n+a, b} : S.Game}

law L20_live_point_goes_to_b:
  for a: Nat
  for b: Nat
  for live: {S.Game.winner(S.Game{a, b}) == None{} : Maybe<S.Side>}
  {S.Game.point(S.Game{a, b}, S.B{}) == S.Game{a, 1n+b} : S.Game}
