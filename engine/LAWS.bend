# LAWS.bend: the rules the engine must never break (SPEC.md, Laws L1-L27).
#
# STATUS: Milestone 2 (game layer: L2-L5, L20): approved by the owner.
#         Milestone 3 (tiebreak, set, match: L6-L13, L21-L25): approved by
#         the owner.
#         Milestone 4 (simulation: L1, L14, L26, L27): approved by the
#         owner.
# Still to come: L15-L19 (tournament, milestone 6).
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
import ./sim.bend as Sim

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

# ===========================================================================
# MILESTONE 3: tiebreak, set and match. Approved by the owner.
# ===========================================================================
#
# How this section is organised:
# - Tiebreak laws (L6-L8, L21) hold for every tiebreak target: 7, 10, ...
# - Set and match score laws (L9, L10, L12, L22, L24) are for the WTA format:
#   6 games win a set, 2 sets win the match. They hold for every tiebreak
#   target, so they don't depend on the deciding-set tiebreak, which is still
#   to be confirmed from the 2026 rulebook.
# - Laws that only pass points along or report a result (L11, L13, L23, L25)
#   hold for every format.
# - L9, L10 and L12 are about sets and matches actually played: "for every
#   possible list of point winners, play it from 0-0, and then ...". A score
#   like 9-0 can be written down but never played, so these laws say nothing
#   about it.
# - Inputs are marked `+` (reusable) throughout. In milestone 2, inputs
#   without `+` could be used only once inside a proof, which made the proofs
#   longer without making the laws any stronger.

# ---------------------------------------------------------------------------
# Helpers for the rules below
# ---------------------------------------------------------------------------

# The opponent of player s.
def Rule.other(s: S.Side) -> S.Side:
  match s:
    case S.A{}:
      S.B{}
    case S.B{}:
      S.A{}

def Rule.same(x: S.Side, y: S.Side) -> Bool:
  match x y:
    case S.A{} S.A{}:
      True{}
    case S.B{} S.B{}:
      True{}
    case S.A{} S.B{}:
      False{}
    case S.B{} S.A{}:
      False{}

def Rule.count(hit: Bool, n: Nat) -> Nat:
  match hit:
    case True{}:
      1n+n
    case False{}:
      n

def Rule.choose(c: Bool, yes: Nat, no: Nat) -> Nat:
  match c:
    case True{}:
      yes
    case False{}:
      no

# ---------------------------------------------------------------------------
# The tiebreak rule
# ---------------------------------------------------------------------------

# A player with x points has won a tiebreak played to `target` points, against
# an opponent with y points, when she has at least `target` points and leads
# by at least 2. (The game rule above is the same thing with target 4.)
def Rule.tiebreak_won(target: Nat, +x: Nat, y: Nat) -> Bool:
  Bool.and(Nat.is_ge(x, target), Nat.is_ge(x, Nat.add(y, 2n)))

# The winner of a tiebreak at a points to b, if anyone.
def Rule.tiebreak_winner(+target: Nat, +a: Nat, +b: Nat) -> Maybe<S.Side>:
  Rule.pick(Rule.tiebreak_won(target, a, b), Rule.tiebreak_won(target, b, a))

# Examples.
law ex_tiebreak_7_5_is_won:
  {Rule.tiebreak_winner(7n, 7n, 5n) == Some{S.A{}} : Maybe<S.Side>}

law ex_tiebreak_7_6_is_not_over:
  {Rule.tiebreak_winner(7n, 7n, 6n) == None{} : Maybe<S.Side>}

# A 10-point tiebreak (as at the Slams) won 10-8 by player B.
law ex_ten_point_tiebreak_won_10_8:
  {Rule.tiebreak_winner(10n, 8n, 10n) == Some{S.B{}} : Maybe<S.Side>}

# Who serves the first seven points of a tiebreak that A starts: A, then B
# twice, then A twice, then B twice.
law ex_tiebreak_serve_pattern:
  {[S.Tiebreak.server(S.A{}, 0n), S.Tiebreak.server(S.A{}, 1n), S.Tiebreak.server(S.A{}, 2n), S.Tiebreak.server(S.A{}, 3n), S.Tiebreak.server(S.A{}, 4n), S.Tiebreak.server(S.A{}, 5n), S.Tiebreak.server(S.A{}, 6n)] == [S.A{}, S.B{}, S.B{}, S.A{}, S.A{}, S.B{}, S.B{}] : List<S.Side>}

# ---------------------------------------------------------------------------
# Tiebreak laws: L6, L7, L8, L21
# ---------------------------------------------------------------------------

# L6. A tiebreak ends only when one player has at least `target` points and
# leads by 2. The engine agrees with the rule at every score, for every target.
law L6_tiebreak_winner_follows_rule:
  for +target: Nat
  for +a: Nat
  for +b: Nat
  {S.Tiebreak.winner(target, S.Tiebreak{a, b}) == Rule.tiebreak_winner(target, a, b) : Maybe<S.Side>}

# L7. A level tiebreak is not over. The spec says "at any tie of 6-6 or
# higher"; this covers every tie, including those below 6-6, which can't be
# over either.
law L7_level_tiebreak_is_not_over:
  for +target: Nat
  for +n: Nat
  {S.Tiebreak.winner(target, S.Tiebreak{n, n}) == None{} : Maybe<S.Side>}

# L7, continued. From a 1-point lead with the leader on at least target-1
# points (6-5, 7-6, 8-7, ... in a 7-point tiebreak), the next point either wins
# the tiebreak or levels it. Here the target is written 2+u, so it is at least
# 2; the leader has 1+u+n points (at least target-1) and the trailer u+n.
# Four laws: either player ahead, either player winning the point.

# A leads and wins the point: tiebreak to A.
law L7_lead_a_converted:
  for +u: Nat
  for +n: Nat
  {S.Tiebreak.winner(2n+u, S.Tiebreak.point(2n+u, S.Tiebreak{1n+Nat.add(u, n), Nat.add(u, n)}, S.A{})) == Some{S.A{}} : Maybe<S.Side>}

# A leads and B wins the point: level again.
law L7_lead_a_levelled:
  for +u: Nat
  for +n: Nat
  {S.Tiebreak.point(2n+u, S.Tiebreak{1n+Nat.add(u, n), Nat.add(u, n)}, S.B{}) == S.Tiebreak{1n+Nat.add(u, n), 1n+Nat.add(u, n)} : S.Tiebreak}

# B leads and wins the point: tiebreak to B.
law L7_lead_b_converted:
  for +u: Nat
  for +n: Nat
  {S.Tiebreak.winner(2n+u, S.Tiebreak.point(2n+u, S.Tiebreak{Nat.add(u, n), 1n+Nat.add(u, n)}, S.B{})) == Some{S.B{}} : Maybe<S.Side>}

# B leads and A wins the point: level again.
law L7_lead_b_levelled:
  for +u: Nat
  for +n: Nat
  {S.Tiebreak.point(2n+u, S.Tiebreak{Nat.add(u, n), 1n+Nat.add(u, n)}, S.A{}) == S.Tiebreak{1n+Nat.add(u, n), 1n+Nat.add(u, n)} : S.Tiebreak}

# L8. Tiebreak serving follows the 1-then-2s pattern. `played` counts the
# tiebreak points already played, so 0 is the first point. Together these
# three laws fix the server of every tiebreak point (see the example above).

# The first point is served by the tiebreak's first server.
law L8_tiebreak_first_point:
  for +first: S.Side
  {S.Tiebreak.server(first, 0n) == first : S.Side}

# The serve changes after 1, 3, 5, ... points have been played ...
law L8_tiebreak_serve_changes:
  for +first: S.Side
  for +n: Nat
  {S.Tiebreak.server(first, 1n+Nat.double(n)) == Rule.other(S.Tiebreak.server(first, Nat.double(n))) : S.Side}

# ... and stays with the same player for the point after that.
law L8_tiebreak_serve_stays:
  for +first: S.Side
  for +n: Nat
  {S.Tiebreak.server(first, 2n+Nat.double(n)) == S.Tiebreak.server(first, 1n+Nat.double(n)) : S.Side}

# L21. While a tiebreak is in progress, each point is added to the player who
# won it; a finished tiebreak does not change. (L20 and L5, for tiebreaks.)
law L21_live_tiebreak_point_goes_to_a:
  for +target: Nat
  for +a: Nat
  for +b: Nat
  for live: {S.Tiebreak.winner(target, S.Tiebreak{a, b}) == None{} : Maybe<S.Side>}
  {S.Tiebreak.point(target, S.Tiebreak{a, b}, S.A{}) == S.Tiebreak{1n+a, b} : S.Tiebreak}

law L21_live_tiebreak_point_goes_to_b:
  for +target: Nat
  for +a: Nat
  for +b: Nat
  for live: {S.Tiebreak.winner(target, S.Tiebreak{a, b}) == None{} : Maybe<S.Side>}
  {S.Tiebreak.point(target, S.Tiebreak{a, b}, S.B{}) == S.Tiebreak{a, 1n+b} : S.Tiebreak}

law L21_won_tiebreak_is_final:
  for +target: Nat
  for +t: S.Tiebreak
  for -w: S.Side
  for won: {S.Tiebreak.winner(target, t) == Some{w} : Maybe<S.Side>}
  for +s: S.Side
  {S.Tiebreak.point(target, t, s) == t : S.Tiebreak}

# ---------------------------------------------------------------------------
# The set rule (6 games win a set)
# ---------------------------------------------------------------------------

# A player with x games has won the set against an opponent with y games when
# she has at least 6 and leads by 2 (6-0 to 6-4, 7-5), or has won the
# tiebreak at 6-6 (7-6).
def Rule.set_won(+x: Nat, +y: Nat) -> Bool:
  Bool.or(Bool.and(Nat.is_ge(x, 6n), Nat.is_ge(x, Nat.add(y, 2n))), Bool.and(Nat.is_eq(x, 7n), Nat.is_eq(y, 6n)))

# The winner of a set at a games to b, if anyone.
def Rule.set_winner(+a: Nat, +b: Nat) -> Maybe<S.Side>:
  Rule.pick(Rule.set_won(a, b), Rule.set_won(b, a))

# A set before its first point: 0-0, playing a new game at 0-0.
def Rule.fresh_set() -> S.TennisSet:
  S.TennisSet{0n, 0n, S.InGame{S.Game{0n, 0n}}}

# What comes next at a games: a tiebreak at 6-6, otherwise a new game. Either
# starts at 0-0.
def Rule.next_play(six_all: Bool) -> S.Play:
  match six_all:
    case True{}:
      S.InTiebreak{S.Tiebreak{0n, 0n}}
    case False{}:
      S.InGame{S.Game{0n, 0n}}

def Rule.next_set(+a: Nat, +b: Nat) -> S.TennisSet:
  S.TennisSet{a, b, Rule.next_play(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 6n)))}

# The set after a game or tiebreak won by w at a-b games: one more game to w,
# then the next game or tiebreak starts.
def Rule.after_game(w: S.Side, a: Nat, b: Nat) -> S.TennisSet:
  match w:
    case S.A{}:
      Rule.next_set(1n+a, b)
    case S.B{}:
      Rule.next_set(a, 1n+b)

# Play a list of points, in order, in a set with tiebreak target `target`.
def Rule.play_set(+target: Nat, pts: List<&2, S.Side>, st: S.TennisSet) -> S.TennisSet:
  match pts:
    case Nil{}:
      st
    case Con{s, rest}:
      Rule.play_set(target, rest, S.TennisSet.point(6n, target, st, s))

# The allowed final scores, as (winner's games, loser's games): 6-0 to 6-4,
# 7-5 and 7-6.
def Rule.set_score_ok(+w: Nat, +l: Nat) -> Bool:
  Bool.or(Bool.and(Nat.is_eq(w, 6n), Nat.is_le(l, 4n)), Bool.and(Nat.is_eq(w, 7n), Bool.or(Nat.is_eq(l, 5n), Nat.is_eq(l, 6n))))

# Is the set's score an allowed final score with player w as the winner?
def Rule.finished_set_ok(w: S.Side, st: S.TennisSet) -> Bool:
  match w:
    case S.A{}:
      match st:
        case S.TennisSet{a, b, _}:
          Rule.set_score_ok(a, b)
    case S.B{}:
      match st:
        case S.TennisSet{a, b, _}:
          Rule.set_score_ok(b, a)

def Rule.in_tiebreak(st: S.TennisSet) -> Bool:
  match st:
    case S.TennisSet{_, _, play}:
      match play:
        case S.InGame{_}:
          False{}
        case S.InTiebreak{_}:
          True{}

def Rule.six_all(st: S.TennisSet) -> Bool:
  match st:
    case S.TennisSet{a, b, _}:
      Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 6n))

# Examples.
law ex_set_6_4_is_won:
  {Rule.set_winner(6n, 4n) == Some{S.A{}} : Maybe<S.Side>}

law ex_set_6_5_is_not_over:
  {Rule.set_winner(6n, 5n) == None{} : Maybe<S.Side>}

law ex_set_7_5_is_won:
  {Rule.set_winner(7n, 5n) == Some{S.A{}} : Maybe<S.Side>}

law ex_set_6_7_is_won_by_b:
  {Rule.set_winner(6n, 7n) == Some{S.B{}} : Maybe<S.Side>}

# ---------------------------------------------------------------------------
# Set laws: L24, L22, L9, L10
# ---------------------------------------------------------------------------

# L24. The engine's verdict on who has won a set agrees with the set rule, at
# every score. Without it, an engine that never ended a set would pass L9 and
# L10, which only say what a finished set looks like.
law L24_set_winner_follows_rule:
  for +a: Nat
  for +b: Nat
  for +play: S.Play
  {S.TennisSet.winner(6n, S.TennisSet{a, b, play}) == Rule.set_winner(a, b) : Maybe<S.Side>}

# L22. While a set is in progress, each point goes into the game or tiebreak
# being played; when that game or tiebreak is won, its winner gets one more
# game and nothing else changes, except that the next game or tiebreak starts
# at 0-0. A finished set does not change.

law L22_point_goes_into_game:
  for +target: Nat
  for +a: Nat
  for +b: Nat
  for +g: S.Game
  for +s: S.Side
  for live: {S.TennisSet.winner(6n, S.TennisSet{a, b, S.InGame{g}}) == None{} : Maybe<S.Side>}
  for game_goes_on: {S.Game.winner(S.Game.point(g, s)) == None{} : Maybe<S.Side>}
  {S.TennisSet.point(6n, target, S.TennisSet{a, b, S.InGame{g}}, s) == S.TennisSet{a, b, S.InGame{S.Game.point(g, s)}} : S.TennisSet}

law L22_won_game_adds_a_game:
  for +target: Nat
  for +a: Nat
  for +b: Nat
  for +g: S.Game
  for +s: S.Side
  for -w: S.Side
  for live: {S.TennisSet.winner(6n, S.TennisSet{a, b, S.InGame{g}}) == None{} : Maybe<S.Side>}
  for game_won: {S.Game.winner(S.Game.point(g, s)) == Some{w} : Maybe<S.Side>}
  {S.TennisSet.point(6n, target, S.TennisSet{a, b, S.InGame{g}}, s) == Rule.after_game(w, a, b) : S.TennisSet}

law L22_point_goes_into_tiebreak:
  for +target: Nat
  for +a: Nat
  for +b: Nat
  for +t: S.Tiebreak
  for +s: S.Side
  for live: {S.TennisSet.winner(6n, S.TennisSet{a, b, S.InTiebreak{t}}) == None{} : Maybe<S.Side>}
  for tiebreak_goes_on: {S.Tiebreak.winner(target, S.Tiebreak.point(target, t, s)) == None{} : Maybe<S.Side>}
  {S.TennisSet.point(6n, target, S.TennisSet{a, b, S.InTiebreak{t}}, s) == S.TennisSet{a, b, S.InTiebreak{S.Tiebreak.point(target, t, s)}} : S.TennisSet}

law L22_won_tiebreak_adds_a_game:
  for +target: Nat
  for +a: Nat
  for +b: Nat
  for +t: S.Tiebreak
  for +s: S.Side
  for -w: S.Side
  for live: {S.TennisSet.winner(6n, S.TennisSet{a, b, S.InTiebreak{t}}) == None{} : Maybe<S.Side>}
  for tiebreak_won: {S.Tiebreak.winner(target, S.Tiebreak.point(target, t, s)) == Some{w} : Maybe<S.Side>}
  {S.TennisSet.point(6n, target, S.TennisSet{a, b, S.InTiebreak{t}}, s) == Rule.after_game(w, a, b) : S.TennisSet}

law L22_won_set_is_final:
  for +target: Nat
  for +st: S.TennisSet
  for -w: S.Side
  for won: {S.TennisSet.winner(6n, st) == Some{w} : Maybe<S.Side>}
  for +s: S.Side
  {S.TennisSet.point(6n, target, st, s) == st : S.TennisSet}

# L9. Every set played from 0-0 that has finished has one of the scores 6-0
# to 6-4, 7-5 or 7-6, either way round; nothing else.
law L9_finished_set_score:
  for +target: Nat
  for +pts: List<&2, S.Side>
  for -w: S.Side
  for won: {S.TennisSet.winner(6n, Rule.play_set(target, pts, Rule.fresh_set())) == Some{w} : Maybe<S.Side>}
  {Rule.finished_set_ok(w, Rule.play_set(target, pts, Rule.fresh_set())) == True{} : Bool}

# L10. In every set played from 0-0, while it is in progress, a tiebreak is
# being played exactly when the games are 6-6. So a tiebreak is played only
# from 6-6; from there the set can only finish 7-6 (L9), and once it has
# finished nothing more is played (L22). Hence a 7-6 set contains exactly one
# tiebreak and no other set contains one, which is how the spec words L10.
law L10_tiebreak_exactly_at_6_all:
  for +target: Nat
  for +pts: List<&2, S.Side>
  for live: {S.TennisSet.winner(6n, Rule.play_set(target, pts, Rule.fresh_set())) == None{} : Maybe<S.Side>}
  {Rule.in_tiebreak(Rule.play_set(target, pts, Rule.fresh_set())) == Rule.six_all(Rule.play_set(target, pts, Rule.fresh_set())) : Bool}

# ---------------------------------------------------------------------------
# The match rule
# ---------------------------------------------------------------------------

# The WTA format: 6 games win a set and 2 sets win the match, with tiebreak
# target t and deciding-set tiebreak target ft.
def Rule.wta(t: Nat, ft: Nat) -> S.Format:
  S.Format{6n, t, 2n, ft}

def Rule.games_of(fmt: S.Format) -> Nat:
  match fmt:
    case S.Format{g, _, _, _}:
      g

def Rule.sets_of(fmt: S.Format) -> Nat:
  match fmt:
    case S.Format{_, _, n, _}:
      n

def Rule.side_if(a_won: Bool) -> S.Side:
  match a_won:
    case True{}:
      S.A{}
    case False{}:
      S.B{}

# Who won a finished set: the player with more games.
def Rule.score_winner(sc: S.Score) -> S.Side:
  match sc:
    case S.Score{+a, +b}:
      Rule.side_if(Nat.is_gt(a, b))

# How many of the finished sets player w won.
def Rule.sets_won(+w: S.Side, done: List<&2, S.Score>) -> Nat:
  match done:
    case Nil{}:
      0n
    case Con{sc, rest}:
      Rule.count(Rule.same(Rule.score_winner(sc), w), Rule.sets_won(w, rest))

# The winner of a match, given the finished sets, when n sets win it.
def Rule.match_winner(+n: Nat, +done: List<&2, S.Score>) -> Maybe<S.Side>:
  Rule.pick(Nat.is_ge(Rule.sets_won(S.A{}, done), n), Nat.is_ge(Rule.sets_won(S.B{}, done), n))

# The tiebreak target for the set being played: the deciding-set target when
# both players are one set from winning, otherwise the normal one.
def Rule.tiebreak_target(fmt: S.Format, +done: List<&2, S.Score>) -> Nat:
  match fmt:
    case S.Format{_, t, +n, ft}:
      Rule.choose(Bool.and(Nat.is_eq(Rule.sets_won(S.A{}, done), Nat.sub(n, 1n)), Nat.is_eq(Rule.sets_won(S.B{}, done), Nat.sub(n, 1n))), ft, t)

# The set in progress after point s, played with the format's settings.
def Rule.set_after(+fmt: S.Format, +done: List<&2, S.Score>, st: S.TennisSet, s: S.Side) -> S.TennisSet:
  S.TennisSet.point(Rule.games_of(fmt), Rule.tiebreak_target(fmt, done), st, s)

def Rule.score_of(st: S.TennisSet) -> S.Score:
  match st:
    case S.TennisSet{a, b, _}:
      S.Score{a, b}

def Rule.done_of(m: S.Match) -> List<&2, S.Score>:
  match m:
    case S.Match{_, done, _}:
      done

# Play a list of points, in order, in a match.
def Rule.play_match(+fmt: S.Format, pts: List<&2, S.Side>, m: S.Match) -> S.Match:
  match pts:
    case Nil{}:
      m
    case Con{s, rest}:
      Rule.play_match(fmt, rest, S.Match.point(fmt, m, s))

# Is this a final match score with player w as the winner: w has exactly 2
# sets and the opponent 0 or 1?
def Rule.match_score_ok(+w: S.Side, +done: List<&2, S.Score>) -> Bool:
  Bool.and(Nat.is_eq(Rule.sets_won(w, done), 2n), Nat.is_le(Rule.sets_won(Rule.other(w), done), 1n))

# Examples. Finished sets are listed most recent first.
law ex_one_set_all_is_not_over:
  {Rule.match_winner(2n, [S.Score{3n, 6n}, S.Score{6n, 4n}]) == None{} : Maybe<S.Side>}

law ex_won_in_three_sets:
  {Rule.match_winner(2n, [S.Score{7n, 6n}, S.Score{3n, 6n}, S.Score{6n, 4n}]) == Some{S.A{}} : Maybe<S.Side>}

# ---------------------------------------------------------------------------
# Match laws: L25, L23, L13, L12
# ---------------------------------------------------------------------------

# L25. The engine's verdict on who has won the match agrees with the match
# rule: the first to win `sets` sets. Without it, an engine that never ended a
# match would pass L12.
law L25_match_winner_follows_rule:
  for +fmt: S.Format
  for +first: S.Side
  for +done: List<&2, S.Score>
  for +st: S.TennisSet
  {S.Match.winner(fmt, S.Match{first, done, st}) == Rule.match_winner(Rule.sets_of(fmt), done) : Maybe<S.Side>}

# L23. A match starts at 0-0 in the first set, with no sets finished.
law L23_match_starts_at_zero:
  for +first: S.Side
  {S.Match.start(first) == S.Match{first, Nil{}, Rule.fresh_set()} : S.Match}

# L23, continued. While a match is in progress, each point goes into the set
# being played (with the deciding-set tiebreak target when it is the deciding
# set) ...
law L23_point_goes_into_set:
  for +fmt: S.Format
  for +first: S.Side
  for +done: List<&2, S.Score>
  for +st: S.TennisSet
  for +s: S.Side
  for live: {S.Match.winner(fmt, S.Match{first, done, st}) == None{} : Maybe<S.Side>}
  for set_goes_on: {S.TennisSet.winner(Rule.games_of(fmt), Rule.set_after(fmt, done, st, s)) == None{} : Maybe<S.Side>}
  {S.Match.point(fmt, S.Match{first, done, st}, s) == S.Match{first, done, Rule.set_after(fmt, done, st, s)} : S.Match}

# ... and when that set is won, its score is added to the finished sets (so
# its winner has one more set) and the next set starts at 0-0. Who serves it
# follows from L11.
law L23_won_set_is_recorded:
  for +fmt: S.Format
  for +first: S.Side
  for +done: List<&2, S.Score>
  for +st: S.TennisSet
  for +s: S.Side
  for -w: S.Side
  for live: {S.Match.winner(fmt, S.Match{first, done, st}) == None{} : Maybe<S.Side>}
  for set_won: {S.TennisSet.winner(Rule.games_of(fmt), Rule.set_after(fmt, done, st, s)) == Some{w} : Maybe<S.Side>}
  {S.Match.point(fmt, S.Match{first, done, st}, s) == S.Match{first, Rule.score_of(Rule.set_after(fmt, done, st, s)) <> done, Rule.fresh_set()} : S.Match}

# L13. Once a match is won, further points do not change it.
law L13_won_match_is_final:
  for +fmt: S.Format
  for +m: S.Match
  for -w: S.Side
  for won: {S.Match.winner(fmt, m) == Some{w} : Maybe<S.Side>}
  for +s: S.Side
  {S.Match.point(fmt, m, s) == m : S.Match}

# L12. Every match played from the start that has finished has a winner with
# exactly 2 sets; the loser has 0 or 1.
law L12_finished_match_score:
  for +t: Nat
  for +ft: Nat
  for +first: S.Side
  for +pts: List<&2, S.Side>
  for -w: S.Side
  for won: {S.Match.winner(Rule.wta(t, ft), Rule.play_match(Rule.wta(t, ft), pts, S.Match.start(first))) == Some{w} : Maybe<S.Side>}
  {Rule.match_score_ok(w, Rule.done_of(Rule.play_match(Rule.wta(t, ft), pts, S.Match.start(first)))) == True{} : Bool}

# ---------------------------------------------------------------------------
# Who serves: L11
# ---------------------------------------------------------------------------

# Who serves game number n (counting from 0) when `first` served game 0:
# players alternate every game.
def Rule.alternate(n: Nat, first: S.Side) -> S.Side:
  match n:
    case 0n:
      first
    case 1n+p:
      Rule.alternate(p, Rule.other(first))

# The number of games in the finished sets, tiebreaks included (7-6 is 13).
def Rule.games_in(done: List<&2, S.Score>) -> Nat:
  match done:
    case Nil{}:
      0n
    case Con{sc, rest}:
      match sc:
        case S.Score{a, b}:
          Nat.add(Nat.add(a, b), Rule.games_in(rest))

# Who serves the next point of the game or tiebreak served first by
# game_server.
def Rule.play_server(game_server: S.Side, play: S.Play) -> S.Side:
  match play:
    case S.InGame{_}:
      game_server
    case S.InTiebreak{t}:
      match t:
        case S.Tiebreak{x, y}:
          S.Tiebreak.server(game_server, Nat.add(x, y))

# Who serves the next point of a set whose first game is served by set_first.
def Rule.set_server(set_first: S.Side, st: S.TennisSet) -> S.Side:
  match st:
    case S.TennisSet{a, b, play}:
      Rule.play_server(Rule.alternate(Nat.add(a, b), set_first), play)

# The serve rule. Count every game played in the match so far, the tiebreak
# counting as a game, and alternate from the match's first server. In an
# ordinary game that player serves every point. In a tiebreak, that player
# serves its first point and the 1-then-2s pattern (L8) follows.
def Rule.match_server(m: S.Match) -> S.Side:
  match m:
    case S.Match{first, done, st}:
      Rule.set_server(Rule.alternate(Rule.games_in(done), first), st)

# Examples, in a match where A serves first.

# A serves the first game.
law ex_a_serves_game_1:
  {Rule.match_server(S.Match{S.A{}, Nil{}, Rule.fresh_set()}) == S.A{} : S.Side}

# At 3-2 in the first set (game 6), B serves.
law ex_b_serves_game_6:
  {Rule.match_server(S.Match{S.A{}, Nil{}, S.TennisSet{3n, 2n, S.InGame{S.Game{0n, 0n}}}}) == S.B{} : S.Side}

# At 6-6 in the first set, the tiebreak is game 13: A serves its first point ...
law ex_a_starts_the_tiebreak:
  {Rule.match_server(S.Match{S.A{}, Nil{}, S.TennisSet{6n, 6n, S.InTiebreak{S.Tiebreak{0n, 0n}}}}) == S.A{} : S.Side}

# ... and B serves the second.
law ex_b_serves_tiebreak_point_2:
  {Rule.match_server(S.Match{S.A{}, Nil{}, S.TennisSet{6n, 6n, S.InTiebreak{S.Tiebreak{1n, 0n}}}}) == S.B{} : S.Side}

# After a 7-6 first set, B serves the first game of set 2: B received first in
# the tiebreak.
law ex_b_serves_after_tiebreak_set:
  {Rule.match_server(S.Match{S.A{}, [S.Score{7n, 6n}], Rule.fresh_set()}) == S.B{} : S.Side}

# After a 6-4 first set (10 games), A serves the first game of set 2.
law ex_a_serves_after_6_4_set:
  {Rule.match_server(S.Match{S.A{}, [S.Score{6n, 4n}], Rule.fresh_set()}) == S.A{} : S.Side}

# L11. The engine's choice of server, which the simulator uses to pick whose
# serve chance applies, follows the serve rule above in every match state.
law L11_server_follows_rule:
  for +m: S.Match
  {S.Match.server(m) == Rule.match_server(m) : S.Side}

# L11, continued. In an ordinary game, the same player serves every point: a
# point that doesn't finish the game leaves the server unchanged.
law L11_same_server_within_game:
  for +fmt: S.Format
  for +first: S.Side
  for +done: List<&2, S.Score>
  for +a: Nat
  for +b: Nat
  for +g: S.Game
  for +s: S.Side
  for live: {S.Match.winner(fmt, S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}) == None{} : Maybe<S.Side>}
  for set_live: {S.TennisSet.winner(Rule.games_of(fmt), S.TennisSet{a, b, S.InGame{g}}) == None{} : Maybe<S.Side>}
  for game_goes_on: {S.Game.winner(S.Game.point(g, s)) == None{} : Maybe<S.Side>}
  {S.Match.server(S.Match.point(fmt, S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}, s)) == S.Match.server(S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}) : S.Side}

# ===========================================================================
# MILESTONE 4: simulation. Approved by the owner.
# ===========================================================================
#
# How this section is organised:
# - L1 is about the point chances the simulator is given.
# - L26 is about one simulated point, L27 about one simulated match, and L14
#   about adding up many runs.
# - The laws treat the random numbers themselves (Sim.Rng.roll) as given: no
#   law says they look random. That is checked by validation instead, against
#   the exact calculator (SPEC.md, Outputs and validation). What the laws do
#   pin down is how the simulator uses them.

# ---------------------------------------------------------------------------
# Point chances: L1
# ---------------------------------------------------------------------------

# A number from the input is a valid point chance when it is at most 10,000
# (100%). It can't be below 0: U32 has no negative numbers.
def Rule.keep_if(ok: Bool, p: U32) -> Maybe<U32>:
  match ok:
    case True{}:
      Some{p}
    case False{}:
      None{}

def Rule.valid_chance(+p: U32) -> Maybe<U32>:
  Rule.keep_if(U32.is_le(p, 10000), p)

# The number inside a checked chance, if the check accepted it.
def Rule.made_value(m: Maybe<Sim.Chance>) -> Maybe<U32>:
  match m:
    case Some{c}:
      Some{Sim.Chance.value(c)}
    case None{}:
      None{}

# Examples.
law ex_chance_100_percent_is_valid:
  {Rule.valid_chance(10000) == Some{10000} : Maybe<U32>}

law ex_chance_above_100_percent_is_rejected:
  {Rule.valid_chance(10001) == None{} : Maybe<U32>}

# L1. Every point chance is between 0 and 10,000.
law L1_chance_in_range:
  for +c: Sim.Chance
  {U32.is_le(Sim.Chance.value(c), 10000) == True{} : Bool}

# L1, continued. The input check accepts exactly the numbers from 0 to 10,000,
# and keeps them unchanged; anything else is rejected, never clamped. (Without
# this, a check that wrongly rejected 10,000, or turned 12,000 into 10,000,
# would still satisfy the law above.)
law L1_input_check:
  for +p: U32
  {Rule.made_value(Sim.Chance.make(p)) == Rule.valid_chance(p) : Maybe<U32>}

# ---------------------------------------------------------------------------
# One simulated point: L26
# ---------------------------------------------------------------------------

# The point chance of whoever is serving: pa when A serves, pb when B serves.
def Rule.serve_chance(server: S.Side, pa: U32, pb: U32) -> U32:
  match server:
    case S.A{}:
      pa
    case S.B{}:
      pb

def Rule.server_or_receiver(server_won: Bool, +server: S.Side) -> S.Side:
  match server_won:
    case True{}:
      server
    case False{}:
      Rule.other(server)

# Who wins a point: the server when the random number (0 to 9,999) is below
# her point chance, the receiver otherwise. With a chance of 6000, the 6,000
# numbers 0 to 5,999 go to the server: exactly 60%.
def Rule.point_winner(+server: S.Side, pa: U32, pb: U32, roll: U32) -> S.Side:
  Rule.server_or_receiver(U32.is_lt(roll, Rule.serve_chance(server, pa, pb)), server)

# One simulated point: the server is the one the serve rule picks (L11), and
# the point is scored by the scoring engine.
def Rule.step(+fmt: S.Format, pa: U32, pb: U32, +m: S.Match, roll: U32) -> S.Match:
  S.Match.point(fmt, m, Rule.point_winner(Rule.match_server(m), pa, pb, roll))

# Examples: A serves with a 60% chance (6000), B with 50% (5000).
law ex_roll_below_chance_is_server_point:
  {Rule.point_winner(S.A{}, 6000, 5000, 5999) == S.A{} : S.Side}

law ex_roll_at_chance_is_receiver_point:
  {Rule.point_winner(S.A{}, 6000, 5000, 6000) == S.B{} : S.Side}

# B serving uses B's chance, not A's: 5,500 is below A's 6000 but not B's 5000.
law ex_b_serving_uses_b_chance:
  {Rule.point_winner(S.B{}, 6000, 5000, 5500) == S.A{} : S.Side}

# A 100% server wins even the highest roll; a 0% server loses even the lowest.
law ex_100_percent_server_wins_every_roll:
  {Rule.point_winner(S.A{}, 10000, 5000, 9999) == S.A{} : S.Side}

law ex_0_percent_server_loses_every_roll:
  {Rule.point_winner(S.B{}, 6000, 0, 0) == S.A{} : S.Side}

# L26. Each simulated point goes to the server exactly when the random number
# is below the server's point chance, and to the receiver otherwise; the
# server is the one L11 picks. Without this, a simulator that used the wrong
# player's chance (or the receiver's) would pass every scoring law.
law L26_point_follows_serve_chance:
  for +fmt: S.Format
  for +ca: Sim.Chance
  for +cb: Sim.Chance
  for +m: S.Match
  for +roll: U32
  {Sim.Point.simulate(fmt, ca, cb, m, roll) == Rule.step(fmt, Sim.Chance.value(ca), Sim.Chance.value(cb), m, roll) : S.Match}

# ---------------------------------------------------------------------------
# One simulated match: L27
# ---------------------------------------------------------------------------

# Play n points, numbered k, k+1, ..., each with its own random number from
# the stream of the match in `slot` of run `run`. Points after the match is
# won change nothing (L13).
def Rule.play_points(n: Nat, +fmt: S.Format, +pa: U32, +pb: U32, +seed: U32, +run: U32, +slot: U32, +k: U32, m: S.Match) -> S.Match:
  match n:
    case 0n:
      m
    case 1n+p:
      Rule.play_points(p, fmt, pa, pb, seed, run, slot, U32.inc(k), Rule.step(fmt, pa, pb, m, Sim.Rng.roll(seed, run, slot, k)))

def Rule.report.go(w: Maybe<S.Side>, m: S.Match) -> Sim.Outcome:
  match w:
    case Some{x}:
      Sim.Won{x, m}
    case None{}:
      Sim.Unfinished{m}

# How a match is reported: won by the player the match rule says has won it,
# otherwise unfinished.
def Rule.report(+fmt: S.Format, +m: S.Match) -> Sim.Outcome:
  Rule.report.go(Rule.match_winner(Rule.sets_of(fmt), Rule.done_of(m)), m)

# The point cap (SPEC.md, Simulation).
def Rule.cap() -> Nat:
  1000n

# L27. A simulated match plays the first 1,000 points of its random stream
# (numbered 0 to 999), starting from 0-0 with `first` serving. It is reported
# as won only by the player who has won by then; otherwise it is reported as
# unfinished. The engine may stop as soon as the match is won (L13 says the
# remaining points would change nothing), but it may not stop earlier, play a
# 1,001st point, skip or reuse a random number, or count an unfinished match
# as a win.
law L27_match_plays_at_most_1000_points:
  for +fmt: S.Format
  for +ca: Sim.Chance
  for +cb: Sim.Chance
  for +seed: U32
  for +run: U32
  for +slot: U32
  for +first: S.Side
  {Sim.Match.simulate(fmt, ca, cb, seed, run, slot, first) == Rule.report(fmt, Rule.play_points(Rule.cap(), fmt, Sim.Chance.value(ca), Sim.Chance.value(cb), seed, run, slot, 0, S.Match.start(first))) : Sim.Outcome}

# L27, continued. In milestone 4 a run is one match, in slot 0, with the first
# server chosen by the coin toss. (So L27 covers every match that is counted.)
law L27_single_run_is_one_match:
  for +fmt: S.Format
  for +ca: Sim.Chance
  for +cb: Sim.Chance
  for +seed: U32
  for +run: U32
  {Sim.Run.single(fmt, ca, cb, seed, run) == Sim.Match.simulate(fmt, ca, cb, seed, run, 0, Sim.Rng.coin(seed, run, 0)) : Sim.Outcome}

# ---------------------------------------------------------------------------
# Counting many runs: L14
# ---------------------------------------------------------------------------

# Every list of d bits (True or False), each exactly once: the d bits of the
# 2^d runs in a block. Those starting False come first, then those starting
# True.
def Rule.cons_all(+b: Bool, xss: List<&2, List<&2, Bool>>) -> List<&2, List<&2, Bool>>:
  match xss:
    case Nil{}:
      Nil{}
    case Con{xs, rest}:
      (b <> xs) <> Rule.cons_all(b, rest)

def Rule.paths(+d: Nat) -> List<&2, List<&2, Bool>>:
  match d:
    case 0n:
      [[]]
    case 1n+p:
      List.append(&2, List<&2, Bool>, Rule.cons_all(False{}, Rule.paths(p)), Rule.cons_all(True{}, Rule.paths(p)))

def Rule.bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# The run number given by a list of bits, written after the block number
# `prefix` in binary: the bits [True, False, True] in block 0 are run 5
# (binary 101); in block 1 they are run 13 (binary 1101).
def Rule.number(path: List<&2, Bool>, prefix: U32) -> U32:
  match path:
    case Nil{}:
      prefix
    case Con{b, rest}:
      Rule.number(rest, (prefix * 2 + Rule.bit(b) : U32))

# Tallies, added field by field.
def Rule.add_sets(x: Sim.SetCounts, y: Sim.SetCounts) -> Sim.SetCounts:
  match x y:
    case Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} Sim.SetCounts{y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}:
      Sim.SetCounts{Nat.add(x1, y1), Nat.add(x2, y2), Nat.add(x3, y3), Nat.add(x4, y4), Nat.add(x5, y5), Nat.add(x6, y6), Nat.add(x7, y7), Nat.add(x8, y8), Nat.add(x9, y9), Nat.add(x10, y10), Nat.add(x11, y11), Nat.add(x12, y12), Nat.add(x13, y13), Nat.add(x14, y14), Nat.add(x15, y15)}

def Rule.add(x: Sim.Tally, y: Sim.Tally) -> Sim.Tally:
  match x y:
    case Sim.Tally{xa, xb, xu, xs} Sim.Tally{ya, yb, yu, ys}:
      Sim.Tally{Nat.add(xa, ya), Nat.add(xb, yb), Nat.add(xu, yu), Rule.add_sets(xs, ys)}

def Rule.no_sets() -> Sim.SetCounts:
  Sim.SetCounts{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

def Rule.nothing() -> Sim.Tally:
  Sim.Tally{0n, 0n, 0n, Rule.no_sets()}

# 1 if the set score is x-y (A's games first), else 0.
def Rule.is_score(+a: Nat, +b: Nat, x: Nat, y: Nat) -> Nat:
  Rule.count(Bool.and(Nat.is_eq(a, x), Nat.is_eq(b, y)), 0n)

# One finished set, counted under its score.
def Rule.one_set(sc: S.Score) -> Sim.SetCounts:
  match sc:
    case S.Score{+a, +b}:
      Sim.SetCounts{Rule.is_score(a, b, 6n, 0n), Rule.is_score(a, b, 6n, 1n), Rule.is_score(a, b, 6n, 2n), Rule.is_score(a, b, 6n, 3n), Rule.is_score(a, b, 6n, 4n), Rule.is_score(a, b, 7n, 5n), Rule.is_score(a, b, 7n, 6n), Rule.is_score(a, b, 0n, 6n), Rule.is_score(a, b, 1n, 6n), Rule.is_score(a, b, 2n, 6n), Rule.is_score(a, b, 3n, 6n), Rule.is_score(a, b, 4n, 6n), Rule.is_score(a, b, 5n, 7n), Rule.is_score(a, b, 6n, 7n), Rule.count(Bool.not(Bool.or(Rule.set_score_ok(a, b), Rule.set_score_ok(b, a))), 0n)}

def Rule.set_scores(done: List<&2, S.Score>) -> Sim.SetCounts:
  match done:
    case Nil{}:
      Rule.no_sets()
    case Con{sc, rest}:
      Rule.add_sets(Rule.one_set(sc), Rule.set_scores(rest))

def Rule.win_for(+w: S.Side, s: S.Side) -> Nat:
  Rule.count(Rule.same(w, s), 0n)

# What one run adds to the totals: one win for the winner and the scores of
# the sets played, or one unfinished match.
def Rule.tally_of(o: Sim.Outcome) -> Sim.Tally:
  match o:
    case Sim.Won{+w, m}:
      Sim.Tally{Rule.win_for(w, S.A{}), Rule.win_for(w, S.B{}), 0n, Rule.set_scores(Rule.done_of(m))}
    case Sim.Unfinished{_}:
      Sim.Tally{0n, 0n, 1n, Rule.no_sets()}

# The totals of a list of tallies, added one after another.
def Rule.sum(ts: List<&2, Sim.Tally>) -> Sim.Tally:
  match ts:
    case Nil{}:
      Rule.nothing()
    case Con{t, rest}:
      Rule.add(t, Rule.sum(rest))

# The tally of each run in block `prefix`, one per list of bits.
def Rule.results(+fmt: S.Format, +ca: Sim.Chance, +cb: Sim.Chance, +seed: U32, +prefix: U32, paths: List<&2, List<&2, Bool>>) -> List<&2, Sim.Tally>:
  match paths:
    case Nil{}:
      Nil{}
    case Con{path, rest}:
      Rule.tally_of(Sim.Run.single(fmt, ca, cb, seed, Rule.number(path, prefix))) <> Rule.results(fmt, ca, cb, seed, prefix, rest)

# Examples.
law ex_two_bits_make_four_runs:
  {Rule.paths(2n) == [[False{}, False{}], [False{}, True{}], [True{}, False{}], [True{}, True{}]] : List<&2, List<&2, Bool>>}

law ex_run_5_in_block_0:
  {Rule.number([True{}, False{}, True{}], 0) == 5 : U32}

law ex_run_13_in_block_1:
  {Rule.number([True{}, False{}, True{}], 1) == 13 : U32}

# B won a set 6-3: counted under b63 only.
law ex_set_3_6_counted_as_b63:
  {Rule.one_set(S.Score{3n, 6n}) == Sim.SetCounts{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n, 0n, 0n, 0n, 0n} : Sim.SetCounts}

# L14. The total over all runs counts every run exactly once, however the work
# is split across cores. Precisely: the engine's totals for the 2^d runs in a
# block equal the plain sum, one run after another, of one tally for each list
# of d bits, that is, one for each run number in the block.
#
# (The spec's first wording, "the same seed and inputs always give the same
# result", is automatically true in Bend, which has no hidden state, so it
# needs no law. Reruns and runs on different numbers of cores are still
# compared by running them.)
law L14_every_run_counted_once:
  for +d: Nat
  for +fmt: S.Format
  for +ca: Sim.Chance
  for +cb: Sim.Chance
  for +seed: U32
  for +prefix: U32
  {Sim.Run.tally(d, fmt, ca, cb, seed, prefix) == Rule.sum(Rule.results(fmt, ca, cb, seed, prefix, Rule.paths(d))) : Sim.Tally}
