# scoring.bend: point, game, tiebreak, set and match scoring.
#
# Milestone 2: the game layer. Its laws (L2-L5, L20) are in LAWS.bend and
# proven in PROOF.bend. Tiebreak, set and match come in milestone 3.

import Base

# The two players in a match.
type Side is Data:
  A{}
  B{}

# A game, as the raw number of points each player has won in it: `a` for
# player A, `b` for player B. Scores are not shortened to tennis names, so
# 40-40 is Game{3n, 3n}, and after two more deuces it is Game{5n, 5n}.
type Game is Data:
  Game{a: Nat, b: Nat}

# ---------------------------------------------------------------------------
# Game
# ---------------------------------------------------------------------------

# True when a player with x points has won the game against an opponent with
# y points: she leads by at least 2 and has at least 4 points. The lead is
# checked first because it settles every deuce and advantage score on its own.
def Game.won_by(+x: Nat, y: Nat) -> Bool:
  Bool.and(Nat.is_ge(x, Nat.add(y, 2n)), Nat.is_ge(x, 4n))

# Turns "has A won?" and "has B won?" into the winner, if any.
def Game.decide(a_won: Bool, b_won: Bool) -> Maybe<Side>:
  match a_won:
    case True{}:
      Some{A{}}
    case False{}:
      match b_won:
        case True{}:
          Some{B{}}
        case False{}:
          None{}

# Who has won the game, if anyone: Some{A{}}, Some{B{}} or None{}.
def Game.winner(g: Game) -> Maybe<Side>:
  match g:
    case Game{+a, +b}:
      Game.decide(Game.won_by(a, b), Game.won_by(b, a))

# Adds one point to player s's count.
def Game.add_point(a: Nat, b: Nat, s: Side) -> Game:
  match s:
    case A{}:
      Game{1n+a, b}
    case B{}:
      Game{a, 1n+b}

# A finished game ignores further points; a live one counts them.
def Game.point.go(w: Maybe<Side>, a: Nat, b: Nat, s: Side) -> Game:
  match w:
    case Some{_}:
      Game{a, b}
    case None{}:
      Game.add_point(a, b, s)

# The game after one more point, won by player `s`.
def Game.point(g: Game, s: Side) -> Game:
  match g:
    case Game{+a, +b}:
      Game.point.go(Game.winner(Game{a, b}), a, b, s)
