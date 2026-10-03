# scoring.bend: point, game, tiebreak, set and match scoring.
#
# Milestone 2 status: INTERFACE ONLY. The types and function signatures below
# are what engine/LAWS.bend talks about. The bodies are `?TODO` on purpose:
# no implementation is written until the owner approves the game-layer laws.

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

# Who has won the game, if anyone: Some{A{}}, Some{B{}} or None{}.
def Game.winner(g: Game) -> Maybe<Side>:
  ?TODO

# The game after one more point, won by player `s`.
def Game.point(g: Game, s: Side) -> Game:
  ?TODO
