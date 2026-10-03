# scoring.bend: point, game, tiebreak, set and match scoring.
#
# Milestone 2: the game layer. Its laws (L2-L5, L20) are in LAWS.bend and
# proven in PROOF.bend.
# Milestone 3: tiebreak, set and match. INTERFACE ONLY for now: the types and
# signatures at the end of this file are what the draft M3 laws talk about.
# Their bodies are `?TODO` until the owner approves those laws.

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

# ---------------------------------------------------------------------------
# Tiebreak, set and match (milestone 3: interface only)
# ---------------------------------------------------------------------------

# A tiebreak, as raw points: `a` for player A, `b` for player B.
type Tiebreak is Data:
  Tiebreak{a: Nat, b: Nat}

# What is being played inside a set: an ordinary game, or the tiebreak.
type Play is Data:
  InGame{game: Game}
  InTiebreak{tiebreak: Tiebreak}

# A set: games won by A and B, and the game or tiebreak being played.
# (Called TennisSet because Bend's Base library already has a Set.)
type TennisSet is Data:
  TennisSet{a: Nat, b: Nat, play: Play}

# The final game score of a finished set, such as Score{6n, 4n}.
type Score is Data:
  Score{a: Nat, b: Nat}

# The format settings from SPEC.md: games to win a set, tiebreak target, sets
# to win the match, and the deciding set's tiebreak target.
type Format is Data:
  Format{games: Nat, tiebreak: Nat, sets: Nat, final_tiebreak: Nat}

# A match: who served first, the finished sets' scores (most recent first),
# and the set in progress.
type Match is Data:
  Match{first: Side, done: List<&2, Score>, set: TennisSet}

# Who has won a tiebreak played to `target` points, if anyone.
def Tiebreak.winner(target: Nat, t: Tiebreak) -> Maybe<Side>:
  ?TODO

# The tiebreak after one more point, won by player `s`.
def Tiebreak.point(target: Nat, t: Tiebreak, s: Side) -> Tiebreak:
  ?TODO

# Who serves the next tiebreak point, given who served its first point and how
# many points have been played.
def Tiebreak.server(first: Side, played: Nat) -> Side:
  ?TODO

# Who has won the set, if anyone, when `games` games win a set.
def TennisSet.winner(games: Nat, st: TennisSet) -> Maybe<Side>:
  ?TODO

# The set after one more point, won by player `s`.
def TennisSet.point(games: Nat, target: Nat, st: TennisSet, s: Side) -> TennisSet:
  ?TODO

# A new match, with player `first` serving first.
def Match.start(first: Side) -> Match:
  ?TODO

# Who has won the match, if anyone.
def Match.winner(fmt: Format, m: Match) -> Maybe<Side>:
  ?TODO

# The match after one more point, won by player `s`.
def Match.point(fmt: Format, m: Match, s: Side) -> Match:
  ?TODO

# Who serves the next point. The simulator uses this to pick whose serve
# chance applies, so the serve-order laws (L8, L11) are about it.
def Match.server(m: Match) -> Side:
  ?TODO
