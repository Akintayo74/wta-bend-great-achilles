# scoring.bend: point, game, tiebreak, set and match scoring.
#
# Milestone 2: the game layer. Its laws (L2-L5, L20) are in LAWS.bend and
# proven in PROOF.bend.
# Milestone 3: tiebreak, set and match. Laws L6-L13 and L21-L25 are in
# LAWS.bend and proven in PROOF.bend.

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
# Tiebreak, set and match
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

# The opponent of player s.
def Side.other(s: Side) -> Side:
  match s:
    case A{}:
      B{}
    case B{}:
      A{}

# ---------------------------------------------------------------------------
# Tiebreak
# ---------------------------------------------------------------------------

# True when a player with x points has won a tiebreak played to `target`
# points against y points: she leads by at least 2 and has at least `target`.
# As in a game, the lead is checked first.
def Tiebreak.won_by(target: Nat, +x: Nat, y: Nat) -> Bool:
  Bool.and(Nat.is_ge(x, Nat.add(y, 2n)), Nat.is_ge(x, target))

# Who has won a tiebreak played to `target` points, if anyone.
def Tiebreak.winner(+target: Nat, t: Tiebreak) -> Maybe<Side>:
  match t:
    case Tiebreak{+a, +b}:
      Game.decide(Tiebreak.won_by(target, a, b), Tiebreak.won_by(target, b, a))

def Tiebreak.add_point(a: Nat, b: Nat, s: Side) -> Tiebreak:
  match s:
    case A{}:
      Tiebreak{1n+a, b}
    case B{}:
      Tiebreak{a, 1n+b}

# A finished tiebreak ignores further points; a live one counts them.
def Tiebreak.point.go(w: Maybe<Side>, a: Nat, b: Nat, s: Side) -> Tiebreak:
  match w:
    case Some{_}:
      Tiebreak{a, b}
    case None{}:
      Tiebreak.add_point(a, b, s)

# The tiebreak after one more point, won by player `s`.
def Tiebreak.point(+target: Nat, t: Tiebreak, s: Side) -> Tiebreak:
  match t:
    case Tiebreak{+a, +b}:
      Tiebreak.point.go(Tiebreak.winner(target, Tiebreak{a, b}), a, b, s)

# Walks through the tiebreak k points at a time. `s` is serving, and `more`
# says whether s still has a second point of her pair to serve.
def Tiebreak.server.go(k: Nat, s: Side, more: Bool) -> Side:
  match k:
    case 0n:
      s
    case 1n+p:
      match more:
        case True{}:
          Tiebreak.server.go(p, s, False{})
        case False{}:
          Tiebreak.server.go(p, Side.other(s), True{})

# Who serves the next tiebreak point, given who served its first point and how
# many points have been played. The first server has a single point, then
# each player serves two in turn.
def Tiebreak.server(first: Side, played: Nat) -> Side:
  Tiebreak.server.go(played, first, False{})

# ---------------------------------------------------------------------------
# Set
# ---------------------------------------------------------------------------

# True when a player with x games has won the set against y games, when
# `games` games win a set: at least `games` and a lead of 2, or games+1 to
# games after the tiebreak.
def TennisSet.won_by(+games: Nat, +x: Nat, +y: Nat) -> Bool:
  Bool.or(Bool.and(Nat.is_ge(x, games), Nat.is_ge(x, Nat.add(y, 2n))), Bool.and(Nat.is_eq(x, 1n+games), Nat.is_eq(y, games)))

# Who has won the set, if anyone, when `games` games win a set.
def TennisSet.winner(+games: Nat, st: TennisSet) -> Maybe<Side>:
  match st:
    case TennisSet{+a, +b, _}:
      Game.decide(TennisSet.won_by(games, a, b), TennisSet.won_by(games, b, a))

# What comes next: a tiebreak when the games are level at `games` all,
# otherwise a new game. Either starts at 0-0.
def TennisSet.next_play(level: Bool) -> Play:
  match level:
    case True{}:
      InTiebreak{Tiebreak{0n, 0n}}
    case False{}:
      InGame{Game{0n, 0n}}

def TennisSet.next(+games: Nat, +a: Nat, +b: Nat) -> TennisSet:
  TennisSet{a, b, TennisSet.next_play(Bool.and(Nat.is_eq(a, games), Nat.is_eq(b, games)))}

# One more game to player w, then the next game or tiebreak.
def TennisSet.add_game(+games: Nat, w: Side, a: Nat, b: Nat) -> TennisSet:
  match w:
    case A{}:
      TennisSet.next(games, 1n+a, b)
    case B{}:
      TennisSet.next(games, a, 1n+b)

# After a point in a game: still going, or won by someone.
def TennisSet.game_done(w: Maybe<Side>, +games: Nat, a: Nat, b: Nat, g: Game) -> TennisSet:
  match w:
    case None{}:
      TennisSet{a, b, InGame{g}}
    case Some{x}:
      TennisSet.add_game(games, x, a, b)

def TennisSet.game_point(+games: Nat, a: Nat, b: Nat, +g: Game) -> TennisSet:
  TennisSet.game_done(Game.winner(g), games, a, b, g)

# After a point in a tiebreak: still going, or won by someone.
def TennisSet.tiebreak_done(w: Maybe<Side>, +games: Nat, a: Nat, b: Nat, t: Tiebreak) -> TennisSet:
  match w:
    case None{}:
      TennisSet{a, b, InTiebreak{t}}
    case Some{x}:
      TennisSet.add_game(games, x, a, b)

def TennisSet.tiebreak_point(+games: Nat, +target: Nat, a: Nat, b: Nat, +t: Tiebreak) -> TennisSet:
  TennisSet.tiebreak_done(Tiebreak.winner(target, t), games, a, b, t)

# A point in a live set goes into the game or tiebreak being played.
def TennisSet.play_point(+games: Nat, +target: Nat, a: Nat, b: Nat, play: Play, s: Side) -> TennisSet:
  match play:
    case InGame{g}:
      TennisSet.game_point(games, a, b, Game.point(g, s))
    case InTiebreak{t}:
      TennisSet.tiebreak_point(games, target, a, b, Tiebreak.point(target, t, s))

# A finished set ignores further points; a live one plays them.
def TennisSet.point.go(w: Maybe<Side>, +games: Nat, +target: Nat, a: Nat, b: Nat, play: Play, s: Side) -> TennisSet:
  match w:
    case Some{_}:
      TennisSet{a, b, play}
    case None{}:
      TennisSet.play_point(games, target, a, b, play, s)

# The set after one more point, won by player `s`.
def TennisSet.point(+games: Nat, +target: Nat, st: TennisSet, s: Side) -> TennisSet:
  match st:
    case TennisSet{+a, +b, +play}:
      TennisSet.point.go(TennisSet.winner(games, TennisSet{a, b, play}), games, target, a, b, play, s)

# ---------------------------------------------------------------------------
# Match
# ---------------------------------------------------------------------------

def Match.games(fmt: Format) -> Nat:
  match fmt:
    case Format{g, _, _, _}:
      g

def Match.sets(fmt: Format) -> Nat:
  match fmt:
    case Format{_, _, n, _}:
      n

def Match.same(x: Side, y: Side) -> Bool:
  match x y:
    case A{} A{}:
      True{}
    case B{} B{}:
      True{}
    case A{} B{}:
      False{}
    case B{} A{}:
      False{}

def Match.count(hit: Bool, n: Nat) -> Nat:
  match hit:
    case True{}:
      1n+n
    case False{}:
      n

def Match.side_if(a_won: Bool) -> Side:
  match a_won:
    case True{}:
      A{}
    case False{}:
      B{}

# Who won a finished set: the player with more games.
def Match.score_winner(sc: Score) -> Side:
  match sc:
    case Score{+a, +b}:
      Match.side_if(Nat.is_gt(a, b))

# How many of the finished sets player w won.
def Match.sets_won(+w: Side, done: List<&2, Score>) -> Nat:
  match done:
    case Nil{}:
      0n
    case Con{sc, rest}:
      Match.count(Match.same(Match.score_winner(sc), w), Match.sets_won(w, rest))

# Who has won the match, if anyone: the first to n sets.
def Match.decide(+n: Nat, +done: List<&2, Score>) -> Maybe<Side>:
  Game.decide(Nat.is_ge(Match.sets_won(A{}, done), n), Nat.is_ge(Match.sets_won(B{}, done), n))

# Who has won the match, if anyone.
def Match.winner(fmt: Format, m: Match) -> Maybe<Side>:
  match m:
    case Match{_, +done, _}:
      Match.decide(Match.sets(fmt), done)

def Match.choose(c: Bool, yes: Nat, no: Nat) -> Nat:
  match c:
    case True{}:
      yes
    case False{}:
      no

# The tiebreak target for the set being played: the deciding-set target when
# both players are one set from winning, otherwise the normal one.
def Match.tiebreak_target(fmt: Format, +done: List<&2, Score>) -> Nat:
  match fmt:
    case Format{_, t, +n, ft}:
      Match.choose(Bool.and(Nat.is_eq(Match.sets_won(A{}, done), Nat.sub(n, 1n)), Nat.is_eq(Match.sets_won(B{}, done), Nat.sub(n, 1n))), ft, t)

# The set in progress after point s.
def Match.set_after(+fmt: Format, +done: List<&2, Score>, st: TennisSet, s: Side) -> TennisSet:
  TennisSet.point(Match.games(fmt), Match.tiebreak_target(fmt, done), st, s)

def Match.fresh_set() -> TennisSet:
  TennisSet{0n, 0n, InGame{Game{0n, 0n}}}

def Match.score_of(st: TennisSet) -> Score:
  match st:
    case TennisSet{a, b, _}:
      Score{a, b}

# After a point: the set goes on, or it is won and recorded, and a new set
# starts at 0-0.
def Match.set_done(w: Maybe<Side>, first: Side, done: List<&2, Score>, +st: TennisSet) -> Match:
  match w:
    case None{}:
      Match{first, done, st}
    case Some{_}:
      Match{first, Match.score_of(st) <> done, Match.fresh_set()}

def Match.set_point(+fmt: Format, first: Side, done: List<&2, Score>, +st: TennisSet) -> Match:
  Match.set_done(TennisSet.winner(Match.games(fmt), st), first, done, st)

# A finished match ignores further points; a live one plays them.
def Match.point.go(w: Maybe<Side>, +fmt: Format, first: Side, +done: List<&2, Score>, st: TennisSet, s: Side) -> Match:
  match w:
    case Some{_}:
      Match{first, done, st}
    case None{}:
      Match.set_point(fmt, first, done, Match.set_after(fmt, done, st, s))

# The match after one more point, won by player `s`.
def Match.point(+fmt: Format, m: Match, s: Side) -> Match:
  match m:
    case Match{+first, +done, +st}:
      Match.point.go(Match.winner(fmt, Match{first, done, st}), fmt, first, done, st, s)

# A new match, with player `first` serving first.
def Match.start(first: Side) -> Match:
  Match{first, Nil{}, Match.fresh_set()}

# Who serves game number n (counting from 0) when `first` served game 0.
def Match.alternate(n: Nat, first: Side) -> Side:
  match n:
    case 0n:
      first
    case 1n+p:
      Match.alternate(p, Side.other(first))

# The number of games in the finished sets, tiebreaks included.
def Match.games_in(done: List<&2, Score>) -> Nat:
  match done:
    case Nil{}:
      0n
    case Con{sc, rest}:
      match sc:
        case Score{a, b}:
          Nat.add(Nat.add(a, b), Match.games_in(rest))

def Match.play_server(game_server: Side, play: Play) -> Side:
  match play:
    case InGame{_}:
      game_server
    case InTiebreak{t}:
      match t:
        case Tiebreak{x, y}:
          Tiebreak.server(game_server, Nat.add(x, y))

def Match.set_server(set_first: Side, st: TennisSet) -> Side:
  match st:
    case TennisSet{a, b, play}:
      Match.play_server(Match.alternate(Nat.add(a, b), set_first), play)

# Who serves the next point. The simulator uses this to pick whose serve
# chance applies. Games alternate from the match's first server, counting
# every game in the match (tiebreaks included); in a tiebreak the 1-then-2s
# pattern starts from that game's server.
def Match.server(m: Match) -> Side:
  match m:
    case Match{first, done, st}:
      Match.set_server(Match.alternate(Match.games_in(done), first), st)
