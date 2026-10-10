# finals.bend: the command-line entry point for the WTA Finals.
#
#   bend engine/finals.bend -o build/finals
#   ./build/finals SEED BITS DRAW P1 P2 P3 P4 P5 P6 P7 P8 [additive|average] [unchecked] [--threads N]
#
# P1 to P8 are the eight players in Race to the Finals order (P1 is seed 1),
# by their names in params.bend (Sabalenka, Gauff, ...). DRAW is `seeded` for
# the seeded draw (a new draw by lot in every run, rulebook VI.B.3), or eight
# letters A and B giving the group of seeds 1 to 8 in turn: `ABBAABBA` puts
# seeds 1, 4, 5 and 8 in group A. The method defaults to additive.
#
# A field may not include a player whose stats haven't been checked by hand
# (SPEC.md, Inputs and data). `unchecked` lifts that for testing; the output
# then says so in its `checked` column.
#
# Plays 2^BITS tournaments and prints a CSV header and one line per seed:
# how often she reached the semifinals, reached the final and won the title.

import Base
import ./scoring.bend as S
import ./sim.bend as Sim
import ./params.bend as P
import ./tournament.bend as Tour
import ./simulate.bend as Cli
import ./matchup.bend as Mu

def header() -> String:
  "seed,bits,method,draw,checked,seed_no,player,semifinals,finals,titles,unfinished"

# ---------------------------------------------------------------------------
# Reading the draw
# ---------------------------------------------------------------------------

def Draw.keep(hit: Bool, n: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      n <> rest
    case False{}:
      rest

# The seeds, counting from n, whose letter is `want`.
def seeds_with(cs: List<&2, Char>, +n: Nat, +want: Char) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      []
    case Con{c, rest}:
      Draw.keep(Char.is_eq(c, want), n, seeds_with(rest, 1n+n, want))

def Draw.group(xs: List<&2, Nat>) -> Maybe<Tour.Group>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      Some{Tour.Group{a, b, c, d}}
    case _:
      None{}

def Draw.pair(a: Maybe<Tour.Group>, b: Maybe<Tour.Group>, len_ok: Bool) -> Maybe<Tour.Draw>:
  match a b len_ok:
    case Some{x} Some{y} True{}:
      Some{Tour.Fixed{x, y}}
    case _ _ _:
      None{}

def Draw.letters(+cs: List<&2, Char>) -> Maybe<Tour.Draw>:
  Draw.pair(Draw.group(seeds_with(cs, 1n, 'A')), Draw.group(seeds_with(cs, 1n, 'B')), Nat.is_eq(List.length(&2, Char, cs), 8n))

def Draw.parse.go(seeded: Bool, +s: String) -> Maybe<Tour.Draw>:
  match seeded:
    case True{}:
      Some{Tour.Seeded{}}
    case False{}:
      Draw.letters(String.to_list(s))

def Draw.parse.check(r: Maybe<Tour.Draw>, s: String) -> IO(Tour.Draw):
  match r:
    case Some{d}:
      IO.pure(Tour.Draw, d)
    case None{}:
      IO.die(Tour.Draw, 2, "DRAW must be `seeded` or eight letters A/B with four of each, got " ++ s)

def Draw.parse(+s: String) -> IO(Tour.Draw):
  Draw.parse.check(Draw.parse.go(String.eq(s, "seeded"), s), s)

# ---------------------------------------------------------------------------
# Options and the hand-checked rule
# ---------------------------------------------------------------------------

# The method after one option: additive or average set it; `unchecked`
# leaves it; anything else makes it None, for good.
def opts.method(m: Maybe<P.Method>, is_add: Bool, is_avg: Bool, is_unc: Bool) -> Maybe<P.Method>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match is_add is_avg is_unc:
        case True{} _ _:
          Some{P.Additive{}}
        case False{} True{} _:
          Some{P.Average{}}
        case False{} False{} True{}:
          Some{x}
        case False{} False{} False{}:
          None{}

# The method and whether unchecked players are allowed, from the options
# after the eight players.
def opts.go(xs: List<&2, String>, m: Maybe<P.Method>, unchecked: Bool) -> Maybe<P.Method> & Bool:
  match xs:
    case Nil{}:
      (m, unchecked)
    case Con{+x, rest}:
      opts.go(rest, opts.method(m, String.eq(x, "additive"), String.eq(x, "average"), String.eq(x, "unchecked")), Bool.or(unchecked, String.eq(x, "unchecked")))

def all_checked(ps: List<&2, P.Player>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, rest}:
      Bool.and(P.Player.checked(p), all_checked(rest))

def check_field(ok: Bool, unchecked: Bool) -> IO(Unit):
  match ok unchecked:
    case True{} _:
      IO.pure(Unit, Unit{})
    case False{} True{}:
      IO.pure(Unit, Unit{})
    case False{} False{}:
      IO.die(Unit, 2, "the field includes a player whose stats haven't been checked by hand (data/players.csv, checked_rpw and checked_dr); add `unchecked` to run anyway for testing")

# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

def nth(n: Nat, c: Tour.Counts) -> Nat:
  match n c:
    case 1n Tour.Counts{x, _, _, _, _, _, _, _}:
      x
    case 2n Tour.Counts{_, x, _, _, _, _, _, _}:
      x
    case 3n Tour.Counts{_, _, x, _, _, _, _, _}:
      x
    case 4n Tour.Counts{_, _, _, x, _, _, _, _}:
      x
    case 5n Tour.Counts{_, _, _, _, x, _, _, _}:
      x
    case 6n Tour.Counts{_, _, _, _, _, x, _, _}:
      x
    case 7n Tour.Counts{_, _, _, _, _, _, x, _}:
      x
    case _ Tour.Counts{_, _, _, _, _, _, _, x}:
      x

def rows(ps: List<&2, P.Player>, +n: Nat, +prefix: List<&2, String>, +t: Tour.Tally) -> List<&2, String>:
  match ps t:
    case Nil{} _:
      []
    case Con{p, rest} Tour.Tally{+ts, +fs, +ss, +u}:
      String.join(List.append(&2, String, prefix, [Nat.show(n), P.Player.id(p), Nat.show(nth(n, ss)), Nat.show(nth(n, fs)), Nat.show(nth(n, ts)), Nat.show(u)]), ",") <> rows(rest, 1n+n, prefix, Tour.Tally{ts, fs, ss, u})

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def field_list(f: Tour.Field) -> List<&2, P.Player>:
  match f:
    case Tour.Field{_, p1, p2, p3, p4, p5, p6, p7, p8}:
      [p1, p2, p3, p4, p5, p6, p7, p8]

def print_all(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{x, rest}:
      do IO<Unit>:
        IO.print(x)
        print_all(rest)

def report(+seed: U32, +d: Nat, +f: Tour.Field, +draw: Tour.Draw, +draw_s: String, +checked: Bool) -> List<&2, String>:
  rows(field_list(f), 1n, [U32.show(seed), Nat.show(d), P.Method.name(Tour.Event.method(f)), draw_s, show_bool(checked)], Tour.Event.tally(d, Cli.wta(), f, draw, seed, 0))

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def method_or_die(m: Maybe<P.Method>) -> IO(P.Method):
  match m:
    case Some{x}:
      IO.pure(P.Method, x)
    case None{}:
      IO.die(P.Method, 2, "options after the players must be additive, average or unchecked")

def players(names: List<&2, String>) -> IO(List<&2, P.Player>):
  match names:
    case Nil{}:
      IO.pure(List<&2, P.Player>, [])
    case Con{+s, rest}:
      do IO<List<&2, P.Player>>:
        p : P.Player <- Mu.player(s)
        ps : List<&2, P.Player> <- players(rest)
        return p <> ps

def run.field(+seed: U32, +d: Nat, +draw: Tour.Draw, +draw_s: String, +checked: Bool, +m: P.Method, ps: List<&2, P.Player>) -> IO(Unit):
  match ps:
    case Con{p1, Con{p2, Con{p3, Con{p4, Con{p5, Con{p6, Con{p7, Con{p8, Nil{}}}}}}}}}:
      do IO<Unit>:
        IO.print(header())
        print_all(report(seed, d, Tour.Field{m, p1, p2, p3, p4, p5, p6, p7, p8}, draw, draw_s, checked))
    case _:
      IO.die(Unit, 2, "need exactly eight players")

def run.go(+seed: U32, +d: Nat, +draw: Tour.Draw, +draw_s: String, +ps: List<&2, P.Player>, o: Maybe<P.Method> & Bool) -> IO(Unit):
  match o:
    case (mm, +unchecked):
      do IO<Unit>:
        m : P.Method <- method_or_die(mm)
        check_field(all_checked(ps), unchecked)
        run.field(seed, d, draw, draw_s, all_checked(ps), m, ps)

def run(seed_s: String, bits_s: String, +draw_s: String, names: List<&2, String>, opts: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    seed : U32 <- Cli.number(seed_s)
    d : Nat <- Cli.bits(bits_s)
    draw : Tour.Draw <- Draw.parse(draw_s)
    ps : List<&2, P.Player> <- players(names)
    o : Maybe<P.Method> & Bool = opts.go(opts, Some{P.Additive{}}, False{})
    run.go(seed, d, draw, draw_s, ps, o)

def copy(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      x <> copy(rest)

def usage() -> IO(Unit):
  IO.die(Unit, 2, "usage: finals SEED BITS DRAW P1 P2 P3 P4 P5 P6 P7 P8 [additive|average] [unchecked]")

def dispatch(args: List<String>) -> IO(Unit):
  match args:
    case Con{_, Con{seed_s, Con{bits_s, Con{draw_s, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, rest}}}}}}}}}}}}:
      run(seed_s, bits_s, draw_s, [a1, a2, a3, a4, a5, a6, a7, a8], copy(rest))
    case _:
      usage()

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    dispatch(args)
