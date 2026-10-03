# simulate.bend: the command-line entry point for single-match simulation.
#
#   bend engine/simulate.bend -o build/simulate
#   ./build/simulate SEED BITS CHANCE_A CHANCE_B [--threads N]
#
# Plays 2^BITS matches between A and B, who win CHANCE_A and CHANCE_B points
# out of 10,000 on their own serve (WTA format: best of three, 7-point
# tiebreaks). Prints a CSV header and one line of counts; prep/ turns that
# into result files.

import Base
import ./scoring.bend as S
import ./sim.bend as Sim

# Best of three sets, 6 games a set, 7-point tiebreaks, including the
# deciding set.
def wta() -> S.Format:
  S.Format{6n, 7n, 2n, 7n}

def header() -> String:
  "seed,bits,chance_a,chance_b,a_wins,b_wins,unfinished,a60,a61,a62,a63,a64,a75,a76,b60,b61,b62,b63,b64,b75,b76,other_sets"

def show_sets(c: Sim.SetCounts) -> List<&2, String>:
  match c:
    case Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}:
      [Nat.show(x1), Nat.show(x2), Nat.show(x3), Nat.show(x4), Nat.show(x5), Nat.show(x6), Nat.show(x7), Nat.show(x8), Nat.show(x9), Nat.show(x10), Nat.show(x11), Nat.show(x12), Nat.show(x13), Nat.show(x14), Nat.show(x15)]

def show_tally(t: Sim.Tally) -> List<&2, String>:
  match t:
    case Sim.Tally{a, b, u, sets}:
      Nat.show(a) <> Nat.show(b) <> Nat.show(u) <> show_sets(sets)

def chance.check(+p: U32, c: Maybe<Sim.Chance>) -> IO(Sim.Chance):
  match c:
    case Some{x}:
      IO.pure(Sim.Chance, x)
    case None{}:
      IO.die(Sim.Chance, 2, "point chance must be 0 to 10000, got " ++ U32.show(p))

def chance.go(r: Maybe<&2, U32>) -> IO(Sim.Chance):
  match r:
    case Some{+p}:
      chance.check(p, Sim.Chance.make(p))
    case None{}:
      IO.die(Sim.Chance, 2, "a point chance must be a whole number")

def chance(s: String) -> IO(Sim.Chance):
  chance.go(U32.read(s))

def number.go(r: Maybe<&2, U32>) -> IO(U32):
  match r:
    case Some{n}:
      IO.pure(U32, n)
    case None{}:
      IO.die(U32, 2, "SEED must be a whole number below 2^32")

def number(s: String) -> IO(U32):
  number.go(U32.read(s))

def bits.check(+n: Nat, ok: Bool) -> IO(Nat):
  match ok:
    case True{}:
      IO.pure(Nat, n)
    case False{}:
      IO.die(Nat, 2, "BITS must be at most 30")

def bits.go(r: Maybe<&2, Nat>) -> IO(Nat):
  match r:
    case Some{+n}:
      bits.check(n, Nat.is_le(n, 30n))
    case None{}:
      IO.die(Nat, 2, "BITS must be a whole number")

def bits(s: String) -> IO(Nat):
  bits.go(Nat.read(s))

def report(+seed: U32, +d: Nat, +ca: Sim.Chance, +cb: Sim.Chance) -> String:
  String.join(U32.show(seed) <> Nat.show(d) <> U32.show(Sim.Chance.value(ca)) <> U32.show(Sim.Chance.value(cb)) <> show_tally(Sim.Run.tally(d, wta(), ca, cb, seed, 0)), ",")

def run(seed_s: String, bits_s: String, a_s: String, b_s: String) -> IO(Unit):
  do IO<Unit>:
    seed : U32 <- number(seed_s)
    d : Nat <- bits(bits_s)
    ca : Sim.Chance <- chance(a_s)
    cb : Sim.Chance <- chance(b_s)
    IO.print(header())
    IO.print(report(seed, d, ca, cb))

def usage() -> IO(Unit):
  IO.die(Unit, 2, "usage: simulate SEED BITS CHANCE_A CHANCE_B")

def dispatch(args: List<String>) -> IO(Unit):
  match args:
    case Con{_, Con{seed_s, Con{bits_s, Con{a_s, Con{b_s, Nil{}}}}}}:
      run(seed_s, bits_s, a_s, b_s)
    case _:
      usage()

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    dispatch(args)
