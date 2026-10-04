# matchup.bend: the command-line entry point for a match between two real
# players, using the point chances in params.bend.
#
#   bend engine/matchup.bend -o build/matchup
#   ./build/matchup SEED BITS PLAYER_A PLAYER_B [additive|average] [--threads N]
#
# PLAYER is her name in params.bend (her surname: Sabalenka, Gauff, ...).
# The method defaults to additive (SPEC.md, decision 6). Plays 2^BITS
# matches, A's chance being the one for A serving to B and B's the one for B
# serving to A, and prints a CSV header and one line of counts.

import Base
import ./scoring.bend as S
import ./sim.bend as Sim
import ./params.bend as P
import ./simulate.bend as Cli

def header() -> String:
  "seed,bits,method,player_a,player_b,chance_a,chance_b,a_wins,b_wins,unfinished,a60,a61,a62,a63,a64,a75,a76,b60,b61,b62,b63,b64,b75,b76,other_sets"

# The two point chances of a match-up: A serving to B, and B serving to A.
def Matchup.chances(+m: P.Method, +a: P.Player, +b: P.Player) -> Sim.Chance & Sim.Chance:
  (P.Serve.chance(m, a, b), P.Serve.chance(m, b, a))

def report.go(+seed: U32, +d: Nat, +m: P.Method, +a: P.Player, +b: P.Player, cs: Sim.Chance & Sim.Chance) -> String:
  match cs:
    case (+ca, +cb):
      String.join(U32.show(seed) <> Nat.show(d) <> P.Method.name(m) <> P.Player.id(a) <> P.Player.id(b) <> U32.show(Sim.Chance.value(ca)) <> U32.show(Sim.Chance.value(cb)) <> Cli.show_tally(Sim.Run.tally(d, Cli.wta(), ca, cb, seed, 0)), ",")

def report(+seed: U32, +d: Nat, +m: P.Method, +a: P.Player, +b: P.Player) -> String:
  report.go(seed, d, m, a, b, Matchup.chances(m, a, b))

# ---------------------------------------------------------------------------
# Reading the arguments
# ---------------------------------------------------------------------------

def first(x: Maybe<P.Player>, y: Maybe<P.Player>) -> Maybe<P.Player>:
  match x:
    case Some{p}:
      Some{p}
    case None{}:
      y

def when(hit: Bool, p: P.Player) -> Maybe<P.Player>:
  match hit:
    case True{}:
      Some{p}
    case False{}:
      None{}

# The player whose id is s, if any.
def find(ps: List<&2, P.Player>, +s: String) -> Maybe<P.Player>:
  match ps:
    case Nil{}:
      None{}
    case Con{+p, rest}:
      first(when(String.eq(s, P.Player.id(p)), p), find(rest, s))

def ids(ps: List<&2, P.Player>) -> List<&2, String>:
  match ps:
    case Nil{}:
      []
    case Con{p, rest}:
      P.Player.id(p) <> ids(rest)

def player.go(s: String, r: Maybe<P.Player>) -> IO(P.Player):
  match r:
    case Some{p}:
      IO.pure(P.Player, p)
    case None{}:
      IO.die(P.Player, 2, "unknown player " ++ s ++ "; players: " ++ String.join(ids(P.Player.all()), " "))

def player(+s: String) -> IO(P.Player):
  player.go(s, find(P.Player.all(), s))

def method.pick(is_add: Bool, is_avg: Bool, s: String) -> IO(P.Method):
  match is_add is_avg:
    case True{} _:
      IO.pure(P.Method, P.Additive{})
    case False{} True{}:
      IO.pure(P.Method, P.Average{})
    case False{} False{}:
      IO.die(P.Method, 2, "method must be additive or average, got " ++ s)

def method(+s: String) -> IO(P.Method):
  method.pick(String.eq(s, "additive"), String.eq(s, "average"), s)

def run(seed_s: String, bits_s: String, a_s: String, b_s: String, m_s: String) -> IO(Unit):
  do IO<Unit>:
    seed : U32 <- Cli.number(seed_s)
    d : Nat <- Cli.bits(bits_s)
    a : P.Player <- player(a_s)
    b : P.Player <- player(b_s)
    m : P.Method <- method(m_s)
    IO.print(header())
    IO.print(report(seed, d, m, a, b))

def usage() -> IO(Unit):
  IO.die(Unit, 2, "usage: matchup SEED BITS PLAYER_A PLAYER_B [additive|average]")

def dispatch(args: List<String>) -> IO(Unit):
  match args:
    case Con{_, Con{seed_s, Con{bits_s, Con{a_s, Con{b_s, Nil{}}}}}}:
      run(seed_s, bits_s, a_s, b_s, "additive")
    case Con{_, Con{seed_s, Con{bits_s, Con{a_s, Con{b_s, Con{m_s, Nil{}}}}}}}:
      run(seed_s, bits_s, a_s, b_s, m_s)
    case _:
      usage()

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    dispatch(args)
