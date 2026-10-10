import Base
import ./scoring.bend as S
import ./sim.bend as Sim
import ./LAWS.bend as Laws
import ./tournament.bend as Tour
import ./params.bend as P
import ./proof_tables.bend as T

def Laws.ex_40_15_is_not_over():
  {==}

def Laws.ex_game_from_40_15():
  {==}

def Laws.ex_advantage_is_not_over():
  {==}

def Laws.ex_game_to_b_after_deuce():
  {==}

law and_swap_inside_decide:
  for p: Bool
  for q: Bool
  for r: Bool
  for t: Bool
  {S.Game.decide(Bool.and(p, q), Bool.and(r, t)) == Laws.Rule.pick(Bool.and(q, p), Bool.and(t, r)) : Maybe<S.Side>}

def and_swap_inside_decide(p, q, r, t):
  match p q r t:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

def Laws.L2_game_winner_follows_rule(a, b):
  and_swap_inside_decide(Nat.is_ge(a, Nat.add(b, 2n)), Nat.is_ge(a, 4n), Nat.is_ge(b, Nat.add(a, 2n)), Nat.is_ge(b, 4n))

def Laws.L20_live_point_goes_to_a(a, b, live):
  %Equal.sym(Maybe<S.Side>, S.Game.winner(S.Game{a, b}), None{}, live) : {S.Game.point.go(_, a, b, S.A{}) == S.Game{1n+a, b} : S.Game}
  {==}

def Laws.L20_live_point_goes_to_b(a, b, live):
  %Equal.sym(Maybe<S.Side>, S.Game.winner(S.Game{a, b}), None{}, live) : {S.Game.point.go(_, a, b, S.B{}) == S.Game{a, 1n+b} : S.Game}
  {==}

def Laws.L5_won_game_is_final(g, w, won, s):
  match g:
    case S.Game{+a, +b}:
      %Equal.sym(Maybe<S.Side>, S.Game.winner(S.Game{a, b}), Some{w}, won) : {S.Game.point.go(_, a, b, s) == S.Game{a, b} : S.Game}
      {==}

# ---------------------------------------------------------------------------
# Lemmas for L3 and L4
# ---------------------------------------------------------------------------
# Every deuce-shaped score is "3 plus n" for some n. The five facts below say
# how a player's count compares with her opponent's count plus 2 at those
# scores. They are proven together, by one induction on n, because the laws
# take n as use-once: one call to this lemma gives all five at once.

def DeuceFacts(-n: Nat) -> Type:
  {Nat.cmp(n, Nat.add(n, 2n)) == LT{} : Cmp}
  & {Nat.cmp(1n+n, Nat.add(n, 2n)) == LT{} : Cmp}
  & {Nat.cmp(2n+n, Nat.add(n, 2n)) == EQ{} : Cmp}
  & {Nat.cmp(n, 1n+Nat.add(n, 2n)) == LT{} : Cmp}
  & {Nat.cmp(n, 2n+Nat.add(n, 2n)) == LT{} : Cmp}

law deuce_comparisons:
  for n: Nat
  DeuceFacts(n)

def deuce_comparisons(n):
  match n:
    case 0n:
      ({==}, {==}, {==}, {==}, {==})
    case 1n+p:
      deuce_comparisons(p)

# Deuce (3+n all): nobody has won.
law won_at_deuce:
  for -n: Nat
  for c: {Nat.cmp(n, Nat.add(n, 2n)) == LT{} : Cmp}
  {S.Game.won_by(3n+n, 3n+n) == False{} : Bool}

def won_at_deuce(n, c):
  %Equal.sym(Cmp, Nat.cmp(n, Nat.add(n, 2n)), LT{}, c) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(3n+n, 4n)) == False{} : Bool}
  {==}

# Advantage (4+n to 3+n): the leader has not won yet.
law won_at_advantage:
  for -n: Nat
  for c: {Nat.cmp(1n+n, Nat.add(n, 2n)) == LT{} : Cmp}
  {S.Game.won_by(4n+n, 3n+n) == False{} : Bool}

def won_at_advantage(n, c):
  %Equal.sym(Cmp, Nat.cmp(1n+n, Nat.add(n, 2n)), LT{}, c) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(4n+n, 4n)) == False{} : Bool}
  {==}

# Two clear after deuce (5+n to 3+n): the leader has won.
law won_two_clear:
  for -n: Nat
  for c: {Nat.cmp(2n+n, Nat.add(n, 2n)) == EQ{} : Cmp}
  {S.Game.won_by(5n+n, 3n+n) == True{} : Bool}

def won_two_clear(n, c):
  %Equal.sym(Cmp, Nat.cmp(2n+n, Nat.add(n, 2n)), EQ{}, c) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(5n+n, 4n)) == True{} : Bool}
  {==}

# Behind at advantage (3+n to 4+n): the trailer has not won.
law won_behind_advantage:
  for -n: Nat
  for c: {Nat.cmp(n, 1n+Nat.add(n, 2n)) == LT{} : Cmp}
  {S.Game.won_by(3n+n, 4n+n) == False{} : Bool}

def won_behind_advantage(n, c):
  %Equal.sym(Cmp, Nat.cmp(n, 1n+Nat.add(n, 2n)), LT{}, c) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(3n+n, 4n)) == False{} : Bool}
  {==}

# Two behind after deuce (3+n to 5+n): the trailer has not won.
law won_two_behind:
  for -n: Nat
  for c: {Nat.cmp(n, 2n+Nat.add(n, 2n)) == LT{} : Cmp}
  {S.Game.won_by(3n+n, 5n+n) == False{} : Bool}

def won_two_behind(n, c):
  %Equal.sym(Cmp, Nat.cmp(n, 2n+Nat.add(n, 2n)), LT{}, c) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(3n+n, 4n)) == False{} : Bool}
  {==}

# ---------------------------------------------------------------------------
# L3 and L4
# ---------------------------------------------------------------------------
# Each proof replaces every won_by(...) in the goal with True or False, using
# the lemmas above; the goal then computes to both sides being equal.

law L3_deuce_is_not_over.from_facts:
  for -n: Nat
  for facts: DeuceFacts(n)
  {S.Game.winner(S.Game{3n+n, 3n+n}) == None{} : Maybe<S.Side>}

def L3_deuce_is_not_over.from_facts(n, facts):
  match facts:
    case (c_tie, _, _, _, _):
    %Equal.sym(Bool, S.Game.won_by(3n+n, 3n+n), False{}, won_at_deuce(n, c_tie)) : {S.Game.decide(_, _) == None{} : Maybe<S.Side>}
    {==}

def Laws.L3_deuce_is_not_over(n):
  L3_deuce_is_not_over.from_facts(n, deuce_comparisons(n))

# Advantage A (4+n to 3+n) is live, so A's point counts: 5+n to 3+n, a game.
law L4_advantage_a_converted.from_facts:
  for -n: Nat
  for facts: DeuceFacts(n)
  {S.Game.winner(S.Game.point(S.Game{4n+n, 3n+n}, S.A{})) == Some{S.A{}} : Maybe<S.Side>}

def L4_advantage_a_converted.from_facts(n, facts):
  match facts:
    case (_, c_adv, c_clear, c_behind, _):
    %Equal.sym(Bool, S.Game.won_by(4n+n, 3n+n), False{}, won_at_advantage(n, c_adv)) : {S.Game.winner(S.Game.point.go(S.Game.decide(_, S.Game.won_by(3n+n, 4n+n)), 4n+n, 3n+n, S.A{})) == Some{S.A{}} : Maybe<S.Side>}
    %Equal.sym(Bool, S.Game.won_by(3n+n, 4n+n), False{}, won_behind_advantage(n, c_behind)) : {S.Game.winner(S.Game.point.go(S.Game.decide(False{}, _), 4n+n, 3n+n, S.A{})) == Some{S.A{}} : Maybe<S.Side>}
    %Equal.sym(Bool, S.Game.won_by(5n+n, 3n+n), True{}, won_two_clear(n, c_clear)) : {S.Game.decide(_, S.Game.won_by(3n+n, 5n+n)) == Some{S.A{}} : Maybe<S.Side>}
    {==}

def Laws.L4_advantage_a_converted(n):
  L4_advantage_a_converted.from_facts(n, deuce_comparisons(n))

# Advantage A is live, so B's point counts: 4+n all, deuce again.
law L4_advantage_a_lost.from_facts:
  for -n: Nat
  for facts: DeuceFacts(n)
  {S.Game.point(S.Game{4n+n, 3n+n}, S.B{}) == S.Game{4n+n, 4n+n} : S.Game}

def L4_advantage_a_lost.from_facts(n, facts):
  match facts:
    case (_, c_adv, _, c_behind, _):
    %Equal.sym(Bool, S.Game.won_by(4n+n, 3n+n), False{}, won_at_advantage(n, c_adv)) : {S.Game.point.go(S.Game.decide(_, S.Game.won_by(3n+n, 4n+n)), 4n+n, 3n+n, S.B{}) == S.Game{4n+n, 4n+n} : S.Game}
    %Equal.sym(Bool, S.Game.won_by(3n+n, 4n+n), False{}, won_behind_advantage(n, c_behind)) : {S.Game.point.go(S.Game.decide(False{}, _), 4n+n, 3n+n, S.B{}) == S.Game{4n+n, 4n+n} : S.Game}
    {==}

def Laws.L4_advantage_a_lost(n):
  L4_advantage_a_lost.from_facts(n, deuce_comparisons(n))

# Advantage B (3+n to 4+n) is live, so B's point counts: 3+n to 5+n, a game.
law L4_advantage_b_converted.from_facts:
  for -n: Nat
  for facts: DeuceFacts(n)
  {S.Game.winner(S.Game.point(S.Game{3n+n, 4n+n}, S.B{})) == Some{S.B{}} : Maybe<S.Side>}

def L4_advantage_b_converted.from_facts(n, facts):
  match facts:
    case (_, c_adv, c_clear, c_behind, c_two_behind):
    %Equal.sym(Bool, S.Game.won_by(3n+n, 4n+n), False{}, won_behind_advantage(n, c_behind)) : {S.Game.winner(S.Game.point.go(S.Game.decide(_, S.Game.won_by(4n+n, 3n+n)), 3n+n, 4n+n, S.B{})) == Some{S.B{}} : Maybe<S.Side>}
    %Equal.sym(Bool, S.Game.won_by(4n+n, 3n+n), False{}, won_at_advantage(n, c_adv)) : {S.Game.winner(S.Game.point.go(S.Game.decide(False{}, _), 3n+n, 4n+n, S.B{})) == Some{S.B{}} : Maybe<S.Side>}
    %Equal.sym(Bool, S.Game.won_by(3n+n, 5n+n), False{}, won_two_behind(n, c_two_behind)) : {S.Game.decide(_, S.Game.won_by(5n+n, 3n+n)) == Some{S.B{}} : Maybe<S.Side>}
    %Equal.sym(Bool, S.Game.won_by(5n+n, 3n+n), True{}, won_two_clear(n, c_clear)) : {S.Game.decide(False{}, _) == Some{S.B{}} : Maybe<S.Side>}
    {==}

def Laws.L4_advantage_b_converted(n):
  L4_advantage_b_converted.from_facts(n, deuce_comparisons(n))

# Advantage B is live, so A's point counts: 4+n all, deuce again.
law L4_advantage_b_lost.from_facts:
  for -n: Nat
  for facts: DeuceFacts(n)
  {S.Game.point(S.Game{3n+n, 4n+n}, S.A{}) == S.Game{4n+n, 4n+n} : S.Game}

def L4_advantage_b_lost.from_facts(n, facts):
  match facts:
    case (_, c_adv, _, c_behind, _):
    %Equal.sym(Bool, S.Game.won_by(3n+n, 4n+n), False{}, won_behind_advantage(n, c_behind)) : {S.Game.point.go(S.Game.decide(_, S.Game.won_by(4n+n, 3n+n)), 3n+n, 4n+n, S.A{}) == S.Game{4n+n, 4n+n} : S.Game}
    %Equal.sym(Bool, S.Game.won_by(4n+n, 3n+n), False{}, won_at_advantage(n, c_adv)) : {S.Game.point.go(S.Game.decide(False{}, _), 3n+n, 4n+n, S.A{}) == S.Game{4n+n, 4n+n} : S.Game}
    {==}
    

def Laws.L4_advantage_b_lost(n):
  L4_advantage_b_lost.from_facts(n, deuce_comparisons(n))
# ===========================================================================
# MILESTONE 3: tiebreak, set and match
# ===========================================================================

# ---------------------------------------------------------------------------
# General helpers
# ---------------------------------------------------------------------------

# From an impossible situation (a value of the empty type), anything follows.
law ex_falso:
  for -T: Type
  for e: Empty
  T

def ex_falso(T, e):
  match e:

# Some{...} is never None{}: Disc.some is Unit on None and Empty on Some, so
# a proof that None equals Some would turn Unit into Empty.
def Disc.some(m: Maybe<S.Side>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

law none_is_not_some:
  for -w: S.Side
  for h: {None{} == Some{w} : Maybe<S.Side>}
  Empty

def none_is_not_some(w, h):
  %h : Disc.some(_)
  Unit{}

# Some{x} equals Some{w} only when x equals w.
law some_injective:
  for -x: S.Side
  for -w: S.Side
  for h: {Some{x} == Some{w} : Maybe<S.Side>}
  {x == w : S.Side}

def some_injective(x, w, h):
  Equal.cong(Maybe<S.Side>, S.Side, m => Maybe.default(&1, S.Side, m, S.A{}), Some{x}, Some{w}, h)

# The engine's Game.decide and the spec's Rule.pick agree on every input.
law decide_is_pick:
  for p: Bool
  for q: Bool
  {S.Game.decide(p, q) == Laws.Rule.pick(p, q) : Maybe<S.Side>}

def decide_is_pick(p, q):
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Comparisons with n + 2, for every n.
law cmp_n_lt_n2:
  for n: Nat
  {Nat.cmp(n, Nat.add(n, 2n)) == LT{} : Cmp}

def cmp_n_lt_n2(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_n_lt_n2(p)

law cmp_n1_lt_n2:
  for n: Nat
  {Nat.cmp(1n+n, Nat.add(n, 2n)) == LT{} : Cmp}

def cmp_n1_lt_n2(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_n1_lt_n2(p)

law cmp_n2_eq_n2:
  for n: Nat
  {Nat.cmp(2n+n, Nat.add(n, 2n)) == EQ{} : Cmp}

def cmp_n2_eq_n2(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_n2_eq_n2(p)

law cmp_n_lt_n3:
  for n: Nat
  {Nat.cmp(n, 1n+Nat.add(n, 2n)) == LT{} : Cmp}

def cmp_n_lt_n3(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_n_lt_n3(p)

law cmp_n_lt_n4:
  for n: Nat
  {Nat.cmp(n, 2n+Nat.add(n, 2n)) == LT{} : Cmp}

def cmp_n_lt_n4(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_n_lt_n4(p)

# u + n is at least u.
law add_is_ge:
  for u: Nat
  for +n: Nat
  {Cmp.is_ge(Nat.cmp(Nat.add(u, n), u)) == True{} : Bool}

def add_is_ge(u, n):
  match u:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case 1n+v:
      add_is_ge(v, n)

# ---------------------------------------------------------------------------
# Tiebreak: examples
# ---------------------------------------------------------------------------

def Laws.ex_tiebreak_7_5_is_won():
  {==}

def Laws.ex_tiebreak_7_6_is_not_over():
  {==}

def Laws.ex_ten_point_tiebreak_won_10_8():
  {==}

def Laws.ex_tiebreak_serve_pattern():
  {==}

# ---------------------------------------------------------------------------
# Tiebreak: who has won at level and one-point-lead scores
# ---------------------------------------------------------------------------

# Level (k all): nobody has won.
law tb_won_level:
  for -target: Nat
  for +k: Nat
  {S.Tiebreak.won_by(target, k, k) == False{} : Bool}

def tb_won_level(target, k):
  %Equal.sym(Cmp, Nat.cmp(k, Nat.add(k, 2n)), LT{}, cmp_n_lt_n2(k)) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(k, target)) == False{} : Bool}
  {==}

# One ahead (1+k to k): the leader has not won yet.
law tb_won_lead1:
  for -target: Nat
  for +k: Nat
  {S.Tiebreak.won_by(target, 1n+k, k) == False{} : Bool}

def tb_won_lead1(target, k):
  %Equal.sym(Cmp, Nat.cmp(1n+k, Nat.add(k, 2n)), LT{}, cmp_n1_lt_n2(k)) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(1n+k, target)) == False{} : Bool}
  {==}

# One behind (k to 1+k): the trailer has not won.
law tb_won_trail1:
  for -target: Nat
  for +k: Nat
  {S.Tiebreak.won_by(target, k, 1n+k) == False{} : Bool}

def tb_won_trail1(target, k):
  %Equal.sym(Cmp, Nat.cmp(k, 1n+Nat.add(k, 2n)), LT{}, cmp_n_lt_n3(k)) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(k, target)) == False{} : Bool}
  {==}

# Two behind (k to 2+k): the trailer has not won.
law tb_won_trail2:
  for -target: Nat
  for +k: Nat
  {S.Tiebreak.won_by(target, k, 2n+k) == False{} : Bool}

def tb_won_trail2(target, k):
  %Equal.sym(Cmp, Nat.cmp(k, 2n+Nat.add(k, 2n)), LT{}, cmp_n_lt_n4(k)) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(k, target)) == False{} : Bool}
  {==}

# Two ahead with at least the target (2+u+n to u+n, target 2+u): won.
law tb_won_lead2:
  for +u: Nat
  for +n: Nat
  {S.Tiebreak.won_by(2n+u, 2n+Nat.add(u, n), Nat.add(u, n)) == True{} : Bool}

def tb_won_lead2(u, n):
  %Equal.sym(Cmp, Nat.cmp(2n+Nat.add(u, n), Nat.add(Nat.add(u, n), 2n)), EQ{}, cmp_n2_eq_n2(Nat.add(u, n))) : {Bool.and(Cmp.is_ge(_), Nat.is_ge(2n+Nat.add(u, n), 2n+u)) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_ge(Nat.cmp(Nat.add(u, n), u)), True{}, add_is_ge(u, n)) : {_ == True{} : Bool}
  {==}

# ---------------------------------------------------------------------------
# Tiebreak: L6, L7, L21
# ---------------------------------------------------------------------------

def Laws.L6_tiebreak_winner_follows_rule(target, a, b):
  and_swap_inside_decide(Nat.is_ge(a, Nat.add(b, 2n)), Nat.is_ge(a, target), Nat.is_ge(b, Nat.add(a, 2n)), Nat.is_ge(b, target))

def Laws.L7_level_tiebreak_is_not_over(target, n):
  %Equal.sym(Bool, S.Tiebreak.won_by(target, n, n), False{}, tb_won_level(target, n)) : {S.Game.decide(_, _) == None{} : Maybe<S.Side>}
  {==}

def Laws.L7_lead_a_converted(u, n):
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, 1n+Nat.add(u, n), Nat.add(u, n)), False{}, tb_won_lead1(2n+u, Nat.add(u, n))) : {S.Tiebreak.winner(2n+u, S.Tiebreak.point.go(S.Game.decide(_, S.Tiebreak.won_by(2n+u, Nat.add(u, n), 1n+Nat.add(u, n))), 1n+Nat.add(u, n), Nat.add(u, n), S.A{})) == Some{S.A{}} : Maybe<S.Side>}
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, Nat.add(u, n), 1n+Nat.add(u, n)), False{}, tb_won_trail1(2n+u, Nat.add(u, n))) : {S.Tiebreak.winner(2n+u, S.Tiebreak.point.go(S.Game.decide(False{}, _), 1n+Nat.add(u, n), Nat.add(u, n), S.A{})) == Some{S.A{}} : Maybe<S.Side>}
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, 2n+Nat.add(u, n), Nat.add(u, n)), True{}, tb_won_lead2(u, n)) : {S.Game.decide(_, S.Tiebreak.won_by(2n+u, Nat.add(u, n), 2n+Nat.add(u, n))) == Some{S.A{}} : Maybe<S.Side>}
  {==}

def Laws.L7_lead_a_levelled(u, n):
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, 1n+Nat.add(u, n), Nat.add(u, n)), False{}, tb_won_lead1(2n+u, Nat.add(u, n))) : {S.Tiebreak.point.go(S.Game.decide(_, S.Tiebreak.won_by(2n+u, Nat.add(u, n), 1n+Nat.add(u, n))), 1n+Nat.add(u, n), Nat.add(u, n), S.B{}) == S.Tiebreak{1n+Nat.add(u, n), 1n+Nat.add(u, n)} : S.Tiebreak}
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, Nat.add(u, n), 1n+Nat.add(u, n)), False{}, tb_won_trail1(2n+u, Nat.add(u, n))) : {S.Tiebreak.point.go(S.Game.decide(False{}, _), 1n+Nat.add(u, n), Nat.add(u, n), S.B{}) == S.Tiebreak{1n+Nat.add(u, n), 1n+Nat.add(u, n)} : S.Tiebreak}
  {==}

def Laws.L7_lead_b_converted(u, n):
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, Nat.add(u, n), 1n+Nat.add(u, n)), False{}, tb_won_trail1(2n+u, Nat.add(u, n))) : {S.Tiebreak.winner(2n+u, S.Tiebreak.point.go(S.Game.decide(_, S.Tiebreak.won_by(2n+u, 1n+Nat.add(u, n), Nat.add(u, n))), Nat.add(u, n), 1n+Nat.add(u, n), S.B{})) == Some{S.B{}} : Maybe<S.Side>}
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, 1n+Nat.add(u, n), Nat.add(u, n)), False{}, tb_won_lead1(2n+u, Nat.add(u, n))) : {S.Tiebreak.winner(2n+u, S.Tiebreak.point.go(S.Game.decide(False{}, _), Nat.add(u, n), 1n+Nat.add(u, n), S.B{})) == Some{S.B{}} : Maybe<S.Side>}
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, Nat.add(u, n), 2n+Nat.add(u, n)), False{}, tb_won_trail2(2n+u, Nat.add(u, n))) : {S.Game.decide(_, S.Tiebreak.won_by(2n+u, 2n+Nat.add(u, n), Nat.add(u, n))) == Some{S.B{}} : Maybe<S.Side>}
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, 2n+Nat.add(u, n), Nat.add(u, n)), True{}, tb_won_lead2(u, n)) : {S.Game.decide(False{}, _) == Some{S.B{}} : Maybe<S.Side>}
  {==}

def Laws.L7_lead_b_levelled(u, n):
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, Nat.add(u, n), 1n+Nat.add(u, n)), False{}, tb_won_trail1(2n+u, Nat.add(u, n))) : {S.Tiebreak.point.go(S.Game.decide(_, S.Tiebreak.won_by(2n+u, 1n+Nat.add(u, n), Nat.add(u, n))), Nat.add(u, n), 1n+Nat.add(u, n), S.A{}) == S.Tiebreak{1n+Nat.add(u, n), 1n+Nat.add(u, n)} : S.Tiebreak}
  %Equal.sym(Bool, S.Tiebreak.won_by(2n+u, 1n+Nat.add(u, n), Nat.add(u, n)), False{}, tb_won_lead1(2n+u, Nat.add(u, n))) : {S.Tiebreak.point.go(S.Game.decide(False{}, _), Nat.add(u, n), 1n+Nat.add(u, n), S.A{}) == S.Tiebreak{1n+Nat.add(u, n), 1n+Nat.add(u, n)} : S.Tiebreak}
  {==}

def Laws.L21_live_tiebreak_point_goes_to_a(target, a, b, live):
  %Equal.sym(Maybe<S.Side>, S.Tiebreak.winner(target, S.Tiebreak{a, b}), None{}, live) : {S.Tiebreak.point.go(_, a, b, S.A{}) == S.Tiebreak{1n+a, b} : S.Tiebreak}
  {==}

def Laws.L21_live_tiebreak_point_goes_to_b(target, a, b, live):
  %Equal.sym(Maybe<S.Side>, S.Tiebreak.winner(target, S.Tiebreak{a, b}), None{}, live) : {S.Tiebreak.point.go(_, a, b, S.B{}) == S.Tiebreak{a, 1n+b} : S.Tiebreak}
  {==}

def Laws.L21_won_tiebreak_is_final(target, t, w, won, s):
  match t:
    case S.Tiebreak{+a, +b}:
      %Equal.sym(Maybe<S.Side>, S.Tiebreak.winner(target, S.Tiebreak{a, b}), Some{w}, won) : {S.Tiebreak.point.go(_, a, b, s) == S.Tiebreak{a, b} : S.Tiebreak}
      {==}

# ---------------------------------------------------------------------------
# Tiebreak serving: L8
# ---------------------------------------------------------------------------

# After an even number of points the serving pair is complete, so whether the
# current server "has one more" makes no difference.
law tb_server_even_more:
  for n: Nat
  for +x: S.Side
  {S.Tiebreak.server.go(Nat.double(n), x, True{}) == S.Tiebreak.server.go(Nat.double(n), x, False{}) : S.Side}

def tb_server_even_more(n, x):
  match n:
    case 0n:
      {==}
    case 1n+m:
      tb_server_even_more(m, S.Side.other(x))

# One point past an even number, the serve has changed.
law tb_server_odd_changes:
  for n: Nat
  for +x: S.Side
  {S.Tiebreak.server.go(1n+Nat.double(n), x, False{}) == S.Side.other(S.Tiebreak.server.go(Nat.double(n), x, False{})) : S.Side}

def tb_server_odd_changes(n, x):
  match n:
    case 0n:
      {==}
    case 1n+m:
      tb_server_odd_changes(m, S.Side.other(x))

def Laws.L8_tiebreak_first_point(first):
  {==}

# The engine's Side.other and the spec's Rule.other agree.
law other_same:
  for x: S.Side
  {S.Side.other(x) == Laws.Rule.other(x) : S.Side}

def other_same(x):
  match x:
    case S.A{}:
      {==}
    case S.B{}:
      {==}

def Laws.L8_tiebreak_serve_changes(first, n):
  Equal.trans(S.Side, S.Tiebreak.server.go(1n+Nat.double(n), first, False{}), S.Side.other(S.Tiebreak.server.go(Nat.double(n), first, False{})), Laws.Rule.other(S.Tiebreak.server.go(Nat.double(n), first, False{})), tb_server_odd_changes(n, first), other_same(S.Tiebreak.server.go(Nat.double(n), first, False{})))

def Laws.L8_tiebreak_serve_stays(first, n):
  Equal.sym(S.Side, S.Tiebreak.server.go(Nat.double(n), S.Side.other(first), True{}), S.Tiebreak.server.go(Nat.double(n), S.Side.other(first), False{}), tb_server_even_more(n, S.Side.other(first)))

# ---------------------------------------------------------------------------
# Set: examples, L24, L22
# ---------------------------------------------------------------------------

def Laws.ex_set_6_4_is_won():
  {==}

def Laws.ex_set_6_5_is_not_over():
  {==}

def Laws.ex_set_7_5_is_won():
  {==}

def Laws.ex_set_6_7_is_won_by_b():
  {==}

def Laws.L24_set_winner_follows_rule(a, b, play):
  decide_is_pick(S.TennisSet.won_by(6n, a, b), S.TennisSet.won_by(6n, b, a))

# The engine's choice of what comes next agrees with the spec's.
law next_play_same:
  for p: Bool
  {S.TennisSet.next_play(p) == Laws.Rule.next_play(p) : S.Play}

def next_play_same(p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# Adding a game: the engine agrees with the spec's Rule.after_game.
law add_game_is_after_game:
  for x: S.Side
  for +a: Nat
  for +b: Nat
  {S.TennisSet.add_game(6n, x, a, b) == Laws.Rule.after_game(x, a, b) : S.TennisSet}

def add_game_is_after_game(x, a, b):
  match x:
    case S.A{}:
      %next_play_same(Bool.and(Nat.is_eq(1n+a, 6n), Nat.is_eq(b, 6n))) : {S.TennisSet{1n+a, b, S.TennisSet.next_play(Bool.and(Nat.is_eq(1n+a, 6n), Nat.is_eq(b, 6n)))} == S.TennisSet{1n+a, b, _} : S.TennisSet}
      {==}
    case S.B{}:
      %next_play_same(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(1n+b, 6n))) : {S.TennisSet{a, 1n+b, S.TennisSet.next_play(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(1n+b, 6n)))} == S.TennisSet{a, 1n+b, _} : S.TennisSet}
      {==}

# When the game just played has a winner w, the set adds a game to w. The
# proof looks at the winner the engine computed (m), and uses the assumption
# m == Some{w} to show it is w.
law game_done_some:
  for -w: S.Side
  for m: Maybe<S.Side>
  for h: {m == Some{w} : Maybe<S.Side>}
  for +a: Nat
  for +b: Nat
  for g: S.Game
  {S.TennisSet.game_done(m, 6n, a, b, g) == Laws.Rule.after_game(w, a, b) : S.TennisSet}

def game_done_some(w, m, h, a, b, g):
  match m:
    case None{}:
      ex_falso({S.TennisSet.game_done(None{}, 6n, a, b, g) == Laws.Rule.after_game(w, a, b) : S.TennisSet}, none_is_not_some(w, h))
    case Some{x}:
      %some_injective(x, w, h) : {S.TennisSet.add_game(6n, x, a, b) == Laws.Rule.after_game(_, a, b) : S.TennisSet}
      add_game_is_after_game(x, a, b)

# The same for a tiebreak.
law tiebreak_done_some:
  for -w: S.Side
  for m: Maybe<S.Side>
  for h: {m == Some{w} : Maybe<S.Side>}
  for +a: Nat
  for +b: Nat
  for t: S.Tiebreak
  {S.TennisSet.tiebreak_done(m, 6n, a, b, t) == Laws.Rule.after_game(w, a, b) : S.TennisSet}

def tiebreak_done_some(w, m, h, a, b, t):
  match m:
    case None{}:
      ex_falso({S.TennisSet.tiebreak_done(None{}, 6n, a, b, t) == Laws.Rule.after_game(w, a, b) : S.TennisSet}, none_is_not_some(w, h))
    case Some{x}:
      %some_injective(x, w, h) : {S.TennisSet.add_game(6n, x, a, b) == Laws.Rule.after_game(_, a, b) : S.TennisSet}
      add_game_is_after_game(x, a, b)

def Laws.L22_point_goes_into_game(target, a, b, g, s, live, game_goes_on):
  %Equal.sym(Maybe<S.Side>, S.TennisSet.winner(6n, S.TennisSet{a, b, S.InGame{g}}), None{}, live) : {S.TennisSet.point.go(_, 6n, target, a, b, S.InGame{g}, s) == S.TennisSet{a, b, S.InGame{S.Game.point(g, s)}} : S.TennisSet}
  %Equal.sym(Maybe<S.Side>, S.Game.winner(S.Game.point(g, s)), None{}, game_goes_on) : {S.TennisSet.game_done(_, 6n, a, b, S.Game.point(g, s)) == S.TennisSet{a, b, S.InGame{S.Game.point(g, s)}} : S.TennisSet}
  {==}

def Laws.L22_won_game_adds_a_game(target, a, b, g, s, w, live, game_won):
  %Equal.sym(Maybe<S.Side>, S.TennisSet.winner(6n, S.TennisSet{a, b, S.InGame{g}}), None{}, live) : {S.TennisSet.point.go(_, 6n, target, a, b, S.InGame{g}, s) == Laws.Rule.after_game(w, a, b) : S.TennisSet}
  game_done_some(w, S.Game.winner(S.Game.point(g, s)), game_won, a, b, S.Game.point(g, s))

def Laws.L22_point_goes_into_tiebreak(target, a, b, t, s, live, tiebreak_goes_on):
  %Equal.sym(Maybe<S.Side>, S.TennisSet.winner(6n, S.TennisSet{a, b, S.InTiebreak{t}}), None{}, live) : {S.TennisSet.point.go(_, 6n, target, a, b, S.InTiebreak{t}, s) == S.TennisSet{a, b, S.InTiebreak{S.Tiebreak.point(target, t, s)}} : S.TennisSet}
  %Equal.sym(Maybe<S.Side>, S.Tiebreak.winner(target, S.Tiebreak.point(target, t, s)), None{}, tiebreak_goes_on) : {S.TennisSet.tiebreak_done(_, 6n, a, b, S.Tiebreak.point(target, t, s)) == S.TennisSet{a, b, S.InTiebreak{S.Tiebreak.point(target, t, s)}} : S.TennisSet}
  {==}

def Laws.L22_won_tiebreak_adds_a_game(target, a, b, t, s, w, live, tiebreak_won):
  %Equal.sym(Maybe<S.Side>, S.TennisSet.winner(6n, S.TennisSet{a, b, S.InTiebreak{t}}), None{}, live) : {S.TennisSet.point.go(_, 6n, target, a, b, S.InTiebreak{t}, s) == Laws.Rule.after_game(w, a, b) : S.TennisSet}
  tiebreak_done_some(w, S.Tiebreak.winner(target, S.Tiebreak.point(target, t, s)), tiebreak_won, a, b, S.Tiebreak.point(target, t, s))

def Laws.L22_won_set_is_final(target, st, w, won, s):
  match st:
    case S.TennisSet{+a, +b, +play}:
      %Equal.sym(Maybe<S.Side>, S.TennisSet.winner(6n, S.TennisSet{a, b, play}), Some{w}, won) : {S.TennisSet.point.go(_, 6n, target, a, b, play, s) == S.TennisSet{a, b, play} : S.TennisSet}
      {==}

# ---------------------------------------------------------------------------
# Match: examples
# ---------------------------------------------------------------------------

def Laws.ex_one_set_all_is_not_over():
  {==}

def Laws.ex_won_in_three_sets():
  {==}

def Laws.ex_a_serves_game_1():
  {==}

def Laws.ex_b_serves_game_6():
  {==}

def Laws.ex_a_starts_the_tiebreak():
  {==}

def Laws.ex_b_serves_tiebreak_point_2():
  {==}

def Laws.ex_b_serves_after_tiebreak_set():
  {==}

def Laws.ex_a_serves_after_6_4_set():
  {==}

# ---------------------------------------------------------------------------
# Match: the engine's helpers agree with the spec's
# ---------------------------------------------------------------------------

law same_same:
  for x: S.Side
  for y: S.Side
  {S.Match.same(x, y) == Laws.Rule.same(x, y) : Bool}

def same_same(x, y):
  match x y:
    case S.A{} S.A{}:
      {==}
    case S.A{} S.B{}:
      {==}
    case S.B{} S.A{}:
      {==}
    case S.B{} S.B{}:
      {==}

law count_same:
  for h: Bool
  for n: Nat
  {S.Match.count(h, n) == Laws.Rule.count(h, n) : Nat}

def count_same(h, n):
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

law side_if_same:
  for p: Bool
  {S.Match.side_if(p) == Laws.Rule.side_if(p) : S.Side}

def side_if_same(p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

law choose_same:
  for c: Bool
  for yes: Nat
  for no: Nat
  {S.Match.choose(c, yes, no) == Laws.Rule.choose(c, yes, no) : Nat}

def choose_same(c, yes, no):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law score_winner_same:
  for sc: S.Score
  {S.Match.score_winner(sc) == Laws.Rule.score_winner(sc) : S.Side}

def score_winner_same(sc):
  match sc:
    case S.Score{+a, +b}:
      side_if_same(Nat.is_gt(a, b))

law score_of_same:
  for st: S.TennisSet
  {S.Match.score_of(st) == Laws.Rule.score_of(st) : S.Score}

def score_of_same(st):
  match st:
    case S.TennisSet{a, b, play}:
      {==}

# Counting sets won: by induction on the list of finished sets.
law sets_won_same:
  for +w: S.Side
  for done: List<&2, S.Score>
  {S.Match.sets_won(w, done) == Laws.Rule.sets_won(w, done) : Nat}

def sets_won_same(w, done):
  match done:
    case Nil{}:
      {==}
    case Con{+sc, +rest}:
      %sets_won_same(w, rest) : {S.Match.count(S.Match.same(S.Match.score_winner(sc), w), S.Match.sets_won(w, rest)) == Laws.Rule.count(Laws.Rule.same(Laws.Rule.score_winner(sc), w), _) : Nat}
      %score_winner_same(sc) : {S.Match.count(S.Match.same(S.Match.score_winner(sc), w), S.Match.sets_won(w, rest)) == Laws.Rule.count(Laws.Rule.same(_, w), S.Match.sets_won(w, rest)) : Nat}
      %same_same(S.Match.score_winner(sc), w) : {S.Match.count(S.Match.same(S.Match.score_winner(sc), w), S.Match.sets_won(w, rest)) == Laws.Rule.count(_, S.Match.sets_won(w, rest)) : Nat}
      count_same(S.Match.same(S.Match.score_winner(sc), w), S.Match.sets_won(w, rest))

law games_same:
  for fmt: S.Format
  {S.Match.games(fmt) == Laws.Rule.games_of(fmt) : Nat}

def games_same(fmt):
  match fmt:
    case S.Format{g, t, n, ft}:
      {==}

law tiebreak_target_same:
  for fmt: S.Format
  for +done: List<&2, S.Score>
  {S.Match.tiebreak_target(fmt, done) == Laws.Rule.tiebreak_target(fmt, done) : Nat}

def tiebreak_target_same(fmt, done):
  match fmt:
    case S.Format{g, +t, +n, +ft}:
      %sets_won_same(S.A{}, done) : {S.Match.choose(Bool.and(Nat.is_eq(S.Match.sets_won(S.A{}, done), Nat.sub(n, 1n)), Nat.is_eq(S.Match.sets_won(S.B{}, done), Nat.sub(n, 1n))), ft, t) == Laws.Rule.choose(Bool.and(Nat.is_eq(_, Nat.sub(n, 1n)), Nat.is_eq(Laws.Rule.sets_won(S.B{}, done), Nat.sub(n, 1n))), ft, t) : Nat}
      %sets_won_same(S.B{}, done) : {S.Match.choose(Bool.and(Nat.is_eq(S.Match.sets_won(S.A{}, done), Nat.sub(n, 1n)), Nat.is_eq(S.Match.sets_won(S.B{}, done), Nat.sub(n, 1n))), ft, t) == Laws.Rule.choose(Bool.and(Nat.is_eq(S.Match.sets_won(S.A{}, done), Nat.sub(n, 1n)), Nat.is_eq(_, Nat.sub(n, 1n))), ft, t) : Nat}
      choose_same(Bool.and(Nat.is_eq(S.Match.sets_won(S.A{}, done), Nat.sub(n, 1n)), Nat.is_eq(S.Match.sets_won(S.B{}, done), Nat.sub(n, 1n))), ft, t)

law set_after_same:
  for +fmt: S.Format
  for +done: List<&2, S.Score>
  for +st: S.TennisSet
  for +s: S.Side
  {S.Match.set_after(fmt, done, st, s) == Laws.Rule.set_after(fmt, done, st, s) : S.TennisSet}

def set_after_same(fmt, done, st, s):
  %games_same(fmt) : {S.TennisSet.point(S.Match.games(fmt), S.Match.tiebreak_target(fmt, done), st, s) == S.TennisSet.point(_, Laws.Rule.tiebreak_target(fmt, done), st, s) : S.TennisSet}
  %tiebreak_target_same(fmt, done) : {S.TennisSet.point(S.Match.games(fmt), S.Match.tiebreak_target(fmt, done), st, s) == S.TennisSet.point(S.Match.games(fmt), _, st, s) : S.TennisSet}
  {==}

law alternate_same:
  for n: Nat
  for +first: S.Side
  {S.Match.alternate(n, first) == Laws.Rule.alternate(n, first) : S.Side}

def alternate_same(n, first):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %other_same(first) : {S.Match.alternate(p, S.Side.other(first)) == Laws.Rule.alternate(p, _) : S.Side}
      alternate_same(p, S.Side.other(first))

law games_in_same:
  for done: List<&2, S.Score>
  {S.Match.games_in(done) == Laws.Rule.games_in(done) : Nat}

def games_in_same(done):
  match done:
    case Nil{}:
      {==}
    case Con{sc, rest}:
      match sc:
        case S.Score{+a, +b}:
          %games_in_same(rest) : {Nat.add(Nat.add(a, b), S.Match.games_in(rest)) == Nat.add(Nat.add(a, b), _) : Nat}
          {==}

# Who serves the current game: the engine agrees with the spec.
law game_server_same:
  for +done: List<&2, S.Score>
  for +first: S.Side
  for +k: Nat
  {S.Match.alternate(k, S.Match.alternate(S.Match.games_in(done), first)) == Laws.Rule.alternate(k, Laws.Rule.alternate(Laws.Rule.games_in(done), first)) : S.Side}

def game_server_same(done, first, k):
  %games_in_same(done) : {S.Match.alternate(k, S.Match.alternate(S.Match.games_in(done), first)) == Laws.Rule.alternate(k, Laws.Rule.alternate(_, first)) : S.Side}
  %alternate_same(S.Match.games_in(done), first) : {S.Match.alternate(k, S.Match.alternate(S.Match.games_in(done), first)) == Laws.Rule.alternate(k, _) : S.Side}
  alternate_same(k, S.Match.alternate(S.Match.games_in(done), first))

law server_same:
  for m: S.Match
  {S.Match.server(m) == Laws.Rule.match_server(m) : S.Side}

def server_same(m):
  match m:
    case S.Match{+first, +done, st}:
      match st:
        case S.TennisSet{+a, +b, play}:
          match play:
            case S.InGame{g}:
              game_server_same(done, first, Nat.add(a, b))
            case S.InTiebreak{t}:
              match t:
                case S.Tiebreak{+x, +y}:
                  %game_server_same(done, first, Nat.add(a, b)) : {S.Tiebreak.server(S.Match.alternate(Nat.add(a, b), S.Match.alternate(S.Match.games_in(done), first)), Nat.add(x, y)) == S.Tiebreak.server(_, Nat.add(x, y)) : S.Side}
                  {==}

# ---------------------------------------------------------------------------
# Match: L25, L23, L13, L11
# ---------------------------------------------------------------------------

def Laws.L25_match_winner_follows_rule(fmt, first, done, st):
  match fmt:
    case S.Format{g, t, +n, ft}:
      %sets_won_same(S.A{}, done) : {S.Game.decide(Nat.is_ge(S.Match.sets_won(S.A{}, done), n), Nat.is_ge(S.Match.sets_won(S.B{}, done), n)) == Laws.Rule.pick(Nat.is_ge(_, n), Nat.is_ge(Laws.Rule.sets_won(S.B{}, done), n)) : Maybe<S.Side>}
      %sets_won_same(S.B{}, done) : {S.Game.decide(Nat.is_ge(S.Match.sets_won(S.A{}, done), n), Nat.is_ge(S.Match.sets_won(S.B{}, done), n)) == Laws.Rule.pick(Nat.is_ge(S.Match.sets_won(S.A{}, done), n), Nat.is_ge(_, n)) : Maybe<S.Side>}
      decide_is_pick(Nat.is_ge(S.Match.sets_won(S.A{}, done), n), Nat.is_ge(S.Match.sets_won(S.B{}, done), n))

def Laws.L23_match_starts_at_zero(first):
  {==}

def Laws.L23_point_goes_into_set(fmt, first, done, st, s, live, set_goes_on):
  %Equal.sym(Maybe<S.Side>, S.Match.winner(fmt, S.Match{first, done, st}), None{}, live) : {S.Match.point.go(_, fmt, first, done, st, s) == S.Match{first, done, Laws.Rule.set_after(fmt, done, st, s)} : S.Match}
  %Equal.sym(S.TennisSet, S.Match.set_after(fmt, done, st, s), Laws.Rule.set_after(fmt, done, st, s), set_after_same(fmt, done, st, s)) : {S.Match.set_done(S.TennisSet.winner(S.Match.games(fmt), _), first, done, _) == S.Match{first, done, Laws.Rule.set_after(fmt, done, st, s)} : S.Match}
  %Equal.sym(Nat, S.Match.games(fmt), Laws.Rule.games_of(fmt), games_same(fmt)) : {S.Match.set_done(S.TennisSet.winner(_, Laws.Rule.set_after(fmt, done, st, s)), first, done, Laws.Rule.set_after(fmt, done, st, s)) == S.Match{first, done, Laws.Rule.set_after(fmt, done, st, s)} : S.Match}
  %Equal.sym(Maybe<S.Side>, S.TennisSet.winner(Laws.Rule.games_of(fmt), Laws.Rule.set_after(fmt, done, st, s)), None{}, set_goes_on) : {S.Match.set_done(_, first, done, Laws.Rule.set_after(fmt, done, st, s)) == S.Match{first, done, Laws.Rule.set_after(fmt, done, st, s)} : S.Match}
  {==}

def Laws.L23_won_set_is_recorded(fmt, first, done, st, s, w, live, set_won):
  %Equal.sym(Maybe<S.Side>, S.Match.winner(fmt, S.Match{first, done, st}), None{}, live) : {S.Match.point.go(_, fmt, first, done, st, s) == S.Match{first, Laws.Rule.score_of(Laws.Rule.set_after(fmt, done, st, s)) <> done, Laws.Rule.fresh_set()} : S.Match}
  %Equal.sym(S.TennisSet, S.Match.set_after(fmt, done, st, s), Laws.Rule.set_after(fmt, done, st, s), set_after_same(fmt, done, st, s)) : {S.Match.set_done(S.TennisSet.winner(S.Match.games(fmt), _), first, done, _) == S.Match{first, Laws.Rule.score_of(Laws.Rule.set_after(fmt, done, st, s)) <> done, Laws.Rule.fresh_set()} : S.Match}
  %Equal.sym(Nat, S.Match.games(fmt), Laws.Rule.games_of(fmt), games_same(fmt)) : {S.Match.set_done(S.TennisSet.winner(_, Laws.Rule.set_after(fmt, done, st, s)), first, done, Laws.Rule.set_after(fmt, done, st, s)) == S.Match{first, Laws.Rule.score_of(Laws.Rule.set_after(fmt, done, st, s)) <> done, Laws.Rule.fresh_set()} : S.Match}
  %Equal.sym(Maybe<S.Side>, S.TennisSet.winner(Laws.Rule.games_of(fmt), Laws.Rule.set_after(fmt, done, st, s)), Some{w}, set_won) : {S.Match.set_done(_, first, done, Laws.Rule.set_after(fmt, done, st, s)) == S.Match{first, Laws.Rule.score_of(Laws.Rule.set_after(fmt, done, st, s)) <> done, Laws.Rule.fresh_set()} : S.Match}
  %score_of_same(Laws.Rule.set_after(fmt, done, st, s)) : {S.Match{first, S.Match.score_of(Laws.Rule.set_after(fmt, done, st, s)) <> done, S.Match.fresh_set()} == S.Match{first, _ <> done, Laws.Rule.fresh_set()} : S.Match}
  {==}

def Laws.L13_won_match_is_final(fmt, m, w, won, s):
  match m:
    case S.Match{+first, +done, +st}:
      %Equal.sym(Maybe<S.Side>, S.Match.winner(fmt, S.Match{first, done, st}), Some{w}, won) : {S.Match.point.go(_, fmt, first, done, st, s) == S.Match{first, done, st} : S.Match}
      {==}

def Laws.L11_server_follows_rule(m):
  server_same(m)

# A proof of an equation may be used only once, so this makes two copies.
law dup_eq:
  for -A: Type
  for -x: A
  for -y: A
  for e: {x == y : A}
  {x == y : A} & {x == y : A}

def dup_eq(A, x, y, e):
  %e : {x == _ : A} & {x == _ : A}
  ({==}, {==})

# L11, second law, with "the set is live" available twice: once for the set
# before the point, once for the set after it (same games, so same verdict).
law same_server_within_game_go:
  for +fmt: S.Format
  for +first: S.Side
  for +done: List<&2, S.Score>
  for +a: Nat
  for +b: Nat
  for +g: S.Game
  for +s: S.Side
  for live: {S.Match.winner(fmt, S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}) == None{} : Maybe<S.Side>}
  for set_live2: {S.TennisSet.winner(Laws.Rule.games_of(fmt), S.TennisSet{a, b, S.InGame{g}}) == None{} : Maybe<S.Side>} & {S.TennisSet.winner(Laws.Rule.games_of(fmt), S.TennisSet{a, b, S.InGame{g}}) == None{} : Maybe<S.Side>}
  for game_goes_on: {S.Game.winner(S.Game.point(g, s)) == None{} : Maybe<S.Side>}
  {S.Match.server(S.Match.point(fmt, S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}, s)) == S.Match.server(S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}) : S.Side}

def same_server_within_game_go(fmt, first, done, a, b, g, s, live, set_live2, game_goes_on):
  match fmt:
    case S.Format{+g6, +t, +n, +ft}:
      match set_live2:
        case (e1, e2):
          %Equal.sym(Maybe<S.Side>, S.Match.winner(S.Format{g6, t, n, ft}, S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}), None{}, live) : {S.Match.server(S.Match.point.go(_, S.Format{g6, t, n, ft}, first, done, S.TennisSet{a, b, S.InGame{g}}, s)) == S.Match.server(S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}) : S.Side}
          %Equal.sym(Maybe<S.Side>, S.TennisSet.winner(g6, S.TennisSet{a, b, S.InGame{g}}), None{}, e1) : {S.Match.server(S.Match.set_point(S.Format{g6, t, n, ft}, first, done, S.TennisSet.point.go(_, g6, S.Match.tiebreak_target(S.Format{g6, t, n, ft}, done), a, b, S.InGame{g}, s))) == S.Match.server(S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}) : S.Side}
          %Equal.sym(Maybe<S.Side>, S.Game.winner(S.Game.point(g, s)), None{}, game_goes_on) : {S.Match.server(S.Match.set_point(S.Format{g6, t, n, ft}, first, done, S.TennisSet.game_done(_, g6, a, b, S.Game.point(g, s)))) == S.Match.server(S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}) : S.Side}
          %Equal.sym(Maybe<S.Side>, S.TennisSet.winner(g6, S.TennisSet{a, b, S.InGame{g}}), None{}, e2) : {S.Match.server(S.Match.set_done(_, first, done, S.TennisSet{a, b, S.InGame{S.Game.point(g, s)}})) == S.Match.server(S.Match{first, done, S.TennisSet{a, b, S.InGame{g}}}) : S.Side}
          {==}

def Laws.L11_same_server_within_game(fmt, first, done, a, b, g, s, live, set_live, game_goes_on):
  same_server_within_game_go(fmt, first, done, a, b, g, s, live, dup_eq(Maybe<S.Side>, S.TennisSet.winner(Laws.Rule.games_of(fmt), S.TennisSet{a, b, S.InGame{g}}), None{}, set_live), game_goes_on)

# ---------------------------------------------------------------------------
# Sequences of points (L9, L10, L12): Bool facts
# ---------------------------------------------------------------------------

def Disc.bool(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law false_is_not_true:
  for h: {False{} == True{} : Bool}
  Empty

def false_is_not_true(h):
  %h : Disc.bool(_)
  Unit{}

# If "p implies q" holds and p holds, then q holds.
law impl_elim:
  for p: Bool
  for q: Bool
  for h1: {T.Imp(p, q) == True{} : Bool}
  for h2: {p == True{} : Bool}
  {q == True{} : Bool}

def impl_elim(p, q, h1, h2):
  match p:
    case True{}:
      h1
    case False{}:
      ex_falso({q == True{} : Bool}, false_is_not_true(h2))

law and_intro:
  for p: Bool
  for q: Bool
  for hp: {p == True{} : Bool}
  for hq: {q == True{} : Bool}
  {Bool.and(p, q) == True{} : Bool}

def and_intro(p, q, hp, hq):
  match p:
    case True{}:
      hq
    case False{}:
      ex_falso({Bool.and(False{}, q) == True{} : Bool}, false_is_not_true(hp))

law and_true_r:
  for p: Bool
  for q: Bool
  for h: {Bool.and(p, q) == True{} : Bool}
  {q == True{} : Bool}

def and_true_r(p, q, h):
  match p:
    case True{}:
      h
    case False{}:
      ex_falso({q == True{} : Bool}, false_is_not_true(h))

law booleq_true:
  for p: Bool
  for q: Bool
  for h: {T.BoolEq(p, q) == True{} : Bool}
  {p == q : Bool}

def booleq_true(p, q, h):
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      ex_falso({True{} == False{} : Bool}, false_is_not_true(h))
    case False{} True{}:
      ex_falso({False{} == True{} : Bool}, false_is_not_true(h))
    case False{} False{}:
      {==}

law isnone_of:
  for -m: Maybe<S.Side>
  for e: {m == None{} : Maybe<S.Side>}
  {T.IsNone(m) == True{} : Bool}

def isnone_of(m, e):
  %Equal.sym(Maybe<S.Side>, m, None{}, e) : {T.IsNone(_) == True{} : Bool}
  {==}

law isside_of:
  for -m: Maybe<S.Side>
  for x: S.Side
  for e: {m == Some{x} : Maybe<S.Side>}
  {T.IsSide(m, x) == True{} : Bool}

def isside_of(m, x, e):
  match x:
    case S.A{}:
      %Equal.sym(Maybe<S.Side>, m, Some{S.A{}}, e) : {T.IsSide(_, S.A{}) == True{} : Bool}
      {==}
    case S.B{}:
      %Equal.sym(Maybe<S.Side>, m, Some{S.B{}}, e) : {T.IsSide(_, S.B{}) == True{} : Bool}
      {==}

# ---------------------------------------------------------------------------
# Sets: every point keeps the set invariant (T.SetInv)
# ---------------------------------------------------------------------------

# A live set's invariant, with "nobody has won" plugged in.
law live_ok_of:
  for +a: Nat
  for +b: Nat
  for tb: Bool
  for l: {T.W0(a, b) == None{} : Maybe<S.Side>}
  for inv: {T.SetInv.go(T.W0(a, b), a, b, tb) == True{} : Bool}
  {T.LiveOK(a, b, tb) == True{} : Bool}

def live_ok_of(a, b, tb, l, inv):
  %l : {T.SetInv.go(_, a, b, tb) == True{} : Bool}
  inv

law add_step_go:
  for +x: S.Side
  for +tb: Bool
  for +a: Nat
  for +b: Nat
  for live2: {T.W0(a, b) == None{} : Maybe<S.Side>} & {T.W0(a, b) == None{} : Maybe<S.Side>}
  for inv: {T.SetInv.go(T.W0(a, b), a, b, tb) == True{} : Bool}
  {T.SetInv(S.TennisSet.add_game(6n, x, a, b)) == True{} : Bool}

def add_step_go(x, tb, a, b, live2, inv):
  match live2:
    case (l1, l2):
      impl_elim(Bool.and(T.LiveOK(a, b, tb), T.IsNone(T.W0(a, b))), T.SetInv(S.TennisSet.add_game(6n, x, a, b)), T.after_ok(x, tb, a, b), and_intro(T.LiveOK(a, b, tb), T.IsNone(T.W0(a, b)), live_ok_of(a, b, tb, l1, inv), isnone_of(T.W0(a, b), l2)))

# A live, valid set stays valid when a game or tiebreak is won (by the table).
law add_step:
  for x: S.Side
  for tb: Bool
  for +a: Nat
  for +b: Nat
  for live: {T.W0(a, b) == None{} : Maybe<S.Side>}
  for inv: {T.SetInv.go(T.W0(a, b), a, b, tb) == True{} : Bool}
  {T.SetInv(S.TennisSet.add_game(6n, x, a, b)) == True{} : Bool}

def add_step(x, tb, a, b, live, inv):
  add_step_go(x, tb, a, b, dup_eq(Maybe<S.Side>, T.W0(a, b), None{}, live), inv)

# A point inside a game: the game goes on (same games, still valid) or is won.
law game_step:
  for +a: Nat
  for +b: Nat
  for -g: S.Game
  for m2: Maybe<S.Side>
  for g2: S.Game
  for live: {S.TennisSet.winner(6n, S.TennisSet{a, b, S.InGame{g}}) == None{} : Maybe<S.Side>}
  for inv: {T.SetInv(S.TennisSet{a, b, S.InGame{g}}) == True{} : Bool}
  {T.SetInv(S.TennisSet.game_done(m2, 6n, a, b, g2)) == True{} : Bool}

def game_step(a, b, g, m2, g2, live, inv):
  match m2:
    case None{}:
      inv
    case Some{x}:
      add_step(x, False{}, a, b, live, inv)

# The same inside a tiebreak.
law tiebreak_step:
  for +a: Nat
  for +b: Nat
  for -t: S.Tiebreak
  for m2: Maybe<S.Side>
  for t2: S.Tiebreak
  for live: {S.TennisSet.winner(6n, S.TennisSet{a, b, S.InTiebreak{t}}) == None{} : Maybe<S.Side>}
  for inv: {T.SetInv(S.TennisSet{a, b, S.InTiebreak{t}}) == True{} : Bool}
  {T.SetInv(S.TennisSet.tiebreak_done(m2, 6n, a, b, t2)) == True{} : Bool}

def tiebreak_step(a, b, t, m2, t2, live, inv):
  match m2:
    case None{}:
      inv
    case Some{x}:
      add_step(x, True{}, a, b, live, inv)

law set_step_go:
  for +target: Nat
  for +a: Nat
  for +b: Nat
  for +s: S.Side
  for m: Maybe<S.Side>
  for +play: S.Play
  for e: {S.TennisSet.winner(6n, S.TennisSet{a, b, play}) == m : Maybe<S.Side>}
  for inv: {T.SetInv(S.TennisSet{a, b, play}) == True{} : Bool}
  {T.SetInv(S.TennisSet.point.go(m, 6n, target, a, b, play, s)) == True{} : Bool}

def set_step_go(target, a, b, s, m, play, e, inv):
  match m:
    case Some{w}:
      inv
    case None{}:
      match play:
        case S.InGame{+g}:
          game_step(a, b, g, S.Game.winner(S.Game.point(g, s)), S.Game.point(g, s), e, inv)
        case S.InTiebreak{+t}:
          tiebreak_step(a, b, t, S.Tiebreak.winner(target, S.Tiebreak.point(target, t, s)), S.Tiebreak.point(target, t, s), e, inv)

# One point keeps any valid set valid.
law set_step:
  for +target: Nat
  for st: S.TennisSet
  for +s: S.Side
  for inv: {T.SetInv(st) == True{} : Bool}
  {T.SetInv(S.TennisSet.point(6n, target, st, s)) == True{} : Bool}

def set_step(target, st, s, inv):
  match st:
    case S.TennisSet{+a, +b, +play}:
      set_step_go(target, a, b, s, S.TennisSet.winner(6n, S.TennisSet{a, b, play}), play, {==}, inv)

# So any list of points keeps a valid set valid (induction on the list).
law set_reach:
  for +target: Nat
  for pts: List<&2, S.Side>
  for +st: S.TennisSet
  for inv: {T.SetInv(st) == True{} : Bool}
  {T.SetInv(Laws.Rule.play_set(target, pts, st)) == True{} : Bool}

def set_reach(target, pts, st, inv):
  match pts:
    case Nil{}:
      inv
    case Con{+s, rest}:
      set_reach(target, rest, S.TennisSet.point(6n, target, st, s), set_step(target, st, s, inv))

# ---------------------------------------------------------------------------
# Sets: L9 and L10 from the invariant
# ---------------------------------------------------------------------------

law fin_side:
  for x: S.Side
  for +a: Nat
  for +b: Nat
  for -play: S.Play
  for ok: {T.FinOK(x, a, b) == True{} : Bool}
  {Laws.Rule.finished_set_ok(x, S.TennisSet{a, b, play}) == True{} : Bool}

def fin_side(x, a, b, play, ok):
  match x:
    case S.A{}:
      ok
    case S.B{}:
      ok

law fin_go:
  for -w: S.Side
  for m: Maybe<S.Side>
  for h: {m == Some{w} : Maybe<S.Side>}
  for +a: Nat
  for +b: Nat
  for -play: S.Play
  for tb: Bool
  for ok: {T.SetInv.go(m, a, b, tb) == True{} : Bool}
  {Laws.Rule.finished_set_ok(w, S.TennisSet{a, b, play}) == True{} : Bool}

def fin_go(w, m, h, a, b, play, tb, ok):
  match m:
    case None{}:
      ex_falso({Laws.Rule.finished_set_ok(w, S.TennisSet{a, b, play}) == True{} : Bool}, none_is_not_some(w, h))
    case Some{x}:
      %some_injective(x, w, h) : {Laws.Rule.finished_set_ok(_, S.TennisSet{a, b, play}) == True{} : Bool}
      fin_side(x, a, b, play, ok)

law fin_set:
  for -w: S.Side
  for st: S.TennisSet
  for won: {S.TennisSet.winner(6n, st) == Some{w} : Maybe<S.Side>}
  for inv: {T.SetInv(st) == True{} : Bool}
  {Laws.Rule.finished_set_ok(w, st) == True{} : Bool}

def fin_set(w, st, won, inv):
  match st:
    case S.TennisSet{+a, +b, +play}:
      fin_go(w, S.TennisSet.winner(6n, S.TennisSet{a, b, play}), won, a, b, play, T.PlayTB(play), inv)

def Laws.L9_finished_set_score(target, pts, w, won):
  fin_set(w, Laws.Rule.play_set(target, pts, Laws.Rule.fresh_set()), won, set_reach(target, pts, Laws.Rule.fresh_set(), {==}))

law tb_live_go:
  for m: Maybe<S.Side>
  for h: {m == None{} : Maybe<S.Side>}
  for +a: Nat
  for +b: Nat
  for play: S.Play
  for ok: {T.SetInv.go(m, a, b, T.PlayTB(play)) == True{} : Bool}
  {Laws.Rule.in_tiebreak(S.TennisSet{a, b, play}) == Laws.Rule.six_all(S.TennisSet{a, b, play}) : Bool}

def tb_live_go(m, h, a, b, play, ok):
  match m:
    case Some{x}:
      ex_falso({Laws.Rule.in_tiebreak(S.TennisSet{a, b, play}) == Laws.Rule.six_all(S.TennisSet{a, b, play}) : Bool}, none_is_not_some(x, Equal.sym(Maybe<S.Side>, Some{x}, None{}, h)))
    case None{}:
      match play:
        case S.InGame{g}:
          booleq_true(False{}, Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 6n)), and_true_r(Nat.is_le(b, 6n), T.BoolEq(False{}, Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 6n))), and_true_r(Nat.is_le(a, 6n), Bool.and(Nat.is_le(b, 6n), T.BoolEq(False{}, Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 6n)))), ok)))
        case S.InTiebreak{t}:
          booleq_true(True{}, Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 6n)), and_true_r(Nat.is_le(b, 6n), T.BoolEq(True{}, Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 6n))), and_true_r(Nat.is_le(a, 6n), Bool.and(Nat.is_le(b, 6n), T.BoolEq(True{}, Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 6n)))), ok)))

law tb_set:
  for st: S.TennisSet
  for live: {S.TennisSet.winner(6n, st) == None{} : Maybe<S.Side>}
  for inv: {T.SetInv(st) == True{} : Bool}
  {Laws.Rule.in_tiebreak(st) == Laws.Rule.six_all(st) : Bool}

def tb_set(st, live, inv):
  match st:
    case S.TennisSet{+a, +b, +play}:
      tb_live_go(S.TennisSet.winner(6n, S.TennisSet{a, b, play}), live, a, b, play, inv)

def Laws.L10_tiebreak_exactly_at_6_all(target, pts, live):
  tb_set(Laws.Rule.play_set(target, pts, Laws.Rule.fresh_set()), live, set_reach(target, pts, Laws.Rule.fresh_set(), {==}))

# ---------------------------------------------------------------------------
# Matches: every point keeps the match invariant (T.MatchInv), then L12
# ---------------------------------------------------------------------------

# After a point in a live match: the set goes on (same finished sets, still
# valid), or it is won and recorded (valid by the table).
law set_rec_go:
  for +t: Nat
  for +ft: Nat
  for +first: S.Side
  for +done: List<&2, S.Score>
  for +st0: S.TennisSet
  for m2: Maybe<S.Side>
  for +st2: S.TennisSet
  for live: {S.Match.winner(Laws.Rule.wta(t, ft), S.Match{first, done, st0}) == None{} : Maybe<S.Side>}
  for inv: {T.MatchInv(S.Match{first, done, st0}) == True{} : Bool}
  {T.MatchInv(S.Match.set_done(m2, first, done, st2)) == True{} : Bool}

def set_rec_go(t, ft, first, done, st0, m2, st2, live, inv):
  match m2:
    case None{}:
      inv
    case Some{_}:
      impl_elim(Bool.and(T.MInvC(Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)), T.MLive(Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done))), T.MInvC(Laws.Rule.count(Laws.Rule.same(Laws.Rule.score_winner(S.Match.score_of(st2)), S.A{}), Laws.Rule.sets_won(S.A{}, done)), Laws.Rule.count(Laws.Rule.same(Laws.Rule.score_winner(S.Match.score_of(st2)), S.B{}), Laws.Rule.sets_won(S.B{}, done))), T.set_added_ok(Laws.Rule.score_winner(S.Match.score_of(st2)), Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)), and_intro(T.MInvC(Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)), T.MLive(Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)), inv, isnone_of(Laws.Rule.match_winner(2n, done), Equal.trans(Maybe<S.Side>, Laws.Rule.match_winner(Laws.Rule.sets_of(Laws.Rule.wta(t, ft)), done), S.Match.winner(Laws.Rule.wta(t, ft), S.Match{first, done, st0}), None{}, Equal.sym(Maybe<S.Side>, S.Match.winner(Laws.Rule.wta(t, ft), S.Match{first, done, st0}), Laws.Rule.match_winner(Laws.Rule.sets_of(Laws.Rule.wta(t, ft)), done), Laws.L25_match_winner_follows_rule(Laws.Rule.wta(t, ft), first, done, st0)), live))))

law match_step_go:
  for +t: Nat
  for +ft: Nat
  for +first: S.Side
  for +done: List<&2, S.Score>
  for +st: S.TennisSet
  for +s: S.Side
  for m: Maybe<S.Side>
  for e: {S.Match.winner(Laws.Rule.wta(t, ft), S.Match{first, done, st}) == m : Maybe<S.Side>}
  for inv: {T.MatchInv(S.Match{first, done, st}) == True{} : Bool}
  {T.MatchInv(S.Match.point.go(m, Laws.Rule.wta(t, ft), first, done, st, s)) == True{} : Bool}

def match_step_go(t, ft, first, done, st, s, m, e, inv):
  match m:
    case Some{_}:
      inv
    case None{}:
      set_rec_go(t, ft, first, done, st, S.TennisSet.winner(S.Match.games(Laws.Rule.wta(t, ft)), S.Match.set_after(Laws.Rule.wta(t, ft), done, st, s)), S.Match.set_after(Laws.Rule.wta(t, ft), done, st, s), e, inv)

# One point keeps any valid match valid.
law match_step:
  for +t: Nat
  for +ft: Nat
  for m: S.Match
  for +s: S.Side
  for inv: {T.MatchInv(m) == True{} : Bool}
  {T.MatchInv(S.Match.point(Laws.Rule.wta(t, ft), m, s)) == True{} : Bool}

def match_step(t, ft, m, s, inv):
  match m:
    case S.Match{+first, +done, +st}:
      match_step_go(t, ft, first, done, st, s, S.Match.winner(Laws.Rule.wta(t, ft), S.Match{first, done, st}), {==}, inv)

# So any list of points keeps a valid match valid.
law match_reach:
  for +t: Nat
  for +ft: Nat
  for pts: List<&2, S.Side>
  for +m: S.Match
  for inv: {T.MatchInv(m) == True{} : Bool}
  {T.MatchInv(Laws.Rule.play_match(Laws.Rule.wta(t, ft), pts, m)) == True{} : Bool}

def match_reach(t, ft, pts, m, inv):
  match pts:
    case Nil{}:
      inv
    case Con{+s, rest}:
      match_reach(t, ft, rest, S.Match.point(Laws.Rule.wta(t, ft), m, s), match_step(t, ft, m, s, inv))

law fin_match_side:
  for x: S.Side
  for +done: List<&2, S.Score>
  for ok: {T.FinM(x, Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)) == True{} : Bool}
  {Laws.Rule.match_score_ok(x, done) == True{} : Bool}

def fin_match_side(x, done, ok):
  match x:
    case S.A{}:
      ok
    case S.B{}:
      ok

law fin_match_go:
  for -w: S.Side
  for m: Maybe<S.Side>
  for +done: List<&2, S.Score>
  for e: {Laws.Rule.pick(Nat.is_ge(Laws.Rule.sets_won(S.A{}, done), 2n), Nat.is_ge(Laws.Rule.sets_won(S.B{}, done), 2n)) == m : Maybe<S.Side>}
  for h: {m == Some{w} : Maybe<S.Side>}
  for inv: {T.MInvC(Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)) == True{} : Bool}
  {Laws.Rule.match_score_ok(w, done) == True{} : Bool}

def fin_match_go(w, m, done, e, h, inv):
  match m:
    case None{}:
      ex_falso({Laws.Rule.match_score_ok(w, done) == True{} : Bool}, none_is_not_some(w, h))
    case Some{+x}:
      %some_injective(x, w, h) : {Laws.Rule.match_score_ok(_, done) == True{} : Bool}
      fin_match_side(x, done, impl_elim(Bool.and(T.MInvC(Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)), T.IsSide(Laws.Rule.pick(Nat.is_ge(Laws.Rule.sets_won(S.A{}, done), 2n), Nat.is_ge(Laws.Rule.sets_won(S.B{}, done), 2n)), x)), T.FinM(x, Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)), T.match_final_ok(x, Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)), and_intro(T.MInvC(Laws.Rule.sets_won(S.A{}, done), Laws.Rule.sets_won(S.B{}, done)), T.IsSide(Laws.Rule.pick(Nat.is_ge(Laws.Rule.sets_won(S.A{}, done), 2n), Nat.is_ge(Laws.Rule.sets_won(S.B{}, done), 2n)), x), inv, isside_of(Laws.Rule.pick(Nat.is_ge(Laws.Rule.sets_won(S.A{}, done), 2n), Nat.is_ge(Laws.Rule.sets_won(S.B{}, done), 2n)), x, e))))

law fin_match:
  for +t: Nat
  for +ft: Nat
  for -w: S.Side
  for mm: S.Match
  for won: {S.Match.winner(Laws.Rule.wta(t, ft), mm) == Some{w} : Maybe<S.Side>}
  for inv: {T.MatchInv(mm) == True{} : Bool}
  {Laws.Rule.match_score_ok(w, Laws.Rule.done_of(mm)) == True{} : Bool}

def fin_match(t, ft, w, mm, won, inv):
  match mm:
    case S.Match{+first, +done, +st}:
      fin_match_go(w, Laws.Rule.pick(Nat.is_ge(Laws.Rule.sets_won(S.A{}, done), 2n), Nat.is_ge(Laws.Rule.sets_won(S.B{}, done), 2n)), done, {==}, Equal.trans(Maybe<S.Side>, Laws.Rule.match_winner(Laws.Rule.sets_of(Laws.Rule.wta(t, ft)), done), S.Match.winner(Laws.Rule.wta(t, ft), S.Match{first, done, st}), Some{w}, Equal.sym(Maybe<S.Side>, S.Match.winner(Laws.Rule.wta(t, ft), S.Match{first, done, st}), Laws.Rule.match_winner(Laws.Rule.sets_of(Laws.Rule.wta(t, ft)), done), Laws.L25_match_winner_follows_rule(Laws.Rule.wta(t, ft), first, done, st)), won), inv)

def Laws.L12_finished_match_score(t, ft, first, pts, w, won):
  fin_match(t, ft, w, Laws.Rule.play_match(Laws.Rule.wta(t, ft), pts, S.Match.start(first)), won, match_reach(t, ft, pts, S.Match.start(first), {==}))

# ===========================================================================
# MILESTONE 4: simulation
# ===========================================================================

def Laws.ex_chance_100_percent_is_valid():
  {==}

def Laws.ex_chance_above_100_percent_is_rejected():
  {==}

def Laws.ex_roll_below_chance_is_server_point():
  {==}

def Laws.ex_roll_at_chance_is_receiver_point():
  {==}

def Laws.ex_b_serving_uses_b_chance():
  {==}

def Laws.ex_100_percent_server_wins_every_roll():
  {==}

def Laws.ex_0_percent_server_loses_every_roll():
  {==}

def Laws.ex_two_bits_make_four_runs():
  {==}

def Laws.ex_run_5_in_block_0():
  {==}

def Laws.ex_run_13_in_block_1():
  {==}

def Laws.ex_set_3_6_counted_as_b63():
  {==}

# ---------------------------------------------------------------------------
# L1: point chances
# ---------------------------------------------------------------------------

# A Chance carries its own proof of being at most 10,000: hand it back.
def Laws.L1_chance_in_range(c):
  match c:
    case Sim.Chance{p, ok}:
      ok

# The check, for either answer of the comparison.
law chance_make_go:
  for +p: U32
  for fits: Bool
  for ok: {U32.is_le(p, 10000) == fits : Bool}
  {Laws.Rule.made_value(Sim.Chance.make.go(p, fits, ok)) == Laws.Rule.keep_if(fits, p) : Maybe<U32>}

def chance_make_go(p, fits, ok):
  match fits:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.L1_input_check(p):
  chance_make_go(p, U32.is_le(p, 10000), {==})

# ---------------------------------------------------------------------------
# L26: one simulated point
# ---------------------------------------------------------------------------

law pick_same:
  for h: Bool
  for +s: S.Side
  {Sim.Point.pick(h, s) == Laws.Rule.server_or_receiver(h, s) : S.Side}

def pick_same(h, s):
  match h s:
    case True{} S.A{}:
      {==}
    case True{} S.B{}:
      {==}
    case False{} S.A{}:
      {==}
    case False{} S.B{}:
      {==}

law point_winner_same:
  for +s: S.Side
  for +pa: U32
  for +pb: U32
  for +roll: U32
  {Sim.Point.winner(s, pa, pb, roll) == Laws.Rule.point_winner(s, pa, pb, roll) : S.Side}

def point_winner_same(s, pa, pb, roll):
  match s:
    case S.A{}:
      pick_same(U32.is_lt(roll, pa), S.A{})
    case S.B{}:
      pick_same(U32.is_lt(roll, pb), S.B{})

# The engine's point step is the spec's, with the chances as plain numbers.
law apply_is_step:
  for +fmt: S.Format
  for +pa: U32
  for +pb: U32
  for +m: S.Match
  for +roll: U32
  {Sim.Point.apply(fmt, pa, pb, m, roll) == Laws.Rule.step(fmt, pa, pb, m, roll) : S.Match}

def apply_is_step(fmt, pa, pb, m, roll):
  %Equal.sym(S.Side, S.Match.server(m), Laws.Rule.match_server(m), server_same(m)) : {S.Match.point(fmt, m, Sim.Point.winner(_, pa, pb, roll)) == Laws.Rule.step(fmt, pa, pb, m, roll) : S.Match}
  %Equal.sym(S.Side, Sim.Point.winner(Laws.Rule.match_server(m), pa, pb, roll), Laws.Rule.point_winner(Laws.Rule.match_server(m), pa, pb, roll), point_winner_same(Laws.Rule.match_server(m), pa, pb, roll)) : {S.Match.point(fmt, m, _) == Laws.Rule.step(fmt, pa, pb, m, roll) : S.Match}
  {==}

def Laws.L26_point_follows_serve_chance(fmt, ca, cb, m, roll):
  apply_is_step(fmt, Sim.Chance.value(ca), Sim.Chance.value(cb), m, roll)

# ---------------------------------------------------------------------------
# L27: one simulated match
# ---------------------------------------------------------------------------

# Once the match is won, playing more points leaves it as it is (by L13).
# The assumption is needed twice (for this point and the rest), so it comes
# as a pair.
law won_stays:
  for n: Nat
  for +fmt: S.Format
  for +pa: U32
  for +pb: U32
  for +seed: U32
  for +run: U32
  for +slot: U32
  for +k: U32
  for +m: S.Match
  for -x: S.Side
  for hh: {S.Match.winner(fmt, m) == Some{x} : Maybe<S.Side>} & {S.Match.winner(fmt, m) == Some{x} : Maybe<S.Side>}
  {Laws.Rule.play_points(n, fmt, pa, pb, seed, run, slot, k, m) == m : S.Match}

def won_stays(n, fmt, pa, pb, seed, run, slot, k, m, x, hh):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match hh:
        case (h1, h2):
          %Equal.sym(S.Match, S.Match.point(fmt, m, Laws.Rule.point_winner(Laws.Rule.match_server(m), pa, pb, Sim.Rng.roll(seed, run, slot, k))), m, Laws.L13_won_match_is_final(fmt, m, x, h1, Laws.Rule.point_winner(Laws.Rule.match_server(m), pa, pb, Sim.Rng.roll(seed, run, slot, k)))) : {Laws.Rule.play_points(p, fmt, pa, pb, seed, run, slot, U32.inc(k), _) == m : S.Match}
          won_stays(p, fmt, pa, pb, seed, run, slot, U32.inc(k), m, x, dup_eq(Maybe<S.Side>, S.Match.winner(fmt, m), Some{x}, h2))

# The engine's loop, which stops as soon as the match is won, gives the same
# match as playing all n points. `w` is who has won so far.
law loop_is_play:
  for n: Nat
  for +fmt: S.Format
  for +pa: U32
  for +pb: U32
  for +seed: U32
  for +run: U32
  for +slot: U32
  for +k: U32
  for +m: S.Match
  for w: Maybe<S.Side>
  for h: {S.Match.winner(fmt, m) == w : Maybe<S.Side>}
  {Sim.Match.loop(n, w, fmt, pa, pb, Sim.Rng.key(seed, run, slot), k, m) == Laws.Rule.play_points(n, fmt, pa, pb, seed, run, slot, k, m) : S.Match}

def loop_is_play(n, fmt, pa, pb, seed, run, slot, k, m, w, h):
  match n w:
    case 0n _:
      {==}
    case 1n+p Some{x}:
      Equal.sym(S.Match, Laws.Rule.play_points(1n+p, fmt, pa, pb, seed, run, slot, k, m), m, won_stays(1n+p, fmt, pa, pb, seed, run, slot, k, m, x, dup_eq(Maybe<S.Side>, S.Match.winner(fmt, m), Some{x}, h)))
    case 1n+p None{}:
      %Equal.sym(S.Match, Sim.Point.apply(fmt, pa, pb, m, Sim.Rng.roll(seed, run, slot, k)), Laws.Rule.step(fmt, pa, pb, m, Sim.Rng.roll(seed, run, slot, k)), apply_is_step(fmt, pa, pb, m, Sim.Rng.roll(seed, run, slot, k))) : {Sim.Match.loop(p, S.Match.winner(fmt, _), fmt, pa, pb, Sim.Rng.key(seed, run, slot), U32.inc(k), _) == Laws.Rule.play_points(p, fmt, pa, pb, seed, run, slot, U32.inc(k), Laws.Rule.step(fmt, pa, pb, m, Sim.Rng.roll(seed, run, slot, k))) : S.Match}
      loop_is_play(p, fmt, pa, pb, seed, run, slot, U32.inc(k), Laws.Rule.step(fmt, pa, pb, m, Sim.Rng.roll(seed, run, slot, k)), S.Match.winner(fmt, Laws.Rule.step(fmt, pa, pb, m, Sim.Rng.roll(seed, run, slot, k))), {==})

law report_go_same:
  for w: Maybe<S.Side>
  for m: S.Match
  {Sim.Match.report.go(w, m) == Laws.Rule.report.go(w, m) : Sim.Outcome}

def report_go_same(w, m):
  match w:
    case Some{x}:
      {==}
    case None{}:
      {==}

# The engine reports a match the way the spec does (using L25).
law report_same:
  for +fmt: S.Format
  for +m: S.Match
  {Sim.Match.report(fmt, m) == Laws.Rule.report(fmt, m) : Sim.Outcome}

def report_same(fmt, m):
  match m:
    case S.Match{+first, +done, +st}:
      %Equal.sym(Maybe<S.Side>, S.Match.winner(fmt, S.Match{first, done, st}), Laws.Rule.match_winner(Laws.Rule.sets_of(fmt), done), Laws.L25_match_winner_follows_rule(fmt, first, done, st)) : {Sim.Match.report.go(_, S.Match{first, done, st}) == Laws.Rule.report(fmt, S.Match{first, done, st}) : Sim.Outcome}
      report_go_same(Laws.Rule.match_winner(Laws.Rule.sets_of(fmt), done), S.Match{first, done, st})

# L27 for any number of points n and any starting match m; the law is the
# case n = 1,000 and m = 0-0.
law match_is_report:
  for +n: Nat
  for +fmt: S.Format
  for +pa: U32
  for +pb: U32
  for +seed: U32
  for +run: U32
  for +slot: U32
  for +m: S.Match
  {Sim.Match.report(fmt, Sim.Match.loop(n, S.Match.winner(fmt, m), fmt, pa, pb, Sim.Rng.key(seed, run, slot), 0, m)) == Laws.Rule.report(fmt, Laws.Rule.play_points(n, fmt, pa, pb, seed, run, slot, 0, m)) : Sim.Outcome}

def match_is_report(n, fmt, pa, pb, seed, run, slot, m):
  %Equal.sym(S.Match, Sim.Match.loop(n, S.Match.winner(fmt, m), fmt, pa, pb, Sim.Rng.key(seed, run, slot), 0, m), Laws.Rule.play_points(n, fmt, pa, pb, seed, run, slot, 0, m), loop_is_play(n, fmt, pa, pb, seed, run, slot, 0, m, S.Match.winner(fmt, m), {==})) : {Sim.Match.report(fmt, _) == Laws.Rule.report(fmt, Laws.Rule.play_points(n, fmt, pa, pb, seed, run, slot, 0, m)) : Sim.Outcome}
  report_same(fmt, Laws.Rule.play_points(n, fmt, pa, pb, seed, run, slot, 0, m))

# Speed note. Once two sides of an equation differ anywhere, Bend's checker
# computes both sides in full, and computing the spec side here means playing
# 1,000 points symbolically (about 20 s). So the proof is split in two with
# Equal.trans: the first step (engine cap = spec cap) has no spec side to
# compute, and the second matches the spec side letter for letter.
def Laws.L27_match_plays_at_most_1000_points(fmt, ca, cb, seed, run, slot, first):
  Equal.trans(Sim.Outcome, Sim.Match.simulate(fmt, ca, cb, seed, run, slot, first), Sim.Match.report(fmt, Sim.Match.loop(Laws.Rule.cap(), S.Match.winner(fmt, S.Match.start(first)), fmt, Sim.Chance.value(ca), Sim.Chance.value(cb), Sim.Rng.key(seed, run, slot), 0, S.Match.start(first))), Laws.Rule.report(fmt, Laws.Rule.play_points(Laws.Rule.cap(), fmt, Sim.Chance.value(ca), Sim.Chance.value(cb), seed, run, slot, 0, S.Match.start(first))), {==}, match_is_report(Laws.Rule.cap(), fmt, Sim.Chance.value(ca), Sim.Chance.value(cb), seed, run, slot, S.Match.start(first)))

def Laws.L27_single_run_is_one_match(fmt, ca, cb, seed, run):
  {==}

# ---------------------------------------------------------------------------
# L14: counting many runs
# ---------------------------------------------------------------------------

# Two facts about adding Nats, by induction.
law nat_add_zero:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}

def nat_add_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, nat_add_zero(p))

law nat_add_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def nat_add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), nat_add_assoc(p, b, c))

# Two tallies are equal when their fields are.

law sets_cong:
  for -x1: Nat
  for -x2: Nat
  for -x3: Nat
  for -x4: Nat
  for -x5: Nat
  for -x6: Nat
  for -x7: Nat
  for -x8: Nat
  for -x9: Nat
  for -x10: Nat
  for -x11: Nat
  for -x12: Nat
  for -x13: Nat
  for -x14: Nat
  for -x15: Nat
  for -y1: Nat
  for -y2: Nat
  for -y3: Nat
  for -y4: Nat
  for -y5: Nat
  for -y6: Nat
  for -y7: Nat
  for -y8: Nat
  for -y9: Nat
  for -y10: Nat
  for -y11: Nat
  for -y12: Nat
  for -y13: Nat
  for -y14: Nat
  for -y15: Nat
  for e1: {x1 == y1 : Nat}
  for e2: {x2 == y2 : Nat}
  for e3: {x3 == y3 : Nat}
  for e4: {x4 == y4 : Nat}
  for e5: {x5 == y5 : Nat}
  for e6: {x6 == y6 : Nat}
  for e7: {x7 == y7 : Nat}
  for e8: {x8 == y8 : Nat}
  for e9: {x9 == y9 : Nat}
  for e10: {x10 == y10 : Nat}
  for e11: {x11 == y11 : Nat}
  for e12: {x12 == y12 : Nat}
  for e13: {x13 == y13 : Nat}
  for e14: {x14 == y14 : Nat}
  for e15: {x15 == y15 : Nat}
  {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}

def sets_cong(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15):
  %e1 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{_, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e2 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, _, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e3 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, _, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e4 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, _, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e5 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, _, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e6 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, _, y7, y8, y9, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e7 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, x6, _, y8, y9, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e8 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, _, y9, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e9 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, _, y10, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e10 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, _, y11, y12, y13, y14, y15} : Sim.SetCounts}
  %e11 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, _, y12, y13, y14, y15} : Sim.SetCounts}
  %e12 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, _, y13, y14, y15} : Sim.SetCounts}
  %e13 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, _, y14, y15} : Sim.SetCounts}
  %e14 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, _, y15} : Sim.SetCounts}
  %e15 : {Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} == Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, _} : Sim.SetCounts}
  {==}

law tally_cong:
  for -xa: Nat
  for -xb: Nat
  for -xu: Nat
  for -xs: Sim.SetCounts
  for -ya: Nat
  for -yb: Nat
  for -yu: Nat
  for -ys: Sim.SetCounts
  for ea: {xa == ya : Nat}
  for eb: {xb == yb : Nat}
  for eu: {xu == yu : Nat}
  for es: {xs == ys : Sim.SetCounts}
  {Sim.Tally{xa, xb, xu, xs} == Sim.Tally{ya, yb, yu, ys} : Sim.Tally}

def tally_cong(xa, xb, xu, xs, ya, yb, yu, ys, ea, eb, eu, es):
  %ea : {Sim.Tally{xa, xb, xu, xs} == Sim.Tally{_, yb, yu, ys} : Sim.Tally}
  %eb : {Sim.Tally{xa, xb, xu, xs} == Sim.Tally{xa, _, yu, ys} : Sim.Tally}
  %eu : {Sim.Tally{xa, xb, xu, xs} == Sim.Tally{xa, xb, _, ys} : Sim.Tally}
  %es : {Sim.Tally{xa, xb, xu, xs} == Sim.Tally{xa, xb, xu, _} : Sim.Tally}
  {==}

# Adding nothing changes nothing; adding is associative.
law add_nothing_left:
  for t: Sim.Tally
  {Laws.Rule.add(Laws.Rule.nothing(), t) == t : Sim.Tally}

def add_nothing_left(t):
  match t:
    case Sim.Tally{a, b, u, s}:
      match s:
        case Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}:
          {==}

law add_nothing_right:
  for t: Sim.Tally
  {Laws.Rule.add(t, Laws.Rule.nothing()) == t : Sim.Tally}

def add_nothing_right(t):
  match t:
    case Sim.Tally{a, b, u, s}:
      match s:
        case Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}:
          tally_cong(Nat.add(a, 0n), Nat.add(b, 0n), Nat.add(u, 0n), Laws.Rule.add_sets(Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, Laws.Rule.no_sets()), a, b, u, Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}, nat_add_zero(a), nat_add_zero(b), nat_add_zero(u), sets_cong(Nat.add(x1, 0n), Nat.add(x2, 0n), Nat.add(x3, 0n), Nat.add(x4, 0n), Nat.add(x5, 0n), Nat.add(x6, 0n), Nat.add(x7, 0n), Nat.add(x8, 0n), Nat.add(x9, 0n), Nat.add(x10, 0n), Nat.add(x11, 0n), Nat.add(x12, 0n), Nat.add(x13, 0n), Nat.add(x14, 0n), Nat.add(x15, 0n), x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, nat_add_zero(x1), nat_add_zero(x2), nat_add_zero(x3), nat_add_zero(x4), nat_add_zero(x5), nat_add_zero(x6), nat_add_zero(x7), nat_add_zero(x8), nat_add_zero(x9), nat_add_zero(x10), nat_add_zero(x11), nat_add_zero(x12), nat_add_zero(x13), nat_add_zero(x14), nat_add_zero(x15)))

law add_assoc:
  for x: Sim.Tally
  for y: Sim.Tally
  for z: Sim.Tally
  {Laws.Rule.add(Laws.Rule.add(x, y), z) == Laws.Rule.add(x, Laws.Rule.add(y, z)) : Sim.Tally}

def add_assoc(x, y, z):
  match x y z:
    case Sim.Tally{xa, xb, xu, Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}} Sim.Tally{ya, yb, yu, Sim.SetCounts{y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}} Sim.Tally{za, zb, zu, Sim.SetCounts{z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}}:
      tally_cong(Nat.add(Nat.add(xa, ya), za), Nat.add(Nat.add(xb, yb), zb), Nat.add(Nat.add(xu, yu), zu), Sim.SetCounts{Nat.add(Nat.add(x1, y1), z1), Nat.add(Nat.add(x2, y2), z2), Nat.add(Nat.add(x3, y3), z3), Nat.add(Nat.add(x4, y4), z4), Nat.add(Nat.add(x5, y5), z5), Nat.add(Nat.add(x6, y6), z6), Nat.add(Nat.add(x7, y7), z7), Nat.add(Nat.add(x8, y8), z8), Nat.add(Nat.add(x9, y9), z9), Nat.add(Nat.add(x10, y10), z10), Nat.add(Nat.add(x11, y11), z11), Nat.add(Nat.add(x12, y12), z12), Nat.add(Nat.add(x13, y13), z13), Nat.add(Nat.add(x14, y14), z14), Nat.add(Nat.add(x15, y15), z15)}, Nat.add(xa, Nat.add(ya, za)), Nat.add(xb, Nat.add(yb, zb)), Nat.add(xu, Nat.add(yu, zu)), Sim.SetCounts{Nat.add(x1, Nat.add(y1, z1)), Nat.add(x2, Nat.add(y2, z2)), Nat.add(x3, Nat.add(y3, z3)), Nat.add(x4, Nat.add(y4, z4)), Nat.add(x5, Nat.add(y5, z5)), Nat.add(x6, Nat.add(y6, z6)), Nat.add(x7, Nat.add(y7, z7)), Nat.add(x8, Nat.add(y8, z8)), Nat.add(x9, Nat.add(y9, z9)), Nat.add(x10, Nat.add(y10, z10)), Nat.add(x11, Nat.add(y11, z11)), Nat.add(x12, Nat.add(y12, z12)), Nat.add(x13, Nat.add(y13, z13)), Nat.add(x14, Nat.add(y14, z14)), Nat.add(x15, Nat.add(y15, z15))}, nat_add_assoc(xa, ya, za), nat_add_assoc(xb, yb, zb), nat_add_assoc(xu, yu, zu), sets_cong(Nat.add(Nat.add(x1, y1), z1), Nat.add(Nat.add(x2, y2), z2), Nat.add(Nat.add(x3, y3), z3), Nat.add(Nat.add(x4, y4), z4), Nat.add(Nat.add(x5, y5), z5), Nat.add(Nat.add(x6, y6), z6), Nat.add(Nat.add(x7, y7), z7), Nat.add(Nat.add(x8, y8), z8), Nat.add(Nat.add(x9, y9), z9), Nat.add(Nat.add(x10, y10), z10), Nat.add(Nat.add(x11, y11), z11), Nat.add(Nat.add(x12, y12), z12), Nat.add(Nat.add(x13, y13), z13), Nat.add(Nat.add(x14, y14), z14), Nat.add(Nat.add(x15, y15), z15), Nat.add(x1, Nat.add(y1, z1)), Nat.add(x2, Nat.add(y2, z2)), Nat.add(x3, Nat.add(y3, z3)), Nat.add(x4, Nat.add(y4, z4)), Nat.add(x5, Nat.add(y5, z5)), Nat.add(x6, Nat.add(y6, z6)), Nat.add(x7, Nat.add(y7, z7)), Nat.add(x8, Nat.add(y8, z8)), Nat.add(x9, Nat.add(y9, z9)), Nat.add(x10, Nat.add(y10, z10)), Nat.add(x11, Nat.add(y11, z11)), Nat.add(x12, Nat.add(y12, z12)), Nat.add(x13, Nat.add(y13, z13)), Nat.add(x14, Nat.add(y14, z14)), Nat.add(x15, Nat.add(y15, z15)), nat_add_assoc(x1, y1, z1), nat_add_assoc(x2, y2, z2), nat_add_assoc(x3, y3, z3), nat_add_assoc(x4, y4, z4), nat_add_assoc(x5, y5, z5), nat_add_assoc(x6, y6, z6), nat_add_assoc(x7, y7, z7), nat_add_assoc(x8, y8, z8), nat_add_assoc(x9, y9, z9), nat_add_assoc(x10, y10, z10), nat_add_assoc(x11, y11, z11), nat_add_assoc(x12, y12, z12), nat_add_assoc(x13, y13, z13), nat_add_assoc(x14, y14, z14), nat_add_assoc(x15, y15, z15)))

# A list of tallies added in two parts is the sum of the parts.
law sum_append:
  for +xs: List<&2, Sim.Tally>
  for +ys: List<&2, Sim.Tally>
  {Laws.Rule.sum(List.append(&2, Sim.Tally, xs, ys)) == Laws.Rule.add(Laws.Rule.sum(xs), Laws.Rule.sum(ys)) : Sim.Tally}

def sum_append(xs, ys):
  match xs:
    case Nil{}:
      Equal.sym(Sim.Tally, Laws.Rule.add(Laws.Rule.nothing(), Laws.Rule.sum(ys)), Laws.Rule.sum(ys), add_nothing_left(Laws.Rule.sum(ys)))
    case Con{+t, +rest}:
      %Equal.sym(Sim.Tally, Laws.Rule.sum(List.append(&2, Sim.Tally, rest, ys)), Laws.Rule.add(Laws.Rule.sum(rest), Laws.Rule.sum(ys)), sum_append(rest, ys)) : {Laws.Rule.add(t, _) == Laws.Rule.add(Laws.Rule.add(t, Laws.Rule.sum(rest)), Laws.Rule.sum(ys)) : Sim.Tally}
      Equal.sym(Sim.Tally, Laws.Rule.add(Laws.Rule.add(t, Laws.Rule.sum(rest)), Laws.Rule.sum(ys)), Laws.Rule.add(t, Laws.Rule.add(Laws.Rule.sum(rest), Laws.Rule.sum(ys))), add_assoc(t, Laws.Rule.sum(rest), Laws.Rule.sum(ys)))

# The runs of two lists of paths are the runs of each.
law results_append:
  for +fmt: S.Format
  for +ca: Sim.Chance
  for +cb: Sim.Chance
  for +seed: U32
  for +prefix: U32
  for +xs: List<&2, List<&2, Bool>>
  for +ys: List<&2, List<&2, Bool>>
  {Laws.Rule.results(fmt, ca, cb, seed, prefix, List.append(&2, List<&2, Bool>, xs, ys)) == List.append(&2, Sim.Tally, Laws.Rule.results(fmt, ca, cb, seed, prefix, xs), Laws.Rule.results(fmt, ca, cb, seed, prefix, ys)) : List<&2, Sim.Tally>}

def results_append(fmt, ca, cb, seed, prefix, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+path, +rest}:
      %Equal.sym(List<&2, Sim.Tally>, Laws.Rule.results(fmt, ca, cb, seed, prefix, List.append(&2, List<&2, Bool>, rest, ys)), List.append(&2, Sim.Tally, Laws.Rule.results(fmt, ca, cb, seed, prefix, rest), Laws.Rule.results(fmt, ca, cb, seed, prefix, ys)), results_append(fmt, ca, cb, seed, prefix, rest, ys)) : {(Laws.Rule.tally_of(Sim.Run.single(fmt, ca, cb, seed, Laws.Rule.number(path, prefix))) <> _) == List.append(&2, Sim.Tally, Laws.Rule.results(fmt, ca, cb, seed, prefix, path <> rest), Laws.Rule.results(fmt, ca, cb, seed, prefix, ys)) : List<&2, Sim.Tally>}
      {==}

# Putting bit b in front of every path moves to block 2*prefix+b.
law results_cons_all:
  for +fmt: S.Format
  for +ca: Sim.Chance
  for +cb: Sim.Chance
  for +seed: U32
  for +b: Bool
  for +prefix: U32
  for +paths: List<&2, List<&2, Bool>>
  {Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(b, paths)) == Laws.Rule.results(fmt, ca, cb, seed, (prefix * 2 + Laws.Rule.bit(b) : U32), paths) : List<&2, Sim.Tally>}

def results_cons_all(fmt, ca, cb, seed, b, prefix, paths):
  match paths:
    case Nil{}:
      {==}
    case Con{+path, +rest}:
      %Equal.sym(List<&2, Sim.Tally>, Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(b, rest)), Laws.Rule.results(fmt, ca, cb, seed, (prefix * 2 + Laws.Rule.bit(b) : U32), rest), results_cons_all(fmt, ca, cb, seed, b, prefix, rest)) : {(Laws.Rule.tally_of(Sim.Run.single(fmt, ca, cb, seed, Laws.Rule.number(b <> path, prefix))) <> _) == Laws.Rule.results(fmt, ca, cb, seed, (prefix * 2 + Laws.Rule.bit(b) : U32), path <> rest) : List<&2, Sim.Tally>}
      {==}

# The engine's tally helpers agree with the spec's.
law add_sets_same:
  for x: Sim.SetCounts
  for y: Sim.SetCounts
  {Sim.Run.add_sets(x, y) == Laws.Rule.add_sets(x, y) : Sim.SetCounts}

def add_sets_same(x, y):
  match x y:
    case Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15} Sim.SetCounts{y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}:
      {==}

law run_add_same:
  for x: Sim.Tally
  for y: Sim.Tally
  {Sim.Run.add(x, y) == Laws.Rule.add(x, y) : Sim.Tally}

def run_add_same(x, y):
  match x y:
    case Sim.Tally{xa, xb, xu, Sim.SetCounts{x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15}} Sim.Tally{ya, yb, yu, Sim.SetCounts{y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}}:
      {==}

law one_set_same:
  for sc: S.Score
  {Sim.Run.one_set(sc) == Laws.Rule.one_set(sc) : Sim.SetCounts}

def one_set_same(sc):
  match sc:
    case S.Score{+a, +b}:
      sets_cong(S.Match.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 0n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 1n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 2n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 3n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 4n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 7n), Nat.is_eq(b, 5n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 7n), Nat.is_eq(b, 6n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b, 6n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 1n), Nat.is_eq(b, 6n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 2n), Nat.is_eq(b, 6n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 3n), Nat.is_eq(b, 6n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 4n), Nat.is_eq(b, 6n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 5n), Nat.is_eq(b, 7n)), 0n), S.Match.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 7n)), 0n), S.Match.count(Bool.not(Bool.or(Sim.Run.score_ok(a, b), Sim.Run.score_ok(b, a))), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 0n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 1n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 2n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 3n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 4n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 7n), Nat.is_eq(b, 5n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 7n), Nat.is_eq(b, 6n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b, 6n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 1n), Nat.is_eq(b, 6n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 2n), Nat.is_eq(b, 6n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 3n), Nat.is_eq(b, 6n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 4n), Nat.is_eq(b, 6n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 5n), Nat.is_eq(b, 7n)), 0n), Laws.Rule.count(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 7n)), 0n), Laws.Rule.count(Bool.not(Bool.or(Laws.Rule.set_score_ok(a, b), Laws.Rule.set_score_ok(b, a))), 0n), count_same(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 0n)), 0n), count_same(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 1n)), 0n), count_same(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 2n)), 0n), count_same(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 3n)), 0n), count_same(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 4n)), 0n), count_same(Bool.and(Nat.is_eq(a, 7n), Nat.is_eq(b, 5n)), 0n), count_same(Bool.and(Nat.is_eq(a, 7n), Nat.is_eq(b, 6n)), 0n), count_same(Bool.and(Nat.is_eq(a, 0n), Nat.is_eq(b, 6n)), 0n), count_same(Bool.and(Nat.is_eq(a, 1n), Nat.is_eq(b, 6n)), 0n), count_same(Bool.and(Nat.is_eq(a, 2n), Nat.is_eq(b, 6n)), 0n), count_same(Bool.and(Nat.is_eq(a, 3n), Nat.is_eq(b, 6n)), 0n), count_same(Bool.and(Nat.is_eq(a, 4n), Nat.is_eq(b, 6n)), 0n), count_same(Bool.and(Nat.is_eq(a, 5n), Nat.is_eq(b, 7n)), 0n), count_same(Bool.and(Nat.is_eq(a, 6n), Nat.is_eq(b, 7n)), 0n), count_same(Bool.not(Bool.or(Sim.Run.score_ok(a, b), Sim.Run.score_ok(b, a))), 0n))

law set_scores_same:
  for +done: List<&2, S.Score>
  {Sim.Run.set_scores(done) == Laws.Rule.set_scores(done) : Sim.SetCounts}

def set_scores_same(done):
  match done:
    case Nil{}:
      {==}
    case Con{+sc, +rest}:
      %Equal.sym(Sim.SetCounts, Sim.Run.one_set(sc), Laws.Rule.one_set(sc), one_set_same(sc)) : {Sim.Run.add_sets(_, Sim.Run.set_scores(rest)) == Laws.Rule.add_sets(Laws.Rule.one_set(sc), Laws.Rule.set_scores(rest)) : Sim.SetCounts}
      %Equal.sym(Sim.SetCounts, Sim.Run.set_scores(rest), Laws.Rule.set_scores(rest), set_scores_same(rest)) : {Sim.Run.add_sets(Laws.Rule.one_set(sc), _) == Laws.Rule.add_sets(Laws.Rule.one_set(sc), Laws.Rule.set_scores(rest)) : Sim.SetCounts}
      add_sets_same(Laws.Rule.one_set(sc), Laws.Rule.set_scores(rest))

law run_count_same:
  for o: Sim.Outcome
  {Sim.Run.count(o) == Laws.Rule.tally_of(o) : Sim.Tally}

def run_count_same(o):
  match o:
    case Sim.Won{w, m}:
      match w m:
        case S.A{} S.Match{_, +done, _}:
          Equal.cong(Sim.SetCounts, Sim.Tally, s => Sim.Tally{1n, 0n, 0n, s}, Sim.Run.set_scores(done), Laws.Rule.set_scores(done), set_scores_same(done))
        case S.B{} S.Match{_, +done, _}:
          Equal.cong(Sim.SetCounts, Sim.Tally, s => Sim.Tally{0n, 1n, 0n, s}, Sim.Run.set_scores(done), Laws.Rule.set_scores(done), set_scores_same(done))
    case Sim.Unfinished{_}:
      {==}

# L14, by induction on the number of bits: a block of 2^(1+p) runs is two
# blocks of 2^p, and its list of paths is the paths starting False followed
# by those starting True.
def Laws.L14_every_run_counted_once(d, fmt, ca, cb, seed, prefix):
  match d:
    case 0n:
      %Equal.sym(Sim.Tally, Sim.Run.count(Sim.Run.single(fmt, ca, cb, seed, prefix)), Laws.Rule.tally_of(Sim.Run.single(fmt, ca, cb, seed, prefix)), run_count_same(Sim.Run.single(fmt, ca, cb, seed, prefix))) : {_ == Laws.Rule.sum(Laws.Rule.results(fmt, ca, cb, seed, prefix, [[]])) : Sim.Tally}
      Equal.sym(Sim.Tally, Laws.Rule.add(Laws.Rule.tally_of(Sim.Run.single(fmt, ca, cb, seed, prefix)), Laws.Rule.nothing()), Laws.Rule.tally_of(Sim.Run.single(fmt, ca, cb, seed, prefix)), add_nothing_right(Laws.Rule.tally_of(Sim.Run.single(fmt, ca, cb, seed, prefix))))
    case 1n+p:
      %Equal.sym(List<&2, Sim.Tally>, Laws.Rule.results(fmt, ca, cb, seed, prefix, List.append(&2, List<&2, Bool>, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p)), Laws.Rule.cons_all(True{}, Laws.Rule.paths(p)))), List.append(&2, Sim.Tally, Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p))), Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p)))), results_append(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p)), Laws.Rule.cons_all(True{}, Laws.Rule.paths(p)))) : {Sim.Run.add(Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)), Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.sum(_) : Sim.Tally}
      %Equal.sym(Sim.Tally, Laws.Rule.sum(List.append(&2, Sim.Tally, Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p))), Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))))), Laws.Rule.add(Laws.Rule.sum(Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p)))), Laws.Rule.sum(Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))))), sum_append(Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p))), Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))))) : {Sim.Run.add(Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)), Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 1 : U32))) == _ : Sim.Tally}
      %Equal.sym(List<&2, Sim.Tally>, Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p))), Laws.Rule.results(fmt, ca, cb, seed, (prefix * 2 + Laws.Rule.bit(False{}) : U32), Laws.Rule.paths(p)), results_cons_all(fmt, ca, cb, seed, False{}, prefix, Laws.Rule.paths(p))) : {Sim.Run.add(Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)), Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.add(Laws.Rule.sum(_), Laws.Rule.sum(Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))))) : Sim.Tally}
      %Equal.sym(List<&2, Sim.Tally>, Laws.Rule.results(fmt, ca, cb, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))), Laws.Rule.results(fmt, ca, cb, seed, (prefix * 2 + Laws.Rule.bit(True{}) : U32), Laws.Rule.paths(p)), results_cons_all(fmt, ca, cb, seed, True{}, prefix, Laws.Rule.paths(p))) : {Sim.Run.add(Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)), Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.add(Laws.Rule.sum(Laws.Rule.results(fmt, ca, cb, seed, (prefix * 2 + 0 : U32), Laws.Rule.paths(p))), Laws.Rule.sum(_)) : Sim.Tally}
      %Laws.L14_every_run_counted_once(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)) : {Sim.Run.add(Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)), Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.add(_, Laws.Rule.sum(Laws.Rule.results(fmt, ca, cb, seed, (prefix * 2 + 1 : U32), Laws.Rule.paths(p)))) : Sim.Tally}
      %Laws.L14_every_run_counted_once(p, fmt, ca, cb, seed, (prefix * 2 + 1 : U32)) : {Sim.Run.add(Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)), Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.add(Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)), _) : Sim.Tally}
      run_add_same(Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 0 : U32)), Sim.Run.tally(p, fmt, ca, cb, seed, (prefix * 2 + 1 : U32)))


# ===========================================================================
# MILESTONE 6: groups, standings and knockouts
# ===========================================================================

def Laws.ex_seeded_draw():
  {==}

def Laws.ex_wins_decide():
  {==}

def Laws.ex_two_way_ties_go_to_head_to_head():
  {==}

def Laws.ex_three_way_tie_by_sets():
  {==}

def Laws.ex_three_way_tie_then_head_to_head():
  {==}

def Laws.ex_three_way_tie_by_games():
  {==}

def Laws.ex_three_way_tie_by_race():
  {==}

def Laws.ex_three_way_tie_for_second():
  {==}

def Laws.ex_semis():
  {==}

# ---------------------------------------------------------------------------
# L15: the draw. Three lots, eight cases, each computed.
# ---------------------------------------------------------------------------

def Laws.L15_seeded_draw_follows_rule(l34, l56, l78):
  match l34 l56 l78:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# ---------------------------------------------------------------------------
# L19: the semifinal lines
# ---------------------------------------------------------------------------

# Three nested choices agree, by trying every combination of the conditions.
law choose3_same:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for s1: Nat
  for s2: Nat
  for s3: Nat
  for s4: Nat
  {S.Match.choose(b1, s1, S.Match.choose(b2, s2, S.Match.choose(b3, s3, s4))) == Laws.Rule.choose(b1, s1, Laws.Rule.choose(b2, s2, Laws.Rule.choose(b3, s3, s4))) : Nat}

def choose3_same(b1, b2, b3, s1, s2, s3, s4):
  match b1 b2 b3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

law at_place_same:
  for +n: Nat
  for g: Tour.Group
  for pl: Tour.Places
  {Tour.Knockout.at_place(n, g, pl) == Laws.Rule.at_place(n, g, pl) : Nat}

def at_place_same(n, g, pl):
  match g pl:
    case Tour.Group{s1, s2, s3, s4} Tour.Places{+p1, +p2, +p3, _}:
      choose3_same(Nat.is_eq(p1, n), Nat.is_eq(p2, n), Nat.is_eq(p3, n), s1, s2, s3, s4)

def Laws.L19_semis_cross_groups(ga, pa, gb, pb):
  %at_place_same(1n, ga, pa) : {Tour.Knockout.semis(ga, pa, gb, pb) == Tour.Semis{_, Laws.Rule.at_place(2n, gb, pb), Laws.Rule.at_place(2n, ga, pa), Laws.Rule.at_place(1n, gb, pb)} : Tour.Semis}
  %at_place_same(2n, gb, pb) : {Tour.Knockout.semis(ga, pa, gb, pb) == Tour.Semis{Tour.Knockout.at_place(1n, ga, pa), _, Laws.Rule.at_place(2n, ga, pa), Laws.Rule.at_place(1n, gb, pb)} : Tour.Semis}
  %at_place_same(2n, ga, pa) : {Tour.Knockout.semis(ga, pa, gb, pb) == Tour.Semis{Tour.Knockout.at_place(1n, ga, pa), Tour.Knockout.at_place(2n, gb, pb), _, Laws.Rule.at_place(1n, gb, pb)} : Tour.Semis}
  %at_place_same(1n, gb, pb) : {Tour.Knockout.semis(ga, pa, gb, pb) == Tour.Semis{Tour.Knockout.at_place(1n, ga, pa), Tour.Knockout.at_place(2n, gb, pb), Tour.Knockout.at_place(2n, ga, pa), _} : Tour.Semis}
  {==}


# ---------------------------------------------------------------------------
# L28: the standings. The engine's helpers follow the rule's one by one.
# The two sides keep their records in different types (Tour.Record and
# Laws.GroupRecord), so `conv` turns one into the other, and the lemmas say
# that converting the engine's record gives the rule's.
# ---------------------------------------------------------------------------

def conv(r: Tour.Record) -> Laws.GroupRecord:
  match r:
    case Tour.Record{a, b, c, d, e}:
      Laws.GroupRecord{a, b, c, d, e}

law games_for_same:
  for s: S.Side
  for sc: S.Score
  {Tour.Standings.games_for(s, sc) == Laws.Rule.games_for(s, sc) : Nat}

def games_for_same(s, sc):
  match s sc:
    case S.A{} S.Score{a, b}:
      {==}
    case S.B{} S.Score{a, b}:
      {==}

law games_won_same:
  for +s: S.Side
  for done: List<&2, S.Score>
  {Tour.Standings.games_won(s, done) == Laws.Rule.games_won(s, done) : Nat}

def games_won_same(s, done):
  match done:
    case Nil{}:
      {==}
    case Con{+sc, +rest}:
      %games_won_same(s, rest) : {Nat.add(Tour.Standings.games_for(s, sc), Tour.Standings.games_won(s, rest)) == Nat.add(Laws.Rule.games_for(s, sc), _) : Nat}
      %games_for_same(s, sc) : {Nat.add(Tour.Standings.games_for(s, sc), Tour.Standings.games_won(s, rest)) == Nat.add(_, Tour.Standings.games_won(s, rest)) : Nat}
      {==}

law entry_conv:
  for +s: S.Side
  for r: Tour.Finished
  {conv(Tour.Standings.entry(s, r)) == Laws.Rule.entry(s, r) : Laws.GroupRecord}

def entry_conv(s, r):
  match r:
    case Tour.Finished{+w, +sets}:
      %other_same(s) : {conv(Tour.Standings.entry(s, Tour.Finished{w, sets})) == Laws.GroupRecord{Laws.Rule.count(Laws.Rule.same(w, s), 0n), Laws.Rule.sets_won(s, sets), Laws.Rule.sets_won(_, sets), Laws.Rule.games_won(s, sets), Laws.Rule.games_won(_, sets)} : Laws.GroupRecord}
      %sets_won_same(s, sets) : {conv(Tour.Standings.entry(s, Tour.Finished{w, sets})) == Laws.GroupRecord{Laws.Rule.count(Laws.Rule.same(w, s), 0n), _, Laws.Rule.sets_won(S.Side.other(s), sets), Laws.Rule.games_won(s, sets), Laws.Rule.games_won(S.Side.other(s), sets)} : Laws.GroupRecord}
      %sets_won_same(S.Side.other(s), sets) : {conv(Tour.Standings.entry(s, Tour.Finished{w, sets})) == Laws.GroupRecord{Laws.Rule.count(Laws.Rule.same(w, s), 0n), S.Match.sets_won(s, sets), _, Laws.Rule.games_won(s, sets), Laws.Rule.games_won(S.Side.other(s), sets)} : Laws.GroupRecord}
      %games_won_same(s, sets) : {conv(Tour.Standings.entry(s, Tour.Finished{w, sets})) == Laws.GroupRecord{Laws.Rule.count(Laws.Rule.same(w, s), 0n), S.Match.sets_won(s, sets), S.Match.sets_won(S.Side.other(s), sets), _, Laws.Rule.games_won(S.Side.other(s), sets)} : Laws.GroupRecord}
      %games_won_same(S.Side.other(s), sets) : {conv(Tour.Standings.entry(s, Tour.Finished{w, sets})) == Laws.GroupRecord{Laws.Rule.count(Laws.Rule.same(w, s), 0n), S.Match.sets_won(s, sets), S.Match.sets_won(S.Side.other(s), sets), Tour.Standings.games_won(s, sets), _} : Laws.GroupRecord}
      %same_same(w, s) : {conv(Tour.Standings.entry(s, Tour.Finished{w, sets})) == Laws.GroupRecord{Laws.Rule.count(_, 0n), S.Match.sets_won(s, sets), S.Match.sets_won(S.Side.other(s), sets), Tour.Standings.games_won(s, sets), Tour.Standings.games_won(S.Side.other(s), sets)} : Laws.GroupRecord}
      %count_same(S.Match.same(w, s), 0n) : {conv(Tour.Standings.entry(s, Tour.Finished{w, sets})) == Laws.GroupRecord{_, S.Match.sets_won(s, sets), S.Match.sets_won(S.Side.other(s), sets), Tour.Standings.games_won(s, sets), Tour.Standings.games_won(S.Side.other(s), sets)} : Laws.GroupRecord}
      {==}

law plus3_conv:
  for a: Tour.Record
  for b: Tour.Record
  for c: Tour.Record
  {conv(Tour.Standings.plus3(a, b, c)) == Laws.Rule.plus3(conv(a), conv(b), conv(c)) : Laws.GroupRecord}

def plus3_conv(a, b, c):
  match a b c:
    case Tour.Record{a1, a2, a3, a4, a5} Tour.Record{b1, b2, b3, b4, b5} Tour.Record{c1, c2, c3, c4, c5}:
      {==}

law record_conv:
  for x: Tour.Pos
  for rr: Tour.RoundRobin
  {conv(Tour.Standings.record(x, rr)) == Laws.Rule.record(x, rr) : Laws.GroupRecord}

def record_conv(x, rr):
  match x rr:
    case Tour.P1{} Tour.RoundRobin{+r12, +r13, +r14, _, _, _}:
      %entry_conv(S.A{}, r12) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.A{}, r12), Tour.Standings.entry(S.A{}, r13), Tour.Standings.entry(S.A{}, r14))) == Laws.Rule.plus3(_, Laws.Rule.entry(S.A{}, r13), Laws.Rule.entry(S.A{}, r14)) : Laws.GroupRecord}
      %entry_conv(S.A{}, r13) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.A{}, r12), Tour.Standings.entry(S.A{}, r13), Tour.Standings.entry(S.A{}, r14))) == Laws.Rule.plus3(conv(Tour.Standings.entry(S.A{}, r12)), _, Laws.Rule.entry(S.A{}, r14)) : Laws.GroupRecord}
      %entry_conv(S.A{}, r14) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.A{}, r12), Tour.Standings.entry(S.A{}, r13), Tour.Standings.entry(S.A{}, r14))) == Laws.Rule.plus3(conv(Tour.Standings.entry(S.A{}, r12)), conv(Tour.Standings.entry(S.A{}, r13)), _) : Laws.GroupRecord}
      plus3_conv(Tour.Standings.entry(S.A{}, r12), Tour.Standings.entry(S.A{}, r13), Tour.Standings.entry(S.A{}, r14))
    case Tour.P2{} Tour.RoundRobin{+r12, _, _, +r23, +r24, _}:
      %entry_conv(S.B{}, r12) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.B{}, r12), Tour.Standings.entry(S.A{}, r23), Tour.Standings.entry(S.A{}, r24))) == Laws.Rule.plus3(_, Laws.Rule.entry(S.A{}, r23), Laws.Rule.entry(S.A{}, r24)) : Laws.GroupRecord}
      %entry_conv(S.A{}, r23) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.B{}, r12), Tour.Standings.entry(S.A{}, r23), Tour.Standings.entry(S.A{}, r24))) == Laws.Rule.plus3(conv(Tour.Standings.entry(S.B{}, r12)), _, Laws.Rule.entry(S.A{}, r24)) : Laws.GroupRecord}
      %entry_conv(S.A{}, r24) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.B{}, r12), Tour.Standings.entry(S.A{}, r23), Tour.Standings.entry(S.A{}, r24))) == Laws.Rule.plus3(conv(Tour.Standings.entry(S.B{}, r12)), conv(Tour.Standings.entry(S.A{}, r23)), _) : Laws.GroupRecord}
      plus3_conv(Tour.Standings.entry(S.B{}, r12), Tour.Standings.entry(S.A{}, r23), Tour.Standings.entry(S.A{}, r24))
    case Tour.P3{} Tour.RoundRobin{_, +r13, _, +r23, _, +r34}:
      %entry_conv(S.B{}, r13) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.B{}, r13), Tour.Standings.entry(S.B{}, r23), Tour.Standings.entry(S.A{}, r34))) == Laws.Rule.plus3(_, Laws.Rule.entry(S.B{}, r23), Laws.Rule.entry(S.A{}, r34)) : Laws.GroupRecord}
      %entry_conv(S.B{}, r23) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.B{}, r13), Tour.Standings.entry(S.B{}, r23), Tour.Standings.entry(S.A{}, r34))) == Laws.Rule.plus3(conv(Tour.Standings.entry(S.B{}, r13)), _, Laws.Rule.entry(S.A{}, r34)) : Laws.GroupRecord}
      %entry_conv(S.A{}, r34) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.B{}, r13), Tour.Standings.entry(S.B{}, r23), Tour.Standings.entry(S.A{}, r34))) == Laws.Rule.plus3(conv(Tour.Standings.entry(S.B{}, r13)), conv(Tour.Standings.entry(S.B{}, r23)), _) : Laws.GroupRecord}
      plus3_conv(Tour.Standings.entry(S.B{}, r13), Tour.Standings.entry(S.B{}, r23), Tour.Standings.entry(S.A{}, r34))
    case Tour.P4{} Tour.RoundRobin{_, _, +r14, _, +r24, +r34}:
      %entry_conv(S.B{}, r14) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.B{}, r14), Tour.Standings.entry(S.B{}, r24), Tour.Standings.entry(S.B{}, r34))) == Laws.Rule.plus3(_, Laws.Rule.entry(S.B{}, r24), Laws.Rule.entry(S.B{}, r34)) : Laws.GroupRecord}
      %entry_conv(S.B{}, r24) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.B{}, r14), Tour.Standings.entry(S.B{}, r24), Tour.Standings.entry(S.B{}, r34))) == Laws.Rule.plus3(conv(Tour.Standings.entry(S.B{}, r14)), _, Laws.Rule.entry(S.B{}, r34)) : Laws.GroupRecord}
      %entry_conv(S.B{}, r34) : {conv(Tour.Standings.plus3(Tour.Standings.entry(S.B{}, r14), Tour.Standings.entry(S.B{}, r24), Tour.Standings.entry(S.B{}, r34))) == Laws.Rule.plus3(conv(Tour.Standings.entry(S.B{}, r14)), conv(Tour.Standings.entry(S.B{}, r24)), _) : Laws.GroupRecord}
      plus3_conv(Tour.Standings.entry(S.B{}, r14), Tour.Standings.entry(S.B{}, r24), Tour.Standings.entry(S.B{}, r34))

law wins_of_conv:
  for r: Tour.Record
  {Tour.Standings.wins_of(r) == Laws.Rule.wins_of(conv(r)) : Nat}

def wins_of_conv(r):
  match r:
    case Tour.Record{a, b, c, d, e}:
      {==}

law wins_same:
  for +x: Tour.Pos
  for +rr: Tour.RoundRobin
  {Tour.Standings.wins(x, rr) == Laws.Rule.wins(x, rr) : Nat}

def wins_same(x, rr):
  %record_conv(x, rr) : {Tour.Standings.wins(x, rr) == Laws.Rule.wins_of(_) : Nat}
  wins_of_conv(Tour.Standings.record(x, rr))

law set_go_conv:
  for y: Tour.Record
  for x: Tour.Record
  {Tour.Standings.set_cmp.go(y, x) == Laws.Rule.set_cmp.go(conv(y), conv(x)) : Cmp}

def set_go_conv(y, x):
  match y x:
    case Tour.Record{a1, a2, a3, a4, a5} Tour.Record{b1, b2, b3, b4, b5}:
      {==}

law game_go_conv:
  for y: Tour.Record
  for x: Tour.Record
  {Tour.Standings.game_cmp.go(y, x) == Laws.Rule.game_cmp.go(conv(y), conv(x)) : Cmp}

def game_go_conv(y, x):
  match y x:
    case Tour.Record{a1, a2, a3, a4, a5} Tour.Record{b1, b2, b3, b4, b5}:
      {==}

law set_cmp_same:
  for +y: Tour.Pos
  for +x: Tour.Pos
  for +rr: Tour.RoundRobin
  {Tour.Standings.set_cmp(y, x, rr) == Laws.Rule.set_cmp(y, x, rr) : Cmp}

def set_cmp_same(y, x, rr):
  %record_conv(y, rr) : {Tour.Standings.set_cmp(y, x, rr) == Laws.Rule.set_cmp.go(_, Laws.Rule.record(x, rr)) : Cmp}
  %record_conv(x, rr) : {Tour.Standings.set_cmp(y, x, rr) == Laws.Rule.set_cmp.go(conv(Tour.Standings.record(y, rr)), _) : Cmp}
  set_go_conv(Tour.Standings.record(y, rr), Tour.Standings.record(x, rr))

law game_cmp_same:
  for +y: Tour.Pos
  for +x: Tour.Pos
  for +rr: Tour.RoundRobin
  {Tour.Standings.game_cmp(y, x, rr) == Laws.Rule.game_cmp(y, x, rr) : Cmp}

def game_cmp_same(y, x, rr):
  %record_conv(y, rr) : {Tour.Standings.game_cmp(y, x, rr) == Laws.Rule.game_cmp.go(_, Laws.Rule.record(x, rr)) : Cmp}
  %record_conv(x, rr) : {Tour.Standings.game_cmp(y, x, rr) == Laws.Rule.game_cmp.go(conv(Tour.Standings.record(y, rr)), _) : Cmp}
  game_go_conv(Tour.Standings.record(y, rr), Tour.Standings.record(x, rr))

law won_as_same:
  for s: S.Side
  for r: Tour.Finished
  {Tour.Standings.won_as(s, r) == Laws.Rule.won_as(s, r) : Bool}

def won_as_same(s, r):
  match s r:
    case S.A{} Tour.Finished{S.A{}, _}:
      {==}
    case S.A{} Tour.Finished{S.B{}, _}:
      {==}
    case S.B{} Tour.Finished{S.A{}, _}:
      {==}
    case S.B{} Tour.Finished{S.B{}, _}:
      {==}

law beat_same:
  for y: Tour.Pos
  for x: Tour.Pos
  for rr: Tour.RoundRobin
  {Tour.Standings.beat(y, x, rr) == Laws.Rule.beat(y, x, rr) : Bool}

def beat_same(y, x, rr):
  match y x rr:
    case Tour.P1{} Tour.P1{} _:
      {==}
    case Tour.P1{} Tour.P2{} Tour.RoundRobin{r, _, _, _, _, _}:
      won_as_same(S.A{}, r)
    case Tour.P1{} Tour.P3{} Tour.RoundRobin{_, r, _, _, _, _}:
      won_as_same(S.A{}, r)
    case Tour.P1{} Tour.P4{} Tour.RoundRobin{_, _, r, _, _, _}:
      won_as_same(S.A{}, r)
    case Tour.P2{} Tour.P1{} Tour.RoundRobin{r, _, _, _, _, _}:
      won_as_same(S.B{}, r)
    case Tour.P2{} Tour.P2{} _:
      {==}
    case Tour.P2{} Tour.P3{} Tour.RoundRobin{_, _, _, r, _, _}:
      won_as_same(S.A{}, r)
    case Tour.P2{} Tour.P4{} Tour.RoundRobin{_, _, _, _, r, _}:
      won_as_same(S.A{}, r)
    case Tour.P3{} Tour.P1{} Tour.RoundRobin{_, r, _, _, _, _}:
      won_as_same(S.B{}, r)
    case Tour.P3{} Tour.P2{} Tour.RoundRobin{_, _, _, r, _, _}:
      won_as_same(S.B{}, r)
    case Tour.P3{} Tour.P3{} _:
      {==}
    case Tour.P3{} Tour.P4{} Tour.RoundRobin{_, _, _, _, _, r}:
      won_as_same(S.A{}, r)
    case Tour.P4{} Tour.P1{} Tour.RoundRobin{_, _, r, _, _, _}:
      won_as_same(S.B{}, r)
    case Tour.P4{} Tour.P2{} Tour.RoundRobin{_, _, _, _, r, _}:
      won_as_same(S.B{}, r)
    case Tour.P4{} Tour.P3{} Tour.RoundRobin{_, _, _, _, _, r}:
      won_as_same(S.B{}, r)
    case Tour.P4{} Tour.P4{} _:
      {==}

law seed_same:
  for x: Tour.Pos
  for g: Tour.Group
  {Tour.Standings.seed(x, g) == Laws.Rule.seed(x, g) : Nat}

def seed_same(x, g):
  match x g:
    case Tour.P1{} Tour.Group{a, b, c, d}:
      {==}
    case Tour.P2{} Tour.Group{a, b, c, d}:
      {==}
    case Tour.P3{} Tour.Group{a, b, c, d}:
      {==}
    case Tour.P4{} Tour.Group{a, b, c, d}:
      {==}

law race_same:
  for +y: Tour.Pos
  for +x: Tour.Pos
  for +g: Tour.Group
  {Tour.Standings.race(y, x, g) == Laws.Rule.race(y, x, g) : Bool}

def race_same(y, x, g):
  %seed_same(y, g) : {Tour.Standings.race(y, x, g) == Nat.is_lt(_, Laws.Rule.seed(x, g)) : Bool}
  %seed_same(x, g) : {Tour.Standings.race(y, x, g) == Nat.is_lt(Tour.Standings.seed(y, g), _) : Bool}
  {==}

law decide_same:
  for c: Cmp
  for l: Bool
  {Tour.Standings.decide(c, l) == Laws.Rule.decide(c, l) : Bool}

def decide_same(c, l):
  match c:
    case GT{}:
      {==}
    case LT{}:
      {==}
    case EQ{}:
      {==}

# The shape of the three-way rule, with its comparisons as inputs: every
# combination of them gives the same answer on both sides.
law three_way_shape:
  for a: Cmp
  for b: Bool
  for c: Cmp
  for d: Bool
  for e: Bool
  for +f: Bool
  {Tour.Standings.decide(a, Tour.Standings.either(b, Tour.Standings.decide(c, Tour.Standings.either(d, e, f)), f)) == Laws.Rule.decide(a, Laws.Rule.either(b, Laws.Rule.decide(c, Laws.Rule.either(d, e, f)), f)) : Bool}

def three_way_shape(a, b, c, d, e, f):
  match a b c d:
    case GT{} True{} GT{} True{}:
      {==}
    case GT{} True{} GT{} False{}:
      {==}
    case GT{} True{} LT{} True{}:
      {==}
    case GT{} True{} LT{} False{}:
      {==}
    case GT{} True{} EQ{} True{}:
      {==}
    case GT{} True{} EQ{} False{}:
      {==}
    case GT{} False{} GT{} True{}:
      {==}
    case GT{} False{} GT{} False{}:
      {==}
    case GT{} False{} LT{} True{}:
      {==}
    case GT{} False{} LT{} False{}:
      {==}
    case GT{} False{} EQ{} True{}:
      {==}
    case GT{} False{} EQ{} False{}:
      {==}
    case LT{} True{} GT{} True{}:
      {==}
    case LT{} True{} GT{} False{}:
      {==}
    case LT{} True{} LT{} True{}:
      {==}
    case LT{} True{} LT{} False{}:
      {==}
    case LT{} True{} EQ{} True{}:
      {==}
    case LT{} True{} EQ{} False{}:
      {==}
    case LT{} False{} GT{} True{}:
      {==}
    case LT{} False{} GT{} False{}:
      {==}
    case LT{} False{} LT{} True{}:
      {==}
    case LT{} False{} LT{} False{}:
      {==}
    case LT{} False{} EQ{} True{}:
      {==}
    case LT{} False{} EQ{} False{}:
      {==}
    case EQ{} True{} GT{} True{}:
      {==}
    case EQ{} True{} GT{} False{}:
      {==}
    case EQ{} True{} LT{} True{}:
      {==}
    case EQ{} True{} LT{} False{}:
      {==}
    case EQ{} True{} EQ{} True{}:
      {==}
    case EQ{} True{} EQ{} False{}:
      {==}
    case EQ{} False{} GT{} True{}:
      {==}
    case EQ{} False{} GT{} False{}:
      {==}
    case EQ{} False{} LT{} True{}:
      {==}
    case EQ{} False{} LT{} False{}:
      {==}
    case EQ{} False{} EQ{} True{}:
      {==}
    case EQ{} False{} EQ{} False{}:
      {==}

law three_way_same:
  for +y: Tour.Pos
  for +x: Tour.Pos
  for +k: Tour.Pos
  for +g: Tour.Group
  for +rr: Tour.RoundRobin
  {Tour.Standings.three_way(y, x, k, g, rr) == Laws.Rule.three_way(y, x, k, g, rr) : Bool}

def three_way_same(y, x, k, g, rr):
  %set_cmp_same(y, x, rr) : {Tour.Standings.three_way(y, x, k, g, rr) == Laws.Rule.decide(_, Laws.Rule.either(Cmp.is_eq(Laws.Rule.set_cmp(k, x, rr)), Laws.Rule.decide(Laws.Rule.game_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(Laws.Rule.game_cmp(k, x, rr)), Laws.Rule.race(y, x, g), Laws.Rule.beat(y, x, rr))), Laws.Rule.beat(y, x, rr))) : Bool}
  %set_cmp_same(k, x, rr) : {Tour.Standings.three_way(y, x, k, g, rr) == Laws.Rule.decide(Tour.Standings.set_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(_), Laws.Rule.decide(Laws.Rule.game_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(Laws.Rule.game_cmp(k, x, rr)), Laws.Rule.race(y, x, g), Laws.Rule.beat(y, x, rr))), Laws.Rule.beat(y, x, rr))) : Bool}
  %game_cmp_same(y, x, rr) : {Tour.Standings.three_way(y, x, k, g, rr) == Laws.Rule.decide(Tour.Standings.set_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(Tour.Standings.set_cmp(k, x, rr)), Laws.Rule.decide(_, Laws.Rule.either(Cmp.is_eq(Laws.Rule.game_cmp(k, x, rr)), Laws.Rule.race(y, x, g), Laws.Rule.beat(y, x, rr))), Laws.Rule.beat(y, x, rr))) : Bool}
  %game_cmp_same(k, x, rr) : {Tour.Standings.three_way(y, x, k, g, rr) == Laws.Rule.decide(Tour.Standings.set_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(Tour.Standings.set_cmp(k, x, rr)), Laws.Rule.decide(Tour.Standings.game_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(_), Laws.Rule.race(y, x, g), Laws.Rule.beat(y, x, rr))), Laws.Rule.beat(y, x, rr))) : Bool}
  %race_same(y, x, g) : {Tour.Standings.three_way(y, x, k, g, rr) == Laws.Rule.decide(Tour.Standings.set_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(Tour.Standings.set_cmp(k, x, rr)), Laws.Rule.decide(Tour.Standings.game_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(Tour.Standings.game_cmp(k, x, rr)), _, Laws.Rule.beat(y, x, rr))), Laws.Rule.beat(y, x, rr))) : Bool}
  %beat_same(y, x, rr) : {Tour.Standings.three_way(y, x, k, g, rr) == Laws.Rule.decide(Tour.Standings.set_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(Tour.Standings.set_cmp(k, x, rr)), Laws.Rule.decide(Tour.Standings.game_cmp(y, x, rr), Laws.Rule.either(Cmp.is_eq(Tour.Standings.game_cmp(k, x, rr)), Tour.Standings.race(y, x, g), _)), _)) : Bool}
  three_way_shape(Tour.Standings.set_cmp(y, x, rr), Cmp.is_eq(Tour.Standings.set_cmp(k, x, rr)), Tour.Standings.game_cmp(y, x, rr), Cmp.is_eq(Tour.Standings.game_cmp(k, x, rr)), Tour.Standings.race(y, x, g), Tour.Standings.beat(y, x, rr))

law tied_same:
  for zt: Bool
  for wt: Bool
  for +y: Tour.Pos
  for +x: Tour.Pos
  for +z: Tour.Pos
  for +w: Tour.Pos
  for +g: Tour.Group
  for +rr: Tour.RoundRobin
  {Tour.Standings.tied(zt, wt, y, x, z, w, g, rr) == Laws.Rule.tied(zt, wt, y, x, z, w, g, rr) : Bool}

def tied_same(zt, wt, y, x, z, w, g, rr):
  match zt wt:
    case False{} False{}:
      beat_same(y, x, rr)
    case True{} False{}:
      three_way_same(y, x, z, g, rr)
    case False{} True{}:
      three_way_same(y, x, w, g, rr)
    case True{} True{}:
      race_same(y, x, g)

law ahead_same:
  for +y: Tour.Pos
  for +x: Tour.Pos
  for +z: Tour.Pos
  for +w: Tour.Pos
  for +g: Tour.Group
  for +rr: Tour.RoundRobin
  {Tour.Standings.ahead(y, x, z, w, g, rr) == Laws.Rule.ahead(y, x, z, w, g, rr) : Bool}

def ahead_same(y, x, z, w, g, rr):
  %wins_same(y, rr) : {Tour.Standings.ahead(y, x, z, w, g, rr) == Laws.Rule.decide(Nat.cmp(_, Laws.Rule.wins(x, rr)), Laws.Rule.tied(Nat.is_eq(Laws.Rule.wins(z, rr), Laws.Rule.wins(x, rr)), Nat.is_eq(Laws.Rule.wins(w, rr), Laws.Rule.wins(x, rr)), y, x, z, w, g, rr)) : Bool}
  %wins_same(x, rr) : {Tour.Standings.ahead(y, x, z, w, g, rr) == Laws.Rule.decide(Nat.cmp(Tour.Standings.wins(y, rr), _), Laws.Rule.tied(Nat.is_eq(Laws.Rule.wins(z, rr), _), Nat.is_eq(Laws.Rule.wins(w, rr), _), y, x, z, w, g, rr)) : Bool}
  %wins_same(z, rr) : {Tour.Standings.ahead(y, x, z, w, g, rr) == Laws.Rule.decide(Nat.cmp(Tour.Standings.wins(y, rr), Tour.Standings.wins(x, rr)), Laws.Rule.tied(Nat.is_eq(_, Tour.Standings.wins(x, rr)), Nat.is_eq(Laws.Rule.wins(w, rr), Tour.Standings.wins(x, rr)), y, x, z, w, g, rr)) : Bool}
  %wins_same(w, rr) : {Tour.Standings.ahead(y, x, z, w, g, rr) == Laws.Rule.decide(Nat.cmp(Tour.Standings.wins(y, rr), Tour.Standings.wins(x, rr)), Laws.Rule.tied(Nat.is_eq(Tour.Standings.wins(z, rr), Tour.Standings.wins(x, rr)), Nat.is_eq(_, Tour.Standings.wins(x, rr)), y, x, z, w, g, rr)) : Bool}
  %tied_same(Nat.is_eq(Tour.Standings.wins(z, rr), Tour.Standings.wins(x, rr)), Nat.is_eq(Tour.Standings.wins(w, rr), Tour.Standings.wins(x, rr)), y, x, z, w, g, rr) : {Tour.Standings.ahead(y, x, z, w, g, rr) == Laws.Rule.decide(Nat.cmp(Tour.Standings.wins(y, rr), Tour.Standings.wins(x, rr)), _) : Bool}
  decide_same(Nat.cmp(Tour.Standings.wins(y, rr), Tour.Standings.wins(x, rr)), Tour.Standings.tied(Nat.is_eq(Tour.Standings.wins(z, rr), Tour.Standings.wins(x, rr)), Nat.is_eq(Tour.Standings.wins(w, rr), Tour.Standings.wins(x, rr)), y, x, z, w, g, rr))

law count3_same:
  for a: Bool
  for b: Bool
  for c: Bool
  {S.Match.count(a, S.Match.count(b, S.Match.count(c, 1n))) == Laws.Rule.count(a, Laws.Rule.count(b, Laws.Rule.count(c, 1n))) : Nat}

def count3_same(a, b, c):
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

law place_same:
  for +x: Tour.Pos
  for +y: Tour.Pos
  for +z: Tour.Pos
  for +w: Tour.Pos
  for +g: Tour.Group
  for +rr: Tour.RoundRobin
  {Tour.Standings.place(x, y, z, w, g, rr) == Laws.Rule.place(x, y, z, w, g, rr) : Nat}

def place_same(x, y, z, w, g, rr):
  %ahead_same(y, x, z, w, g, rr) : {Tour.Standings.place(x, y, z, w, g, rr) == Laws.Rule.count(_, Laws.Rule.count(Laws.Rule.ahead(z, x, y, w, g, rr), Laws.Rule.count(Laws.Rule.ahead(w, x, y, z, g, rr), 1n))) : Nat}
  %ahead_same(z, x, y, w, g, rr) : {Tour.Standings.place(x, y, z, w, g, rr) == Laws.Rule.count(Tour.Standings.ahead(y, x, z, w, g, rr), Laws.Rule.count(_, Laws.Rule.count(Laws.Rule.ahead(w, x, y, z, g, rr), 1n))) : Nat}
  %ahead_same(w, x, y, z, g, rr) : {Tour.Standings.place(x, y, z, w, g, rr) == Laws.Rule.count(Tour.Standings.ahead(y, x, z, w, g, rr), Laws.Rule.count(Tour.Standings.ahead(z, x, y, w, g, rr), Laws.Rule.count(_, 1n))) : Nat}
  count3_same(Tour.Standings.ahead(y, x, z, w, g, rr), Tour.Standings.ahead(z, x, y, w, g, rr), Tour.Standings.ahead(w, x, y, z, g, rr))

def Laws.L28_standings_follow_rule(g, rr):
  %place_same(Tour.P1{}, Tour.P2{}, Tour.P3{}, Tour.P4{}, g, rr) : {Tour.Standings.places(g, rr) == Tour.Places{_, Laws.Rule.place(Tour.P2{}, Tour.P1{}, Tour.P3{}, Tour.P4{}, g, rr), Laws.Rule.place(Tour.P3{}, Tour.P1{}, Tour.P2{}, Tour.P4{}, g, rr), Laws.Rule.place(Tour.P4{}, Tour.P1{}, Tour.P2{}, Tour.P3{}, g, rr)} : Tour.Places}
  %place_same(Tour.P2{}, Tour.P1{}, Tour.P3{}, Tour.P4{}, g, rr) : {Tour.Standings.places(g, rr) == Tour.Places{Tour.Standings.place(Tour.P1{}, Tour.P2{}, Tour.P3{}, Tour.P4{}, g, rr), _, Laws.Rule.place(Tour.P3{}, Tour.P1{}, Tour.P2{}, Tour.P4{}, g, rr), Laws.Rule.place(Tour.P4{}, Tour.P1{}, Tour.P2{}, Tour.P3{}, g, rr)} : Tour.Places}
  %place_same(Tour.P3{}, Tour.P1{}, Tour.P2{}, Tour.P4{}, g, rr) : {Tour.Standings.places(g, rr) == Tour.Places{Tour.Standings.place(Tour.P1{}, Tour.P2{}, Tour.P3{}, Tour.P4{}, g, rr), Tour.Standings.place(Tour.P2{}, Tour.P1{}, Tour.P3{}, Tour.P4{}, g, rr), _, Laws.Rule.place(Tour.P4{}, Tour.P1{}, Tour.P2{}, Tour.P3{}, g, rr)} : Tour.Places}
  %place_same(Tour.P4{}, Tour.P1{}, Tour.P2{}, Tour.P3{}, g, rr) : {Tour.Standings.places(g, rr) == Tour.Places{Tour.Standings.place(Tour.P1{}, Tour.P2{}, Tour.P3{}, Tour.P4{}, g, rr), Tour.Standings.place(Tour.P2{}, Tour.P1{}, Tour.P3{}, Tour.P4{}, g, rr), Tour.Standings.place(Tour.P3{}, Tour.P1{}, Tour.P2{}, Tour.P4{}, g, rr), _} : Tour.Places}
  {==}

# ---------------------------------------------------------------------------
# L29: one whole tournament. The engine's helpers follow the rule's, step by
# step, using L15, L19 and L28 for the draw, the semifinal lines and the
# standings.
# ---------------------------------------------------------------------------

law pick8_same:
  for n: Nat
  for p1: P.Player
  for p2: P.Player
  for p3: P.Player
  for p4: P.Player
  for p5: P.Player
  for p6: P.Player
  for p7: P.Player
  for p8: P.Player
  {Tour.Event.pick8(n, p1, p2, p3, p4, p5, p6, p7, p8) == Laws.Rule.pick8(n, p1, p2, p3, p4, p5, p6, p7, p8) : P.Player}

def pick8_same(n, p1, p2, p3, p4, p5, p6, p7, p8):
  match n:
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 0n:
      {==}
    case 8n+p:
      {==}

law player_same:
  for n: Nat
  for f: Tour.Field
  {Tour.Event.player(n, f) == Laws.Rule.player(n, f) : P.Player}

def player_same(n, f):
  match f:
    case Tour.Field{m, p1, p2, p3, p4, p5, p6, p7, p8}:
      pick8_same(n, p1, p2, p3, p4, p5, p6, p7, p8)

law chance_same:
  for +f: Tour.Field
  for +x: Nat
  for +y: Nat
  {Tour.Event.chance(f, x, y) == Laws.Rule.chance(f, x, y) : Sim.Chance}

def chance_same(f, x, y):
  match f:
    case Tour.Field{+m, +p1, +p2, +p3, +p4, +p5, +p6, +p7, +p8}:
      %pick8_same(x, p1, p2, p3, p4, p5, p6, p7, p8) : {Tour.Event.chance(Tour.Field{m, p1, p2, p3, p4, p5, p6, p7, p8}, x, y) == P.Serve.chance(m, _, Laws.Rule.pick8(y, p1, p2, p3, p4, p5, p6, p7, p8)) : Sim.Chance}
      %pick8_same(y, p1, p2, p3, p4, p5, p6, p7, p8) : {Tour.Event.chance(Tour.Field{m, p1, p2, p3, p4, p5, p6, p7, p8}, x, y) == P.Serve.chance(m, Tour.Event.pick8(x, p1, p2, p3, p4, p5, p6, p7, p8), _) : Sim.Chance}
      {==}

law finished_same:
  for o: Sim.Outcome
  {Tour.Event.finished(o) == Laws.Rule.finished(o) : Maybe<Tour.Finished>}

def finished_same(o):
  match o:
    case Sim.Won{w, S.Match{a, b, c}}:
      {==}
    case Sim.Unfinished{m}:
      {==}

law match_at_same:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for +slot: U32
  for +x: Nat
  for +y: Nat
  {Tour.Event.match_at(fmt, f, seed, run, slot, x, y) == Laws.Rule.match_at(fmt, f, seed, run, slot, x, y) : Maybe<Tour.Finished>}

def match_at_same(fmt, f, seed, run, slot, x, y):
  %chance_same(f, x, y) : {Tour.Event.match_at(fmt, f, seed, run, slot, x, y) == Laws.Rule.finished(Sim.Match.simulate(fmt, _, Laws.Rule.chance(f, y, x), seed, run, slot, Sim.Rng.coin(seed, run, slot))) : Maybe<Tour.Finished>}
  %chance_same(f, y, x) : {Tour.Event.match_at(fmt, f, seed, run, slot, x, y) == Laws.Rule.finished(Sim.Match.simulate(fmt, Tour.Event.chance(f, x, y), _, seed, run, slot, Sim.Rng.coin(seed, run, slot))) : Maybe<Tour.Finished>}
  finished_same(Sim.Match.simulate(fmt, Tour.Event.chance(f, x, y), Tour.Event.chance(f, y, x), seed, run, slot, Sim.Rng.coin(seed, run, slot)))

law all6_same:
  for a: Maybe<Tour.Finished>
  for b: Maybe<Tour.Finished>
  for c: Maybe<Tour.Finished>
  for d: Maybe<Tour.Finished>
  for e: Maybe<Tour.Finished>
  for h: Maybe<Tour.Finished>
  {Tour.Event.all6(a, b, c, d, e, h) == Laws.Rule.all6(a, b, c, d, e, h) : Maybe<Tour.RoundRobin>}

def all6_same(a, b, c, d, e, h):
  match a:
    case None{}:
      {==}
    case Some{x0}:
      match b:
        case None{}:
          {==}
        case Some{x1}:
          match c:
            case None{}:
              {==}
            case Some{x2}:
              match d:
                case None{}:
                  {==}
                case Some{x3}:
                  match e:
                    case None{}:
                      {==}
                    case Some{x4}:
                      match h:
                        case None{}:
                          {==}
                        case Some{x5}:
                          {==}

law group_play_same:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for +base: U32
  for g: Tour.Group
  {Tour.Event.group_play(fmt, f, seed, run, base, g) == Laws.Rule.group_play(fmt, f, seed, run, base, g) : Maybe<Tour.RoundRobin>}

def group_play_same(fmt, f, seed, run, base, g):
  match g:
    case Tour.Group{+s1, +s2, +s3, +s4}:
      %match_at_same(fmt, f, seed, run, base, s1, s2) : {Tour.Event.group_play(fmt, f, seed, run, base, Tour.Group{s1, s2, s3, s4}) == Laws.Rule.all6(_, Laws.Rule.match_at(fmt, f, seed, run, (base + 1 : U32), s1, s3), Laws.Rule.match_at(fmt, f, seed, run, (base + 2 : U32), s1, s4), Laws.Rule.match_at(fmt, f, seed, run, (base + 3 : U32), s2, s3), Laws.Rule.match_at(fmt, f, seed, run, (base + 4 : U32), s2, s4), Laws.Rule.match_at(fmt, f, seed, run, (base + 5 : U32), s3, s4)) : Maybe<Tour.RoundRobin>}
      %match_at_same(fmt, f, seed, run, (base + 1 : U32), s1, s3) : {Tour.Event.group_play(fmt, f, seed, run, base, Tour.Group{s1, s2, s3, s4}) == Laws.Rule.all6(Tour.Event.match_at(fmt, f, seed, run, base, s1, s2), _, Laws.Rule.match_at(fmt, f, seed, run, (base + 2 : U32), s1, s4), Laws.Rule.match_at(fmt, f, seed, run, (base + 3 : U32), s2, s3), Laws.Rule.match_at(fmt, f, seed, run, (base + 4 : U32), s2, s4), Laws.Rule.match_at(fmt, f, seed, run, (base + 5 : U32), s3, s4)) : Maybe<Tour.RoundRobin>}
      %match_at_same(fmt, f, seed, run, (base + 2 : U32), s1, s4) : {Tour.Event.group_play(fmt, f, seed, run, base, Tour.Group{s1, s2, s3, s4}) == Laws.Rule.all6(Tour.Event.match_at(fmt, f, seed, run, base, s1, s2), Tour.Event.match_at(fmt, f, seed, run, (base + 1 : U32), s1, s3), _, Laws.Rule.match_at(fmt, f, seed, run, (base + 3 : U32), s2, s3), Laws.Rule.match_at(fmt, f, seed, run, (base + 4 : U32), s2, s4), Laws.Rule.match_at(fmt, f, seed, run, (base + 5 : U32), s3, s4)) : Maybe<Tour.RoundRobin>}
      %match_at_same(fmt, f, seed, run, (base + 3 : U32), s2, s3) : {Tour.Event.group_play(fmt, f, seed, run, base, Tour.Group{s1, s2, s3, s4}) == Laws.Rule.all6(Tour.Event.match_at(fmt, f, seed, run, base, s1, s2), Tour.Event.match_at(fmt, f, seed, run, (base + 1 : U32), s1, s3), Tour.Event.match_at(fmt, f, seed, run, (base + 2 : U32), s1, s4), _, Laws.Rule.match_at(fmt, f, seed, run, (base + 4 : U32), s2, s4), Laws.Rule.match_at(fmt, f, seed, run, (base + 5 : U32), s3, s4)) : Maybe<Tour.RoundRobin>}
      %match_at_same(fmt, f, seed, run, (base + 4 : U32), s2, s4) : {Tour.Event.group_play(fmt, f, seed, run, base, Tour.Group{s1, s2, s3, s4}) == Laws.Rule.all6(Tour.Event.match_at(fmt, f, seed, run, base, s1, s2), Tour.Event.match_at(fmt, f, seed, run, (base + 1 : U32), s1, s3), Tour.Event.match_at(fmt, f, seed, run, (base + 2 : U32), s1, s4), Tour.Event.match_at(fmt, f, seed, run, (base + 3 : U32), s2, s3), _, Laws.Rule.match_at(fmt, f, seed, run, (base + 5 : U32), s3, s4)) : Maybe<Tour.RoundRobin>}
      %match_at_same(fmt, f, seed, run, (base + 5 : U32), s3, s4) : {Tour.Event.group_play(fmt, f, seed, run, base, Tour.Group{s1, s2, s3, s4}) == Laws.Rule.all6(Tour.Event.match_at(fmt, f, seed, run, base, s1, s2), Tour.Event.match_at(fmt, f, seed, run, (base + 1 : U32), s1, s3), Tour.Event.match_at(fmt, f, seed, run, (base + 2 : U32), s1, s4), Tour.Event.match_at(fmt, f, seed, run, (base + 3 : U32), s2, s3), Tour.Event.match_at(fmt, f, seed, run, (base + 4 : U32), s2, s4), _) : Maybe<Tour.RoundRobin>}
      all6_same(Tour.Event.match_at(fmt, f, seed, run, base, s1, s2), Tour.Event.match_at(fmt, f, seed, run, (base + 1 : U32), s1, s3), Tour.Event.match_at(fmt, f, seed, run, (base + 2 : U32), s1, s4), Tour.Event.match_at(fmt, f, seed, run, (base + 3 : U32), s2, s3), Tour.Event.match_at(fmt, f, seed, run, (base + 4 : U32), s2, s4), Tour.Event.match_at(fmt, f, seed, run, (base + 5 : U32), s3, s4))

law groups_same:
  for d: Tour.Draw
  for +seed: U32
  for +run: U32
  {Tour.Event.groups(d, seed, run) == Laws.Rule.groups(d, seed, run) : Tour.Group & Tour.Group}

def groups_same(d, seed, run):
  match d:
    case Tour.Seeded{}:
      %same_same(Sim.Rng.coin(seed, run, 15), S.A{}) : {Tour.Event.groups(Tour.Seeded{}, seed, run) == Laws.Rule.seeded_groups(_, Laws.Rule.lot(seed, run, 16), Laws.Rule.lot(seed, run, 17)) : Tour.Group & Tour.Group}
      %same_same(Sim.Rng.coin(seed, run, 16), S.A{}) : {Tour.Event.groups(Tour.Seeded{}, seed, run) == Laws.Rule.seeded_groups(Tour.Event.lot(seed, run, 15), _, Laws.Rule.lot(seed, run, 17)) : Tour.Group & Tour.Group}
      %same_same(Sim.Rng.coin(seed, run, 17), S.A{}) : {Tour.Event.groups(Tour.Seeded{}, seed, run) == Laws.Rule.seeded_groups(Tour.Event.lot(seed, run, 15), Tour.Event.lot(seed, run, 16), _) : Tour.Group & Tour.Group}
      Laws.L15_seeded_draw_follows_rule(Tour.Event.lot(seed, run, 15), Tour.Event.lot(seed, run, 16), Tour.Event.lot(seed, run, 17))
    case Tour.Fixed{a, b}:
      {==}

law on_line_same:
  for n: Nat
  for sm: Tour.Semis
  {Tour.Knockout.on_line(n, sm) == Laws.Rule.on_line(n, sm) : Nat}

def on_line_same(n, sm):
  match n sm:
    case 1n Tour.Semis{a, b, c, d}:
      {==}
    case 2n Tour.Semis{a, b, c, d}:
      {==}
    case 3n Tour.Semis{a, b, c, d}:
      {==}
    case 0n Tour.Semis{a, b, c, d}:
      {==}
    case 4n+p Tour.Semis{a, b, c, d}:
      {==}

law winner_of_same:
  for r: Tour.Finished
  for a: Nat
  for b: Nat
  {Tour.Knockout.winner_of(r, a, b) == Laws.Rule.winner_of(r, a, b) : Nat}

def winner_of_same(r, a, b):
  match r:
    case Tour.Finished{S.A{}, s}:
      {==}
    case Tour.Finished{S.B{}, s}:
      {==}

law finish_same:
  for +ga: Tour.Group
  for +gb: Tour.Group
  for +ra: Tour.RoundRobin
  for +rb: Tour.RoundRobin
  for +sm: Tour.Semis
  for +r1: Tour.Finished
  for +r2: Tour.Finished
  for +f1: Nat
  for +f2: Nat
  for fr: Maybe<Tour.Finished>
  {Tour.Event.finish(ga, gb, ra, rb, sm, r1, r2, f1, f2, fr) == Laws.Rule.finish(ga, gb, ra, rb, sm, r1, r2, f1, f2, fr) : Tour.Outcome}

def finish_same(ga, gb, ra, rb, sm, r1, r2, f1, f2, fr):
  match fr:
    case Some{+r}:
      %winner_of_same(r, f1, f2) : {Tour.Event.finish(ga, gb, ra, rb, sm, r1, r2, f1, f2, Some{r}) == Tour.Complete{ga, gb, ra, rb, sm, r1, r2, f1, f2, r, _} : Tour.Outcome}
      {==}
    case None{}:
      {==}

law final_stage_same:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for +ga: Tour.Group
  for +gb: Tour.Group
  for +ra: Tour.RoundRobin
  for +rb: Tour.RoundRobin
  for +sm: Tour.Semis
  for +r1: Tour.Finished
  for +r2: Tour.Finished
  for +f1: Nat
  for +f2: Nat
  {Tour.Event.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, f1, f2) == Laws.Rule.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, f1, f2) : Tour.Outcome}

def final_stage_same(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, f1, f2):
  %match_at_same(fmt, f, seed, run, 14, f1, f2) : {Tour.Event.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, f1, f2) == Laws.Rule.finish(ga, gb, ra, rb, sm, r1, r2, f1, f2, _) : Tour.Outcome}
  finish_same(ga, gb, ra, rb, sm, r1, r2, f1, f2, Tour.Event.match_at(fmt, f, seed, run, 14, f1, f2))

law after_semis_same:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for +ga: Tour.Group
  for +gb: Tour.Group
  for +ra: Tour.RoundRobin
  for +rb: Tour.RoundRobin
  for +sm: Tour.Semis
  for s1: Maybe<Tour.Finished>
  for s2: Maybe<Tour.Finished>
  {Tour.Event.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, s1, s2) == Laws.Rule.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, s1, s2) : Tour.Outcome}

def after_semis_same(fmt, f, seed, run, ga, gb, ra, rb, sm, s1, s2):
  match s1 s2:
    case Some{+r1} Some{+r2}:
      %on_line_same(1n, sm) : {Tour.Event.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Some{r1}, Some{r2}) == Laws.Rule.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, Laws.Rule.winner_of(r1, _, Laws.Rule.on_line(2n, sm)), Laws.Rule.winner_of(r2, Laws.Rule.on_line(3n, sm), Laws.Rule.on_line(4n, sm))) : Tour.Outcome}
      %on_line_same(2n, sm) : {Tour.Event.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Some{r1}, Some{r2}) == Laws.Rule.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, Laws.Rule.winner_of(r1, Tour.Knockout.on_line(1n, sm), _), Laws.Rule.winner_of(r2, Laws.Rule.on_line(3n, sm), Laws.Rule.on_line(4n, sm))) : Tour.Outcome}
      %on_line_same(3n, sm) : {Tour.Event.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Some{r1}, Some{r2}) == Laws.Rule.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, Laws.Rule.winner_of(r1, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)), Laws.Rule.winner_of(r2, _, Laws.Rule.on_line(4n, sm))) : Tour.Outcome}
      %on_line_same(4n, sm) : {Tour.Event.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Some{r1}, Some{r2}) == Laws.Rule.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, Laws.Rule.winner_of(r1, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)), Laws.Rule.winner_of(r2, Tour.Knockout.on_line(3n, sm), _)) : Tour.Outcome}
      %winner_of_same(r1, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)) : {Tour.Event.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Some{r1}, Some{r2}) == Laws.Rule.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, _, Laws.Rule.winner_of(r2, Tour.Knockout.on_line(3n, sm), Tour.Knockout.on_line(4n, sm))) : Tour.Outcome}
      %winner_of_same(r2, Tour.Knockout.on_line(3n, sm), Tour.Knockout.on_line(4n, sm)) : {Tour.Event.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Some{r1}, Some{r2}) == Laws.Rule.final_stage(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, Tour.Knockout.winner_of(r1, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)), _) : Tour.Outcome}
      final_stage_same(fmt, f, seed, run, ga, gb, ra, rb, sm, r1, r2, Tour.Knockout.winner_of(r1, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)), Tour.Knockout.winner_of(r2, Tour.Knockout.on_line(3n, sm), Tour.Knockout.on_line(4n, sm)))
    case Some{r1} None{}:
      {==}
    case None{} Some{r2}:
      {==}
    case None{} None{}:
      {==}

law semis_stage_same:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for +ga: Tour.Group
  for +gb: Tour.Group
  for +ra: Tour.RoundRobin
  for +rb: Tour.RoundRobin
  for +sm: Tour.Semis
  {Tour.Event.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, sm) == Laws.Rule.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, sm) : Tour.Outcome}

def semis_stage_same(fmt, f, seed, run, ga, gb, ra, rb, sm):
  %on_line_same(1n, sm) : {Tour.Event.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, sm) == Laws.Rule.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Laws.Rule.match_at(fmt, f, seed, run, 12, _, Laws.Rule.on_line(2n, sm)), Laws.Rule.match_at(fmt, f, seed, run, 13, Laws.Rule.on_line(3n, sm), Laws.Rule.on_line(4n, sm))) : Tour.Outcome}
  %on_line_same(2n, sm) : {Tour.Event.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, sm) == Laws.Rule.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Laws.Rule.match_at(fmt, f, seed, run, 12, Tour.Knockout.on_line(1n, sm), _), Laws.Rule.match_at(fmt, f, seed, run, 13, Laws.Rule.on_line(3n, sm), Laws.Rule.on_line(4n, sm))) : Tour.Outcome}
  %on_line_same(3n, sm) : {Tour.Event.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, sm) == Laws.Rule.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Laws.Rule.match_at(fmt, f, seed, run, 12, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)), Laws.Rule.match_at(fmt, f, seed, run, 13, _, Laws.Rule.on_line(4n, sm))) : Tour.Outcome}
  %on_line_same(4n, sm) : {Tour.Event.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, sm) == Laws.Rule.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Laws.Rule.match_at(fmt, f, seed, run, 12, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)), Laws.Rule.match_at(fmt, f, seed, run, 13, Tour.Knockout.on_line(3n, sm), _)) : Tour.Outcome}
  %match_at_same(fmt, f, seed, run, 12, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)) : {Tour.Event.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, sm) == Laws.Rule.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, _, Laws.Rule.match_at(fmt, f, seed, run, 13, Tour.Knockout.on_line(3n, sm), Tour.Knockout.on_line(4n, sm))) : Tour.Outcome}
  %match_at_same(fmt, f, seed, run, 13, Tour.Knockout.on_line(3n, sm), Tour.Knockout.on_line(4n, sm)) : {Tour.Event.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, sm) == Laws.Rule.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, Tour.Event.match_at(fmt, f, seed, run, 12, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)), _) : Tour.Outcome}
  after_semis_same(fmt, f, seed, run, ga, gb, ra, rb, sm, Tour.Event.match_at(fmt, f, seed, run, 12, Tour.Knockout.on_line(1n, sm), Tour.Knockout.on_line(2n, sm)), Tour.Event.match_at(fmt, f, seed, run, 13, Tour.Knockout.on_line(3n, sm), Tour.Knockout.on_line(4n, sm)))

law after_groups_same:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for +ga: Tour.Group
  for +gb: Tour.Group
  for xa: Maybe<Tour.RoundRobin>
  for xb: Maybe<Tour.RoundRobin>
  {Tour.Event.after_groups(fmt, f, seed, run, ga, gb, xa, xb) == Laws.Rule.after_groups(fmt, f, seed, run, ga, gb, xa, xb) : Tour.Outcome}

def after_groups_same(fmt, f, seed, run, ga, gb, xa, xb):
  match xa xb:
    case Some{+ra} Some{+rb}:
      %Laws.L28_standings_follow_rule(ga, ra) : {Tour.Event.after_groups(fmt, f, seed, run, ga, gb, Some{ra}, Some{rb}) == Laws.Rule.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, Laws.Rule.semis(ga, _, gb, Laws.Rule.places(gb, rb))) : Tour.Outcome}
      %Laws.L28_standings_follow_rule(gb, rb) : {Tour.Event.after_groups(fmt, f, seed, run, ga, gb, Some{ra}, Some{rb}) == Laws.Rule.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, Laws.Rule.semis(ga, Tour.Standings.places(ga, ra), gb, _)) : Tour.Outcome}
      %Laws.L19_semis_cross_groups(ga, Tour.Standings.places(ga, ra), gb, Tour.Standings.places(gb, rb)) : {Tour.Event.after_groups(fmt, f, seed, run, ga, gb, Some{ra}, Some{rb}) == Laws.Rule.semis_stage(fmt, f, seed, run, ga, gb, ra, rb, _) : Tour.Outcome}
      semis_stage_same(fmt, f, seed, run, ga, gb, ra, rb, Tour.Knockout.semis(ga, Tour.Standings.places(ga, ra), gb, Tour.Standings.places(gb, rb)))
    case Some{ra} None{}:
      {==}
    case None{} Some{rb}:
      {==}
    case None{} None{}:
      {==}

law after_draw_same:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for gs: Tour.Group & Tour.Group
  {Tour.Event.after_draw(fmt, f, seed, run, gs) == Laws.Rule.after_draw(fmt, f, seed, run, gs) : Tour.Outcome}

def after_draw_same(fmt, f, seed, run, gs):
  match gs:
    case (+ga, +gb):
      %group_play_same(fmt, f, seed, run, 0, ga) : {Tour.Event.after_draw(fmt, f, seed, run, (ga, gb)) == Laws.Rule.after_groups(fmt, f, seed, run, ga, gb, _, Laws.Rule.group_play(fmt, f, seed, run, 6, gb)) : Tour.Outcome}
      %group_play_same(fmt, f, seed, run, 6, gb) : {Tour.Event.after_draw(fmt, f, seed, run, (ga, gb)) == Laws.Rule.after_groups(fmt, f, seed, run, ga, gb, Tour.Event.group_play(fmt, f, seed, run, 0, ga), _) : Tour.Outcome}
      after_groups_same(fmt, f, seed, run, ga, gb, Tour.Event.group_play(fmt, f, seed, run, 0, ga), Tour.Event.group_play(fmt, f, seed, run, 6, gb))

def Laws.L29_tournament_follows_rules(fmt, f, d, seed, run):
  %groups_same(d, seed, run) : {Tour.Event.play(fmt, f, d, seed, run) == Laws.Rule.after_draw(fmt, f, seed, run, _) : Tour.Outcome}
  after_draw_same(fmt, f, seed, run, Tour.Event.groups(d, seed, run))


# ---------------------------------------------------------------------------
# L18: the champion won her semifinal and the final. By L29 the engine plays
# the rule's tournament; in it, the finalists are the semifinal winners and
# the champion is the final's winner by construction, so each check compares
# a number with itself.
# ---------------------------------------------------------------------------

law cmp_refl:
  for n: Nat
  {Nat.cmp(n, n) == EQ{} : Cmp}

def cmp_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      cmp_refl(p)

law is_eq_refl:
  for n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

def is_eq_refl(n):
  %Equal.sym(Cmp, Nat.cmp(n, n), EQ{}, cmp_refl(n)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

law and3_refl:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  {Bool.and(Bool.and(Nat.is_eq(x, x), Nat.is_eq(y, y)), Nat.is_eq(z, z)) == True{} : Bool}

def and3_refl(x, y, z):
  %Equal.sym(Bool, Nat.is_eq(x, x), True{}, is_eq_refl(x)) : {Bool.and(Bool.and(_, Nat.is_eq(y, y)), Nat.is_eq(z, z)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(y, y), True{}, is_eq_refl(y)) : {Bool.and(Bool.and(True{}, _), Nat.is_eq(z, z)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(z, z), True{}, is_eq_refl(z)) : {Bool.and(Bool.and(True{}, True{}), _) == True{} : Bool}
  {==}

law ok_finish:
  for +ga: Tour.Group
  for +gb: Tour.Group
  for +ra: Tour.RoundRobin
  for +rb: Tour.RoundRobin
  for +sm: Tour.Semis
  for +r1: Tour.Finished
  for +r2: Tour.Finished
  for fr: Maybe<Tour.Finished>
  {Laws.Rule.champion_ok(Laws.Rule.finish(ga, gb, ra, rb, sm, r1, r2, Laws.Rule.winner_of(r1, Laws.Rule.on_line(1n, sm), Laws.Rule.on_line(2n, sm)), Laws.Rule.winner_of(r2, Laws.Rule.on_line(3n, sm), Laws.Rule.on_line(4n, sm)), fr)) == True{} : Bool}

def ok_finish(ga, gb, ra, rb, sm, r1, r2, fr):
  match fr:
    case Some{+r}:
      and3_refl(Laws.Rule.winner_of(r1, Laws.Rule.on_line(1n, sm), Laws.Rule.on_line(2n, sm)), Laws.Rule.winner_of(r2, Laws.Rule.on_line(3n, sm), Laws.Rule.on_line(4n, sm)), Laws.Rule.winner_of(r, Laws.Rule.winner_of(r1, Laws.Rule.on_line(1n, sm), Laws.Rule.on_line(2n, sm)), Laws.Rule.winner_of(r2, Laws.Rule.on_line(3n, sm), Laws.Rule.on_line(4n, sm))))
    case None{}:
      {==}

law ok_after_semis:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for +ga: Tour.Group
  for +gb: Tour.Group
  for +ra: Tour.RoundRobin
  for +rb: Tour.RoundRobin
  for +sm: Tour.Semis
  for s1: Maybe<Tour.Finished>
  for s2: Maybe<Tour.Finished>
  {Laws.Rule.champion_ok(Laws.Rule.after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, s1, s2)) == True{} : Bool}

def ok_after_semis(fmt, f, seed, run, ga, gb, ra, rb, sm, s1, s2):
  match s1 s2:
    case Some{+r1} Some{+r2}:
      ok_finish(ga, gb, ra, rb, sm, r1, r2, Laws.Rule.match_at(fmt, f, seed, run, 14, Laws.Rule.winner_of(r1, Laws.Rule.on_line(1n, sm), Laws.Rule.on_line(2n, sm)), Laws.Rule.winner_of(r2, Laws.Rule.on_line(3n, sm), Laws.Rule.on_line(4n, sm))))
    case Some{r1} None{}:
      {==}
    case None{} Some{r2}:
      {==}
    case None{} None{}:
      {==}

law ok_after_groups:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for +ga: Tour.Group
  for +gb: Tour.Group
  for xa: Maybe<Tour.RoundRobin>
  for xb: Maybe<Tour.RoundRobin>
  {Laws.Rule.champion_ok(Laws.Rule.after_groups(fmt, f, seed, run, ga, gb, xa, xb)) == True{} : Bool}

def ok_after_groups(fmt, f, seed, run, ga, gb, xa, xb):
  match xa xb:
    case Some{+ra} Some{+rb}:
      ok_after_semis(fmt, f, seed, run, ga, gb, ra, rb, Laws.Rule.semis(ga, Laws.Rule.places(ga, ra), gb, Laws.Rule.places(gb, rb)), Laws.Rule.match_at(fmt, f, seed, run, 12, Laws.Rule.on_line(1n, Laws.Rule.semis(ga, Laws.Rule.places(ga, ra), gb, Laws.Rule.places(gb, rb))), Laws.Rule.on_line(2n, Laws.Rule.semis(ga, Laws.Rule.places(ga, ra), gb, Laws.Rule.places(gb, rb)))), Laws.Rule.match_at(fmt, f, seed, run, 13, Laws.Rule.on_line(3n, Laws.Rule.semis(ga, Laws.Rule.places(ga, ra), gb, Laws.Rule.places(gb, rb))), Laws.Rule.on_line(4n, Laws.Rule.semis(ga, Laws.Rule.places(ga, ra), gb, Laws.Rule.places(gb, rb)))))
    case Some{ra} None{}:
      {==}
    case None{} Some{rb}:
      {==}
    case None{} None{}:
      {==}

law ok_after_draw:
  for +fmt: S.Format
  for +f: Tour.Field
  for +seed: U32
  for +run: U32
  for gs: Tour.Group & Tour.Group
  {Laws.Rule.champion_ok(Laws.Rule.after_draw(fmt, f, seed, run, gs)) == True{} : Bool}

def ok_after_draw(fmt, f, seed, run, gs):
  match gs:
    case (+ga, +gb):
      ok_after_groups(fmt, f, seed, run, ga, gb, Laws.Rule.group_play(fmt, f, seed, run, 0, ga), Laws.Rule.group_play(fmt, f, seed, run, 6, gb))

def Laws.L18_champion_won_semi_and_final(fmt, f, d, seed, run):
  %Equal.sym(Tour.Outcome, Tour.Event.play(fmt, f, d, seed, run), Laws.Rule.tournament(fmt, f, d, seed, run), Laws.L29_tournament_follows_rules(fmt, f, d, seed, run)) : {Laws.Rule.champion_ok(_) == True{} : Bool}
  ok_after_draw(fmt, f, seed, run, Laws.Rule.groups(d, seed, run))


# ---------------------------------------------------------------------------
# L30: every tournament counted once. The same proof as L14, for the
# tournament's tally.
# ---------------------------------------------------------------------------

law counts_cong:
  for -x1: Nat
  for -x2: Nat
  for -x3: Nat
  for -x4: Nat
  for -x5: Nat
  for -x6: Nat
  for -x7: Nat
  for -x8: Nat
  for -y1: Nat
  for -y2: Nat
  for -y3: Nat
  for -y4: Nat
  for -y5: Nat
  for -y6: Nat
  for -y7: Nat
  for -y8: Nat
  for e1: {x1 == y1 : Nat}
  for e2: {x2 == y2 : Nat}
  for e3: {x3 == y3 : Nat}
  for e4: {x4 == y4 : Nat}
  for e5: {x5 == y5 : Nat}
  for e6: {x6 == y6 : Nat}
  for e7: {x7 == y7 : Nat}
  for e8: {x8 == y8 : Nat}
  {Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} == Tour.Counts{y1, y2, y3, y4, y5, y6, y7, y8} : Tour.Counts}

def counts_cong(x1, x2, x3, x4, x5, x6, x7, x8, y1, y2, y3, y4, y5, y6, y7, y8, e1, e2, e3, e4, e5, e6, e7, e8):
  %e1 : {Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} == Tour.Counts{_, y2, y3, y4, y5, y6, y7, y8} : Tour.Counts}
  %e2 : {Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} == Tour.Counts{x1, _, y3, y4, y5, y6, y7, y8} : Tour.Counts}
  %e3 : {Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} == Tour.Counts{x1, x2, _, y4, y5, y6, y7, y8} : Tour.Counts}
  %e4 : {Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} == Tour.Counts{x1, x2, x3, _, y5, y6, y7, y8} : Tour.Counts}
  %e5 : {Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} == Tour.Counts{x1, x2, x3, x4, _, y6, y7, y8} : Tour.Counts}
  %e6 : {Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} == Tour.Counts{x1, x2, x3, x4, x5, _, y7, y8} : Tour.Counts}
  %e7 : {Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} == Tour.Counts{x1, x2, x3, x4, x5, x6, _, y8} : Tour.Counts}
  %e8 : {Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} == Tour.Counts{x1, x2, x3, x4, x5, x6, x7, _} : Tour.Counts}
  {==}

law ttally_cong:
  for -xt: Tour.Counts
  for -xf: Tour.Counts
  for -xs: Tour.Counts
  for -xu: Nat
  for -yt: Tour.Counts
  for -yf: Tour.Counts
  for -ys: Tour.Counts
  for -yu: Nat
  for et: {xt == yt : Tour.Counts}
  for ef: {xf == yf : Tour.Counts}
  for es: {xs == ys : Tour.Counts}
  for eu: {xu == yu : Nat}
  {Tour.Tally{xt, xf, xs, xu} == Tour.Tally{yt, yf, ys, yu} : Tour.Tally}

def ttally_cong(xt, xf, xs, xu, yt, yf, ys, yu, et, ef, es, eu):
  %et : {Tour.Tally{xt, xf, xs, xu} == Tour.Tally{_, yf, ys, yu} : Tour.Tally}
  %ef : {Tour.Tally{xt, xf, xs, xu} == Tour.Tally{xt, _, ys, yu} : Tour.Tally}
  %es : {Tour.Tally{xt, xf, xs, xu} == Tour.Tally{xt, xf, _, yu} : Tour.Tally}
  %eu : {Tour.Tally{xt, xf, xs, xu} == Tour.Tally{xt, xf, xs, _} : Tour.Tally}
  {==}

law add_tally_nothing_left:
  for t: Tour.Tally
  {Laws.Rule.add_tally(Laws.Rule.no_tally(), t) == t : Tour.Tally}

def add_tally_nothing_left(t):
  match t:
    case Tour.Tally{Tour.Counts{xt1, xt2, xt3, xt4, xt5, xt6, xt7, xt8}, Tour.Counts{xf1, xf2, xf3, xf4, xf5, xf6, xf7, xf8}, Tour.Counts{xs1, xs2, xs3, xs4, xs5, xs6, xs7, xs8}, xu}:
      {==}

law add_tally_nothing_right:
  for t: Tour.Tally
  {Laws.Rule.add_tally(t, Laws.Rule.no_tally()) == t : Tour.Tally}

def add_tally_nothing_right(t):
  match t:
    case Tour.Tally{Tour.Counts{xt1, xt2, xt3, xt4, xt5, xt6, xt7, xt8}, Tour.Counts{xf1, xf2, xf3, xf4, xf5, xf6, xf7, xf8}, Tour.Counts{xs1, xs2, xs3, xs4, xs5, xs6, xs7, xs8}, xu}:
      ttally_cong(Tour.Counts{Nat.add(xt1, 0n), Nat.add(xt2, 0n), Nat.add(xt3, 0n), Nat.add(xt4, 0n), Nat.add(xt5, 0n), Nat.add(xt6, 0n), Nat.add(xt7, 0n), Nat.add(xt8, 0n)}, Tour.Counts{Nat.add(xf1, 0n), Nat.add(xf2, 0n), Nat.add(xf3, 0n), Nat.add(xf4, 0n), Nat.add(xf5, 0n), Nat.add(xf6, 0n), Nat.add(xf7, 0n), Nat.add(xf8, 0n)}, Tour.Counts{Nat.add(xs1, 0n), Nat.add(xs2, 0n), Nat.add(xs3, 0n), Nat.add(xs4, 0n), Nat.add(xs5, 0n), Nat.add(xs6, 0n), Nat.add(xs7, 0n), Nat.add(xs8, 0n)}, Nat.add(xu, 0n), Tour.Counts{xt1, xt2, xt3, xt4, xt5, xt6, xt7, xt8}, Tour.Counts{xf1, xf2, xf3, xf4, xf5, xf6, xf7, xf8}, Tour.Counts{xs1, xs2, xs3, xs4, xs5, xs6, xs7, xs8}, xu, counts_cong(Nat.add(xt1, 0n), Nat.add(xt2, 0n), Nat.add(xt3, 0n), Nat.add(xt4, 0n), Nat.add(xt5, 0n), Nat.add(xt6, 0n), Nat.add(xt7, 0n), Nat.add(xt8, 0n), xt1, xt2, xt3, xt4, xt5, xt6, xt7, xt8, nat_add_zero(xt1), nat_add_zero(xt2), nat_add_zero(xt3), nat_add_zero(xt4), nat_add_zero(xt5), nat_add_zero(xt6), nat_add_zero(xt7), nat_add_zero(xt8)), counts_cong(Nat.add(xf1, 0n), Nat.add(xf2, 0n), Nat.add(xf3, 0n), Nat.add(xf4, 0n), Nat.add(xf5, 0n), Nat.add(xf6, 0n), Nat.add(xf7, 0n), Nat.add(xf8, 0n), xf1, xf2, xf3, xf4, xf5, xf6, xf7, xf8, nat_add_zero(xf1), nat_add_zero(xf2), nat_add_zero(xf3), nat_add_zero(xf4), nat_add_zero(xf5), nat_add_zero(xf6), nat_add_zero(xf7), nat_add_zero(xf8)), counts_cong(Nat.add(xs1, 0n), Nat.add(xs2, 0n), Nat.add(xs3, 0n), Nat.add(xs4, 0n), Nat.add(xs5, 0n), Nat.add(xs6, 0n), Nat.add(xs7, 0n), Nat.add(xs8, 0n), xs1, xs2, xs3, xs4, xs5, xs6, xs7, xs8, nat_add_zero(xs1), nat_add_zero(xs2), nat_add_zero(xs3), nat_add_zero(xs4), nat_add_zero(xs5), nat_add_zero(xs6), nat_add_zero(xs7), nat_add_zero(xs8)), nat_add_zero(xu))

law add_tally_assoc:
  for x: Tour.Tally
  for y: Tour.Tally
  for z: Tour.Tally
  {Laws.Rule.add_tally(Laws.Rule.add_tally(x, y), z) == Laws.Rule.add_tally(x, Laws.Rule.add_tally(y, z)) : Tour.Tally}

def add_tally_assoc(x, y, z):
  match x y z:
    case Tour.Tally{Tour.Counts{xt1, xt2, xt3, xt4, xt5, xt6, xt7, xt8}, Tour.Counts{xf1, xf2, xf3, xf4, xf5, xf6, xf7, xf8}, Tour.Counts{xs1, xs2, xs3, xs4, xs5, xs6, xs7, xs8}, xu} Tour.Tally{Tour.Counts{yt1, yt2, yt3, yt4, yt5, yt6, yt7, yt8}, Tour.Counts{yf1, yf2, yf3, yf4, yf5, yf6, yf7, yf8}, Tour.Counts{ys1, ys2, ys3, ys4, ys5, ys6, ys7, ys8}, yu} Tour.Tally{Tour.Counts{zt1, zt2, zt3, zt4, zt5, zt6, zt7, zt8}, Tour.Counts{zf1, zf2, zf3, zf4, zf5, zf6, zf7, zf8}, Tour.Counts{zs1, zs2, zs3, zs4, zs5, zs6, zs7, zs8}, zu}:
      ttally_cong(Tour.Counts{Nat.add(Nat.add(xt1, yt1), zt1), Nat.add(Nat.add(xt2, yt2), zt2), Nat.add(Nat.add(xt3, yt3), zt3), Nat.add(Nat.add(xt4, yt4), zt4), Nat.add(Nat.add(xt5, yt5), zt5), Nat.add(Nat.add(xt6, yt6), zt6), Nat.add(Nat.add(xt7, yt7), zt7), Nat.add(Nat.add(xt8, yt8), zt8)}, Tour.Counts{Nat.add(Nat.add(xf1, yf1), zf1), Nat.add(Nat.add(xf2, yf2), zf2), Nat.add(Nat.add(xf3, yf3), zf3), Nat.add(Nat.add(xf4, yf4), zf4), Nat.add(Nat.add(xf5, yf5), zf5), Nat.add(Nat.add(xf6, yf6), zf6), Nat.add(Nat.add(xf7, yf7), zf7), Nat.add(Nat.add(xf8, yf8), zf8)}, Tour.Counts{Nat.add(Nat.add(xs1, ys1), zs1), Nat.add(Nat.add(xs2, ys2), zs2), Nat.add(Nat.add(xs3, ys3), zs3), Nat.add(Nat.add(xs4, ys4), zs4), Nat.add(Nat.add(xs5, ys5), zs5), Nat.add(Nat.add(xs6, ys6), zs6), Nat.add(Nat.add(xs7, ys7), zs7), Nat.add(Nat.add(xs8, ys8), zs8)}, Nat.add(Nat.add(xu, yu), zu), Tour.Counts{Nat.add(xt1, Nat.add(yt1, zt1)), Nat.add(xt2, Nat.add(yt2, zt2)), Nat.add(xt3, Nat.add(yt3, zt3)), Nat.add(xt4, Nat.add(yt4, zt4)), Nat.add(xt5, Nat.add(yt5, zt5)), Nat.add(xt6, Nat.add(yt6, zt6)), Nat.add(xt7, Nat.add(yt7, zt7)), Nat.add(xt8, Nat.add(yt8, zt8))}, Tour.Counts{Nat.add(xf1, Nat.add(yf1, zf1)), Nat.add(xf2, Nat.add(yf2, zf2)), Nat.add(xf3, Nat.add(yf3, zf3)), Nat.add(xf4, Nat.add(yf4, zf4)), Nat.add(xf5, Nat.add(yf5, zf5)), Nat.add(xf6, Nat.add(yf6, zf6)), Nat.add(xf7, Nat.add(yf7, zf7)), Nat.add(xf8, Nat.add(yf8, zf8))}, Tour.Counts{Nat.add(xs1, Nat.add(ys1, zs1)), Nat.add(xs2, Nat.add(ys2, zs2)), Nat.add(xs3, Nat.add(ys3, zs3)), Nat.add(xs4, Nat.add(ys4, zs4)), Nat.add(xs5, Nat.add(ys5, zs5)), Nat.add(xs6, Nat.add(ys6, zs6)), Nat.add(xs7, Nat.add(ys7, zs7)), Nat.add(xs8, Nat.add(ys8, zs8))}, Nat.add(xu, Nat.add(yu, zu)), counts_cong(Nat.add(Nat.add(xt1, yt1), zt1), Nat.add(Nat.add(xt2, yt2), zt2), Nat.add(Nat.add(xt3, yt3), zt3), Nat.add(Nat.add(xt4, yt4), zt4), Nat.add(Nat.add(xt5, yt5), zt5), Nat.add(Nat.add(xt6, yt6), zt6), Nat.add(Nat.add(xt7, yt7), zt7), Nat.add(Nat.add(xt8, yt8), zt8), Nat.add(xt1, Nat.add(yt1, zt1)), Nat.add(xt2, Nat.add(yt2, zt2)), Nat.add(xt3, Nat.add(yt3, zt3)), Nat.add(xt4, Nat.add(yt4, zt4)), Nat.add(xt5, Nat.add(yt5, zt5)), Nat.add(xt6, Nat.add(yt6, zt6)), Nat.add(xt7, Nat.add(yt7, zt7)), Nat.add(xt8, Nat.add(yt8, zt8)), nat_add_assoc(xt1, yt1, zt1), nat_add_assoc(xt2, yt2, zt2), nat_add_assoc(xt3, yt3, zt3), nat_add_assoc(xt4, yt4, zt4), nat_add_assoc(xt5, yt5, zt5), nat_add_assoc(xt6, yt6, zt6), nat_add_assoc(xt7, yt7, zt7), nat_add_assoc(xt8, yt8, zt8)), counts_cong(Nat.add(Nat.add(xf1, yf1), zf1), Nat.add(Nat.add(xf2, yf2), zf2), Nat.add(Nat.add(xf3, yf3), zf3), Nat.add(Nat.add(xf4, yf4), zf4), Nat.add(Nat.add(xf5, yf5), zf5), Nat.add(Nat.add(xf6, yf6), zf6), Nat.add(Nat.add(xf7, yf7), zf7), Nat.add(Nat.add(xf8, yf8), zf8), Nat.add(xf1, Nat.add(yf1, zf1)), Nat.add(xf2, Nat.add(yf2, zf2)), Nat.add(xf3, Nat.add(yf3, zf3)), Nat.add(xf4, Nat.add(yf4, zf4)), Nat.add(xf5, Nat.add(yf5, zf5)), Nat.add(xf6, Nat.add(yf6, zf6)), Nat.add(xf7, Nat.add(yf7, zf7)), Nat.add(xf8, Nat.add(yf8, zf8)), nat_add_assoc(xf1, yf1, zf1), nat_add_assoc(xf2, yf2, zf2), nat_add_assoc(xf3, yf3, zf3), nat_add_assoc(xf4, yf4, zf4), nat_add_assoc(xf5, yf5, zf5), nat_add_assoc(xf6, yf6, zf6), nat_add_assoc(xf7, yf7, zf7), nat_add_assoc(xf8, yf8, zf8)), counts_cong(Nat.add(Nat.add(xs1, ys1), zs1), Nat.add(Nat.add(xs2, ys2), zs2), Nat.add(Nat.add(xs3, ys3), zs3), Nat.add(Nat.add(xs4, ys4), zs4), Nat.add(Nat.add(xs5, ys5), zs5), Nat.add(Nat.add(xs6, ys6), zs6), Nat.add(Nat.add(xs7, ys7), zs7), Nat.add(Nat.add(xs8, ys8), zs8), Nat.add(xs1, Nat.add(ys1, zs1)), Nat.add(xs2, Nat.add(ys2, zs2)), Nat.add(xs3, Nat.add(ys3, zs3)), Nat.add(xs4, Nat.add(ys4, zs4)), Nat.add(xs5, Nat.add(ys5, zs5)), Nat.add(xs6, Nat.add(ys6, zs6)), Nat.add(xs7, Nat.add(ys7, zs7)), Nat.add(xs8, Nat.add(ys8, zs8)), nat_add_assoc(xs1, ys1, zs1), nat_add_assoc(xs2, ys2, zs2), nat_add_assoc(xs3, ys3, zs3), nat_add_assoc(xs4, ys4, zs4), nat_add_assoc(xs5, ys5, zs5), nat_add_assoc(xs6, ys6, zs6), nat_add_assoc(xs7, ys7, zs7), nat_add_assoc(xs8, ys8, zs8)), nat_add_assoc(xu, yu, zu))

law event_sum_append:
  for +xs: List<&2, Tour.Tally>
  for +ys: List<&2, Tour.Tally>
  {Laws.Rule.event_sum(List.append(&2, Tour.Tally, xs, ys)) == Laws.Rule.add_tally(Laws.Rule.event_sum(xs), Laws.Rule.event_sum(ys)) : Tour.Tally}

def event_sum_append(xs, ys):
  match xs:
    case Nil{}:
      Equal.sym(Tour.Tally, Laws.Rule.add_tally(Laws.Rule.no_tally(), Laws.Rule.event_sum(ys)), Laws.Rule.event_sum(ys), add_tally_nothing_left(Laws.Rule.event_sum(ys)))
    case Con{+t, +rest}:
      %Equal.sym(Tour.Tally, Laws.Rule.event_sum(List.append(&2, Tour.Tally, rest, ys)), Laws.Rule.add_tally(Laws.Rule.event_sum(rest), Laws.Rule.event_sum(ys)), event_sum_append(rest, ys)) : {Laws.Rule.add_tally(t, _) == Laws.Rule.add_tally(Laws.Rule.add_tally(t, Laws.Rule.event_sum(rest)), Laws.Rule.event_sum(ys)) : Tour.Tally}
      Equal.sym(Tour.Tally, Laws.Rule.add_tally(Laws.Rule.add_tally(t, Laws.Rule.event_sum(rest)), Laws.Rule.event_sum(ys)), Laws.Rule.add_tally(t, Laws.Rule.add_tally(Laws.Rule.event_sum(rest), Laws.Rule.event_sum(ys))), add_tally_assoc(t, Laws.Rule.event_sum(rest), Laws.Rule.event_sum(ys)))

law event_results_append:
  for +fmt: S.Format
  for +f: Tour.Field
  for +d: Tour.Draw
  for +seed: U32
  for +prefix: U32
  for +xs: List<&2, List<&2, Bool>>
  for +ys: List<&2, List<&2, Bool>>
  {Laws.Rule.event_results(fmt, f, d, seed, prefix, List.append(&2, List<&2, Bool>, xs, ys)) == List.append(&2, Tour.Tally, Laws.Rule.event_results(fmt, f, d, seed, prefix, xs), Laws.Rule.event_results(fmt, f, d, seed, prefix, ys)) : List<&2, Tour.Tally>}

def event_results_append(fmt, f, d, seed, prefix, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+path, +rest}:
      %Equal.sym(List<&2, Tour.Tally>, Laws.Rule.event_results(fmt, f, d, seed, prefix, List.append(&2, List<&2, Bool>, rest, ys)), List.append(&2, Tour.Tally, Laws.Rule.event_results(fmt, f, d, seed, prefix, rest), Laws.Rule.event_results(fmt, f, d, seed, prefix, ys)), event_results_append(fmt, f, d, seed, prefix, rest, ys)) : {(Laws.Rule.event_tally(Tour.Event.play(fmt, f, d, seed, Laws.Rule.number(path, prefix))) <> _) == List.append(&2, Tour.Tally, Laws.Rule.event_results(fmt, f, d, seed, prefix, path <> rest), Laws.Rule.event_results(fmt, f, d, seed, prefix, ys)) : List<&2, Tour.Tally>}
      {==}

law event_results_cons_all:
  for +fmt: S.Format
  for +f: Tour.Field
  for +d: Tour.Draw
  for +seed: U32
  for +b: Bool
  for +prefix: U32
  for +paths: List<&2, List<&2, Bool>>
  {Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(b, paths)) == Laws.Rule.event_results(fmt, f, d, seed, (prefix * 2 + Laws.Rule.bit(b) : U32), paths) : List<&2, Tour.Tally>}

def event_results_cons_all(fmt, f, d, seed, b, prefix, paths):
  match paths:
    case Nil{}:
      {==}
    case Con{+path, +rest}:
      %Equal.sym(List<&2, Tour.Tally>, Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(b, rest)), Laws.Rule.event_results(fmt, f, d, seed, (prefix * 2 + Laws.Rule.bit(b) : U32), rest), event_results_cons_all(fmt, f, d, seed, b, prefix, rest)) : {(Laws.Rule.event_tally(Tour.Event.play(fmt, f, d, seed, Laws.Rule.number(b <> path, prefix))) <> _) == Laws.Rule.event_results(fmt, f, d, seed, (prefix * 2 + Laws.Rule.bit(b) : U32), path <> rest) : List<&2, Tour.Tally>}
      {==}

law one_same:
  for n: Nat
  {Tour.Event.one(n) == Laws.Rule.one(n) : Tour.Counts}

def one_same(n):
  match n:
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 0n:
      {==}
    case 9n+p:
      {==}

law add_counts_same:
  for x: Tour.Counts
  for y: Tour.Counts
  {Tour.Event.add_counts(x, y) == Laws.Rule.add_counts(x, y) : Tour.Counts}

def add_counts_same(x, y):
  match x y:
    case Tour.Counts{x1, x2, x3, x4, x5, x6, x7, x8} Tour.Counts{y1, y2, y3, y4, y5, y6, y7, y8}:
      {==}

law event_add_same:
  for x: Tour.Tally
  for y: Tour.Tally
  {Tour.Event.add(x, y) == Laws.Rule.add_tally(x, y) : Tour.Tally}

def event_add_same(x, y):
  match x y:
    case Tour.Tally{Tour.Counts{xt1, xt2, xt3, xt4, xt5, xt6, xt7, xt8}, Tour.Counts{xf1, xf2, xf3, xf4, xf5, xf6, xf7, xf8}, Tour.Counts{xs1, xs2, xs3, xs4, xs5, xs6, xs7, xs8}, xu} Tour.Tally{Tour.Counts{yt1, yt2, yt3, yt4, yt5, yt6, yt7, yt8}, Tour.Counts{yf1, yf2, yf3, yf4, yf5, yf6, yf7, yf8}, Tour.Counts{ys1, ys2, ys3, ys4, ys5, ys6, ys7, ys8}, yu}:
      {==}

law event_count_same:
  for o: Tour.Outcome
  {Tour.Event.count(o) == Laws.Rule.event_tally(o) : Tour.Tally}

def event_count_same(o):
  match o:
    case Tour.Complete{ga, gb, ra, rb, Tour.Semis{+l1, +l2, +l3, +l4}, r1, r2, +f1, +f2, r, +c}:
      %one_same(c) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{_, Laws.Rule.add_counts(Laws.Rule.one(f1), Laws.Rule.one(f2)), Laws.Rule.add_counts(Laws.Rule.add_counts(Laws.Rule.one(l1), Laws.Rule.one(l2)), Laws.Rule.add_counts(Laws.Rule.one(l3), Laws.Rule.one(l4))), 0n} : Tour.Tally}
      %one_same(f1) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), Laws.Rule.add_counts(_, Laws.Rule.one(f2)), Laws.Rule.add_counts(Laws.Rule.add_counts(Laws.Rule.one(l1), Laws.Rule.one(l2)), Laws.Rule.add_counts(Laws.Rule.one(l3), Laws.Rule.one(l4))), 0n} : Tour.Tally}
      %one_same(f2) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), Laws.Rule.add_counts(Tour.Event.one(f1), _), Laws.Rule.add_counts(Laws.Rule.add_counts(Laws.Rule.one(l1), Laws.Rule.one(l2)), Laws.Rule.add_counts(Laws.Rule.one(l3), Laws.Rule.one(l4))), 0n} : Tour.Tally}
      %one_same(l1) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), Laws.Rule.add_counts(Tour.Event.one(f1), Tour.Event.one(f2)), Laws.Rule.add_counts(Laws.Rule.add_counts(_, Laws.Rule.one(l2)), Laws.Rule.add_counts(Laws.Rule.one(l3), Laws.Rule.one(l4))), 0n} : Tour.Tally}
      %one_same(l2) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), Laws.Rule.add_counts(Tour.Event.one(f1), Tour.Event.one(f2)), Laws.Rule.add_counts(Laws.Rule.add_counts(Tour.Event.one(l1), _), Laws.Rule.add_counts(Laws.Rule.one(l3), Laws.Rule.one(l4))), 0n} : Tour.Tally}
      %one_same(l3) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), Laws.Rule.add_counts(Tour.Event.one(f1), Tour.Event.one(f2)), Laws.Rule.add_counts(Laws.Rule.add_counts(Tour.Event.one(l1), Tour.Event.one(l2)), Laws.Rule.add_counts(_, Laws.Rule.one(l4))), 0n} : Tour.Tally}
      %one_same(l4) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), Laws.Rule.add_counts(Tour.Event.one(f1), Tour.Event.one(f2)), Laws.Rule.add_counts(Laws.Rule.add_counts(Tour.Event.one(l1), Tour.Event.one(l2)), Laws.Rule.add_counts(Tour.Event.one(l3), _)), 0n} : Tour.Tally}
      %add_counts_same(Tour.Event.one(f1), Tour.Event.one(f2)) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), _, Laws.Rule.add_counts(Laws.Rule.add_counts(Tour.Event.one(l1), Tour.Event.one(l2)), Laws.Rule.add_counts(Tour.Event.one(l3), Tour.Event.one(l4))), 0n} : Tour.Tally}
      %add_counts_same(Tour.Event.one(l1), Tour.Event.one(l2)) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), Tour.Event.add_counts(Tour.Event.one(f1), Tour.Event.one(f2)), Laws.Rule.add_counts(_, Laws.Rule.add_counts(Tour.Event.one(l3), Tour.Event.one(l4))), 0n} : Tour.Tally}
      %add_counts_same(Tour.Event.one(l3), Tour.Event.one(l4)) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), Tour.Event.add_counts(Tour.Event.one(f1), Tour.Event.one(f2)), Laws.Rule.add_counts(Tour.Event.add_counts(Tour.Event.one(l1), Tour.Event.one(l2)), _), 0n} : Tour.Tally}
      %add_counts_same(Tour.Event.add_counts(Tour.Event.one(l1), Tour.Event.one(l2)), Tour.Event.add_counts(Tour.Event.one(l3), Tour.Event.one(l4))) : {Tour.Event.count(Tour.Complete{ga, gb, ra, rb, Tour.Semis{l1, l2, l3, l4}, r1, r2, f1, f2, r, c}) == Tour.Tally{Tour.Event.one(c), Tour.Event.add_counts(Tour.Event.one(f1), Tour.Event.one(f2)), _, 0n} : Tour.Tally}
      {==}
    case Tour.Unfinished{}:
      {==}

# L30, by induction on the number of bits, exactly as L14.
def Laws.L30_every_tournament_counted_once(d0, fmt, f, d, seed, prefix):
  match d0:
    case 0n:
      %Equal.sym(Tour.Tally, Tour.Event.count(Tour.Event.play(fmt, f, d, seed, prefix)), Laws.Rule.event_tally(Tour.Event.play(fmt, f, d, seed, prefix)), event_count_same(Tour.Event.play(fmt, f, d, seed, prefix))) : {_ == Laws.Rule.event_sum(Laws.Rule.event_results(fmt, f, d, seed, prefix, [[]])) : Tour.Tally}
      Equal.sym(Tour.Tally, Laws.Rule.add_tally(Laws.Rule.event_tally(Tour.Event.play(fmt, f, d, seed, prefix)), Laws.Rule.no_tally()), Laws.Rule.event_tally(Tour.Event.play(fmt, f, d, seed, prefix)), add_tally_nothing_right(Laws.Rule.event_tally(Tour.Event.play(fmt, f, d, seed, prefix))))
    case 1n+p:
      %Equal.sym(List<&2, Tour.Tally>, Laws.Rule.event_results(fmt, f, d, seed, prefix, List.append(&2, List<&2, Bool>, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p)), Laws.Rule.cons_all(True{}, Laws.Rule.paths(p)))), List.append(&2, Tour.Tally, Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p))), Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p)))), event_results_append(fmt, f, d, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p)), Laws.Rule.cons_all(True{}, Laws.Rule.paths(p)))) : {Tour.Event.add(Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 0 : U32)), Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.event_sum(_) : Tour.Tally}
      %Equal.sym(Tour.Tally, Laws.Rule.event_sum(List.append(&2, Tour.Tally, Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p))), Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))))), Laws.Rule.add_tally(Laws.Rule.event_sum(Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p)))), Laws.Rule.event_sum(Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))))), event_sum_append(Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p))), Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))))) : {Tour.Event.add(Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 0 : U32)), Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 1 : U32))) == _ : Tour.Tally}
      %Equal.sym(List<&2, Tour.Tally>, Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(False{}, Laws.Rule.paths(p))), Laws.Rule.event_results(fmt, f, d, seed, (prefix * 2 + Laws.Rule.bit(False{}) : U32), Laws.Rule.paths(p)), event_results_cons_all(fmt, f, d, seed, False{}, prefix, Laws.Rule.paths(p))) : {Tour.Event.add(Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 0 : U32)), Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.add_tally(Laws.Rule.event_sum(_), Laws.Rule.event_sum(Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))))) : Tour.Tally}
      %Equal.sym(List<&2, Tour.Tally>, Laws.Rule.event_results(fmt, f, d, seed, prefix, Laws.Rule.cons_all(True{}, Laws.Rule.paths(p))), Laws.Rule.event_results(fmt, f, d, seed, (prefix * 2 + Laws.Rule.bit(True{}) : U32), Laws.Rule.paths(p)), event_results_cons_all(fmt, f, d, seed, True{}, prefix, Laws.Rule.paths(p))) : {Tour.Event.add(Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 0 : U32)), Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.add_tally(Laws.Rule.event_sum(Laws.Rule.event_results(fmt, f, d, seed, (prefix * 2 + 0 : U32), Laws.Rule.paths(p))), Laws.Rule.event_sum(_)) : Tour.Tally}
      %Laws.L30_every_tournament_counted_once(p, fmt, f, d, seed, (prefix * 2 + 0 : U32)) : {Tour.Event.add(Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 0 : U32)), Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.add_tally(_, Laws.Rule.event_sum(Laws.Rule.event_results(fmt, f, d, seed, (prefix * 2 + 1 : U32), Laws.Rule.paths(p)))) : Tour.Tally}
      %Laws.L30_every_tournament_counted_once(p, fmt, f, d, seed, (prefix * 2 + 1 : U32)) : {Tour.Event.add(Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 0 : U32)), Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 1 : U32))) == Laws.Rule.add_tally(Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 0 : U32)), _) : Tour.Tally}
      event_add_same(Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 0 : U32)), Tour.Event.tally(p, fmt, f, d, seed, (prefix * 2 + 1 : U32)))

