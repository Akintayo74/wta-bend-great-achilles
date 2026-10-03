import Base
import ./scoring.bend as S
import ./LAWS.bend as Laws
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
