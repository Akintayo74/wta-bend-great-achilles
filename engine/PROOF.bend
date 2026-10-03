import Base
import ./scoring.bend as S
import ./LAWS.bend as Laws

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