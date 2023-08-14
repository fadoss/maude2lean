--
-- Proof that a deadlock state is always reachable in a dining philosophers
-- example used for model checking in previous works
--
-- We proceed in two steps:
--  1. A term where every philosopher has taken the right fork is reachable
--     from the initial state (easy)
--  2. No rewrite is possible from such a term (more complicated)
--

import .philosophers

--
-- Initial definitions
--

-- Convert a natural number from Lean to Maude
def nat_l2m : ℕ → Maude.kNat
  | 0            := Maude.kNat.zero
  | (nat.succ n) := Maude.kNat.s (nat_l2m n)

-- Every such natural number has sort Nat
lemma nat_l2m_has_sort_nat (n : ℕ) : (nat_l2m n).has_sort Maude.MSort.Nat :=
begin
  induction n with m h,
  case nat.zero {
    simp [nat_l2m],
  },
  case nat.succ {
    simp [nat_l2m, h],
  }
end

--
-- Proof of (1)
--

namespace Maude.kList

/-- every_phil_has_right_fork holds on lists where every philosopher has taken
    the right fork and there is no spare forks -/
def every_phil_has_right_fork : Maude.kList → Prop
  | (join a b)      := (every_phil_has_right_fork a) ∧ (every_phil_has_right_fork b)
  | (phil l id r)   := l =E o ∧ r =E fork
  | (initialList n) := n =E Maude.kNat.zero
  | empty           := true
  | _               := false

/-- The equation for initialList with Lean natural numbers -/
lemma initialList_step (n : ℕ) : (initialList (nat_l2m n.succ)) =E
    (join (initialList (nat_l2m n)) (join (phil o (nat_l2m n) o) fork)) :=
begin
  rw nat_l2m,
  apply eq_initialList₁,
  exact nat_l2m_has_sort_nat n,
end

/-- The list of the initial state can be rewritten to another state where
    every philosopher has the right fork (the property does not hold for
    the left fork since the conext is needed for kTable.rl_left) -/
theorem has_deadlock (n : ℕ) : ∃ t, (initialList (nat_l2m n)) =>* t
                                     ∧ t.every_phil_has_right_fork  :=
begin
  induction n with m h,
  case nat.zero {
    existsi Maude.kList.empty,
    split,
    -- empty is reachable (in zero steps)
    apply rw_star.refl,
    simp [nat_l2m, eq_initialList₀],
    -- every philosopher (there is none) has the right fork in empty
    simp [every_phil_has_right_fork],
  },
  case nat.succ {
    cases h with t h,
    existsi (join t (phil o (nat_l2m m) fork)),
    split,
    -- The expression above is reachable

    transitivity (initialList (nat_l2m m)).join ((o.phil (nat_l2m m) o).join fork),
    exact (rw_star.refl (initialList_step m)),
      -- The first philosophers are done by induction hypothesis
      transitivity (t.join ((o.phil (nat_l2m m) o).join fork)),
      apply rw_star_sub_join₀,
      exact h.left,
      -- The last philosopher is done by applying the right rule
      apply rw_star_sub_join₁,
      apply rw_star.step,
      apply rl_right,
      exact o_decl,
      exact nat_l2m_has_sort_nat m,
    -- The expression have saatisfies every_phil_has_right_fork
    simp [every_phil_has_right_fork, h],
    split,
    refl,
    refl,
  }
end

end Maude.kList

namespace Maude.kTable

/-- Extension of every_phil_has_right_fork to kTable -/
def every_phil_has_right_fork : Maude.kTable → Prop
  | (table l)   := Maude.kList.every_phil_has_right_fork l
  | (initial n) := n =E Maude.kNat.zero

/-- The initial state can be rewritten to a term where every philosopher
    has a right fork for any number of philosophers -/
theorem has_deadlock (n : ℕ) : ∃ t, (initial (nat_l2m n)) =>* t
                                     ∧ t.every_phil_has_right_fork  :=
begin
  have h := Maude.kList.has_deadlock n,
  cases h with l h,
  existsi (table l),
  split, {
    -- < l > is reachable
    transitivity (table (Maude.kList.initialList (nat_l2m n))),
    apply rw_star.refl,
    apply eq_initial,
    exact nat_l2m_has_sort_nat n,
    exact rw_star_sub_table h.left, },
    -- < l > satisfies every_phil_has_right_fork
    rw every_phil_has_right_fork,
    exact h.right,
end

end Maude.kTable

--
-- Proof of (2)
--

namespace Maude.kNat

/-- No rule rewrite is possible in the Nat kind -/
lemma no_step {n m : Maude.kNat} : ¬ (n =>1 m) :=
begin
  intro h,
  induction h,
  all_goals { contradiction },
end

/-- Zero is not a successor (we define this as an axiom because the Nat module
    of Maude does not include equations because the operations are implemented
    internally) -/
axiom zero_neqe_s (n : Maude.kNat) : ¬ (n.s =E zero)

end Maude.kNat

namespace Maude.kList

/-- List without philosophers -/
def no_phil : Maude.kList → Prop
  | (join a b)      := no_phil a ∧ no_phil b
  | (initialList n) := n =E Maude.kNat.zero
  | (phil _ _ _)    := false
  | _               := true

/-- List combining given argument with identity elements -/
def extends_with_id (e : Maude.kList) : Maude.kList → Prop
  | (join a b)      := extends_with_id a ∧ extends_with_id b
  | (initialList n) := n =E Maude.kNat.zero
  | empty           := true
  | l               := l = e

/-- extend_with_id fork is closed under =A -/
lemma fork_aclass {a b : Maude.kList} (h : a =A b) :
  extends_with_id fork a ↔ extends_with_id fork b :=
begin
  induction h,
  -- Remove trivial cases
  any_goals {simp [*, extends_with_id, and.assoc]},
end

/-- no_phil is closed under =A -/
lemma no_phil_aclass {a b : Maude.kList} (h : a =A b) : no_phil a ↔ no_phil b :=
begin
  induction h,
  any_goals {simp [*, no_phil, and.assoc]},
end

/-- extends_with_id fork is closed under =E -/
lemma fork_eclass {a b : Maude.kList} (h : a =E b) :
  extends_with_id fork a ↔ extends_with_id fork b :=
begin
  induction h,
  -- Remove all trivial cases
  any_goals {simp [extends_with_id, and.assoc]},
  any_goals {cc},
  case eqe.from_eqa : _ _ h {
    exact fork_aclass h,
  },
  case eqe.eqe_initialList : l r h {
    simp [*],
  },
  case eqe.eq_initialList₁ : n {
    exact Maude.kNat.zero_neqe_s n,
  }
end

/-- no_phil is closed under =E -/
lemma no_phil_eclass {a b : Maude.kList} (h : a =E b) : no_phil a ↔ no_phil b :=
begin
  induction h,
  -- Remove all trivial cases
  any_goals {repeat {rw no_phil at *}},
  any_goals {cc},
  case eqe.from_eqa : _ _ h {
    exact no_phil_aclass h,
  },
  case eqe.eqe_initialList : l r hlr {
    simp [*],
  },
  case eqe.eq_initialList₁ : n {
    simp,
    exact Maude.kNat.zero_neqe_s n,
  }
end

/-- no_phil states are deadlocked -/
lemma no_phil_deadlock (a b : Maude.kList) (hp : no_phil a) : ¬ (a =>1 b) :=
begin
  intro h,
  induction h,
  -- Remove trivial cases
  any_goals {repeat {rw no_phil at *}},
  any_goals {cc},
  -- Handle remaining cases
  case rw_one.eqe_left : _ _ _ h _ h_ff {
    exact h_ff ((no_phil_eclass h).mp hp),
  },
  case rw_one.sub_initialList : _ _ h {
    exact Maude.kNat.no_step h,
  },
end

/-- fork and empty hand are not equivalent modulo equations -/
lemma fork_neqe_o : ¬ (fork =E o) :=
begin
  intro h1,
  have h2 := fork_eclass h1,
  simp [extends_with_id] at h2,
  cc,
end

/-- every_phil_has_right_fork is closed under =A -/
def ephrf_aclass {a b : Maude.kList} (h : a =A b) :
  every_phil_has_right_fork a ↔ every_phil_has_right_fork b :=
begin
  induction h,
  any_goals {simp [*, every_phil_has_right_fork]},
  case eqa.join_assoc {
    rw and.assoc,
  }
end

/-- every_phil_has_right_fork is closed under =E -/
lemma ephrf_eclass {a b : Maude.kList} (h : a =E b) :
  every_phil_has_right_fork a ↔ every_phil_has_right_fork b :=
begin
  induction h,
  any_goals {simp [*, every_phil_has_right_fork]},
  case eqe.from_eqa : _ _ h {
    exact ephrf_aclass h,
  },
  case eqe.eq_initialList₁ : n {
    exact Maude.kNat.zero_neqe_s n,
  }
end

/-- every_phil_has_right_fork states are deadlocked -/
lemma ephrf_deadlock (a b : Maude.kList) (h : every_phil_has_right_fork a) :
  ¬ (a.rw_one b) :=
begin
  intro hs,
  induction hs,
  case rw_one.eqe_left : _ _ _ h_xEy _ h_ff {
    exact h_ff ((ephrf_eclass h_xEy).mp h),
  },
  case rw_one.eqe_right : _ _ _ _ _ ih {
    exact ih h,
  },
  case rw_one.sub_phil₀ : id r l r' hlr h_ff {
    rw every_phil_has_right_fork at h,
    have hl : no_phil l, {
      apply (no_phil_eclass h.left).mpr,
      rw no_phil,
      trivial,
    },
    exact no_phil_deadlock _ _ hl hlr,
  },
  case rw_one.sub_phil₁ : _ _ _ _ hid {
    exact Maude.kNat.no_step hid,
  },
  case rw_one.sub_phil₂ : l id r r' hlr h_ff {
    rw every_phil_has_right_fork at h,
    have hr : no_phil r, {
      apply (no_phil_eclass h.right).mpr,
      rw no_phil,
      trivial,
    },
    exact no_phil_deadlock _ _ hr hlr,
  },
  case rw_one.sub_join₀ {
    rw every_phil_has_right_fork at h,
    exact hs_x h.left,
  },
  case rw_one.sub_join₁ {
    rw every_phil_has_right_fork at h,
    exact hs_x h.right,
  },
  case rw_one.sub_initialList : _ _ hl {
    exact Maude.kNat.no_step hl,
  },
  case rw_one.rl_left {
    repeat {rw every_phil_has_right_fork at h},
    exact h.left,
  },
  case rw_one.rl_right {
    repeat {rw every_phil_has_right_fork at h},
    exact h.right,
  },
  case rw_one.rl_release {
    rw every_phil_has_right_fork at h,
    exact fork_neqe_o h.left,
  },
end

end Maude.kList

namespace Maude.kTable

/-- every_phil_has_right_fork is closed under =A on kTable -/
def ephrf_aclass {a b : Maude.kTable} (h : a =A b) :
  every_phil_has_right_fork a ↔ every_phil_has_right_fork b :=
begin
  induction h,
  -- Remove trivial goals
  any_goals {repeat {rw every_phil_has_right_fork at *}},
  any_goals {cc},
  -- Remaining goals
  case eqa.eqa_table : l r hlr {
    exact Maude.kList.ephrf_aclass hlr,
  },
  case eqa.eqa_initial : l r hlr {
    simp [hlr],
  },
end

/-- every_phil_has_right_fork is closed under =A on kTable -/
def ephrf_eclass {a b : Maude.kTable} (h : a =E b) :
  every_phil_has_right_fork a ↔ every_phil_has_right_fork b :=
begin
  induction h,
  -- Remove trivial goals
  any_goals {repeat {rw every_phil_has_right_fork at *}},
  any_goals {cc},
  -- Remaining goals
  case eqe.from_eqa : _ _ h {
    exact ephrf_aclass h,
  },
  case eqe.eqe_table : _ _ h {
    exact Maude.kList.ephrf_eclass h,
  },
  case eqe.eqe_initial : l r hlr {
    simp [hlr],
  },
  case eqe.eq_initial {
    rw Maude.kList.every_phil_has_right_fork,
  },
  case eqe.eq_table {
    repeat {rw Maude.kList.every_phil_has_right_fork},
    cc,
  },
end

/-- every_phil_has_right_fork states are deadlocked -/
lemma ephrf_deadlock (a b : Maude.kTable) (hf : a.every_phil_has_right_fork) :
  ¬ (a =>1 b) :=
begin
  intro h,
  induction h,
  case rw_one.eqe_left : l m r hlm hmr h_ff {
    exact h_ff ((ephrf_eclass hlm).mp hf),
  },
  case rw_one.eqe_right : l m r hlm hmr h_ff {
    exact h_ff hf,
  },
  case rw_one.sub_table : _ _ h_step {
    exact Maude.kList.ephrf_deadlock _ _ hf h_step,
  },
  case rw_one.rl_left {
    repeat {rw Maude.kList.every_phil_has_right_fork at h},
    exact hf.right.right,
  },
  case rw_one.sub_initial : l r hlr {
    exact Maude.kNat.no_step hlr,
  },
end

end Maude.kTable
