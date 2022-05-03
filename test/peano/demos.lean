--
-- Proof of the associativity of the sum of Peano numbers specified in Maude
--
-- The start by proving the sufficient completeness of the definition of sum,
-- i.e. that a constructor term can always be reached from any term. Then,
-- associativity is proven for constructor terms and the proof is extended for
-- any term.
--

import .peano
open Maude

-- Let the + sign be used for the sum (disabled, since interferes with simp)
-- instance : has_add Maude.kNat := ⟨ Maude.kNat.sum ⟩ 

/-- All elements in the Nat kind have sort Nat
    (not in use now, since the error-free kind optimization is enabled) -/
lemma all_are_nat (n : kNat) : n ⊳ MSort.Nat :=
begin
  induction n with m h _ _ h1 h2,
  all_goals {simp [*]},
end

/-- Constructor terms other than zero are successors -/
lemma zero_or_succ (n : kNat) (hc : n.ctor_only) (hz : n ≠ kNat.zero) :
        ∃ m : kNat, n = m.s :=
begin
  cases n,
  case kNat.zero {
    contradiction,
  },
  case kNat.s {
    existsi n,
    refl,
  },
  case kNat.sum {
    rw kNat.ctor_only at hc,
    contradiction,
  },
end

/-- Size of a term in the Nat kind -/
def Maude.kNat.size : kNat → ℕ
  | kNat.zero      := 0
  | (kNat.s n)     := n.size.succ
  | (kNat.sum n m) := (n.size + m.size).succ

-- Lemmas relating the size of the sum and its operands

lemma sum_l_smaller (l r : kNat) : l.size.succ ≤ (l.sum r).size :=
begin
  rw Maude.kNat.size,
  apply nat.succ_le_succ,
  exact nat.le_add_right _ _,
end

lemma sum_r_smaller (l r : kNat) : r.size.succ ≤ (l.sum r).size :=
begin
  rw Maude.kNat.size,
  apply nat.succ_le_succ,
  exact nat.le_add_left _ _,
end

/-- Any term can be reduced to a (smaller) constructor term (auxiliary lemma) -/
lemma sc_nat_aux (n : kNat) (r : ℕ) (hs: n.size ≤ r) :
        ∃ m, n =E m ∧ m.ctor_only ∧ m.size ≤ n.size :=
begin
  induction r generalizing n,
  case nat.zero {
    cases n,
    case kNat.zero {
      existsi kNat.zero,
      simp [kNat.ctor_only, le_refl],
    },
    case kNat.s {
      rw Maude.kNat.size at hs,
      have nhs := nat.not_succ_le_zero n.size,
      contradiction,
    },
    case kNat.sum : l r {
      rw Maude.kNat.size at hs,
      have nhs := nat.not_succ_le_zero _,
      contradiction,
    },
  },
  case nat.succ : rn ih {
    cases n,
    case kNat.zero {
      existsi kNat.zero,
      simp [kNat.ctor_only, le_refl],
    },
    case kNat.s {
      rw Maude.kNat.size at hs,
      have hs' := nat.le_of_succ_le_succ hs,
      cases (ih n hs'),
      existsi w.s,
      split,
      simp [h.left],
      rw kNat.ctor_only,
      split,
      exact h.right.left,
      rw [Maude.kNat.size, Maude.kNat.size],
      apply nat.succ_le_succ,
      exact h.right.right,
    },
    case kNat.sum : l r {
      -- (1) Find a constructor term 'cr' for 'r'
      have r_smaller : r.size ≤ rn,
        apply nat.le_of_succ_le_succ,
        transitivity (l.sum r).size,
        exact sum_r_smaller _ _,
        exact hs,
      -- r_smaller is done
      cases (ih r r_smaller) with cr h_cr,
      -- (2) Prove (l.sum r) =E (l.sum cr) for future use
      have sum_cr_r : (l.sum r) =E l.sum cr,
        simp [h_cr.left],
      -- sum_cr_r is done
      -- (3) Distinguish whether cr is zero or not (to apply an equation)
      by_cases (cr = kNat.zero),
      -- [cr = 0] the constructor term for the sum is that of l (cl)
      have l_smaller : l.size ≤ rn,
        apply nat.le_of_succ_le_succ,
        transitivity (l.sum r).size,
        exact sum_l_smaller _ _,
        exact hs,
      -- l_smaller is done
      cases (ih l l_smaller) with cl h_cl,
      existsi cl,
      split,
      -- equivalent modulo equations
      rw h at sum_cr_r,
      simp [sum_cr_r],
      exact h_cl.left,
      -- constructor only
      split,
      exact h_cl.right.left,
      -- size bound
      rw Maude.kNat.size,
      apply nat.le_succ_of_le,
      transitivity l.size,
      exact h_cl.right.right,
      apply nat.le_add_right,
      -- [cr ≠ 0] First, we show that cr = cm.s for some cm, then
      -- we apply the second equation for the sum and find a constr
      -- term 'cw' for l.sum cm, and finally cw.s is what we want
      cases (zero_or_succ cr h_cr.right.left h) with cm h_cm,
      have sum_smaller : (l.sum cm).size <= rn,
        rw Maude.kNat.size,
        rw Maude.kNat.size at hs,
        transitivity l.size + cr.size,
        rw [h_cm, Maude.kNat.size, nat.add_succ],
        transitivity l.size + r.size,
        apply nat.add_le_add_left,
        exact h_cr.right.right,
        apply nat.le_of_succ_le_succ,
        exact hs,
      -- sum_smaller is done
      cases (ih (l.sum cm) sum_smaller) with cw h_cw,
      existsi cw.s,
      split,
      -- equivalent modulo equations
      simp [*],
      -- constructor only
      split,
      rw kNat.ctor_only,
      exact h_cw.right.left,
      -- size bound
      repeat {rw Maude.kNat.size},
      apply nat.succ_le_succ,
      transitivity (l.sum cm).size,
      exact h_cw.right.right,
      rw Maude.kNat.size,
      rw ← nat.add_succ,
      apply nat.add_le_add_left,
      transitivity cr.size,
      rw [h_cm, Maude.kNat.size],
      exact h_cr.right.right,
    },
  },
end

/-- The defined operators in Nat (sum) are sufficient complete -/
theorem sc_nat (n : kNat) : ∃ m, n =E m ∧ m.ctor_only :=
begin
  cases (sc_nat_aux n n.size (nat.le_refl n.size)),
  existsi w,
  simp [h],
end

/-- The sum of Nat numbers is associative on a constructor term -/
lemma sum_assoc_aux (n m o : kNat) (oh : o.ctor_only) :
        n.sum (m.sum o) =E (n.sum m).sum o :=
begin
  induction o,
  case kNat.zero {
    simp,
  },
  case kNat.s : o ih {
    simp,
    apply kNat.eqe_s,
    rw kNat.ctor_only at oh,
    exact ih oh,
  },
  case kNat.sum : l r hl hr {
    rw kNat.ctor_only at oh,
    contradiction,
  },
end

/-- The sum of Nat numbers is associative -/
theorem sum_assoc (n m o : kNat) : n.sum (m.sum o) =E (n.sum m).sum o :=
begin
  cases (sc_nat o) with w,
  simp [h.left],
  exact sum_assoc_aux n m w h.right,
end

/-- Zero is neutral also to the left -/
lemma zero_sum (n : kNat) (hc : n.ctor_only) : kNat.zero.sum n =E n :=
begin
  induction n,
  case kNat.zero {
    simp,
  },
  case kNat.s : m hm {
    rw kNat.ctor_only at hc,
    simp [*],
  },
  case kNat.sum {
    rw kNat.ctor_only at hc,
    contradiction,
  },
end
