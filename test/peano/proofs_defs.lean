--
-- Proof of the associativity of the sum of Peano numbers specified in Maude
-- (with-defined-as-defs version)
--
-- This proof is the same as demos.lean but for a translation of the PEANO
-- module where derived operators are represented as Lean definitions. As a
-- result, sum is no longer part of the inductive type kNat, but a function
-- at the Lean level whose applications are related to their definitions by
-- standard Lean equality.
--

import .peano_defs
open Maude

/-- The sum of Nat numbers is associative -/
theorem sum_assoc (n m o : kNat) : n.sum (m.sum o) = (n.sum m).sum o :=
begin
  induction o,
  case kNat.zero {
    simp,
  },
  case kNat.s : o ih {
    simp,
    exact ih,
  },
end

/-- Zero is neutral also to the left -/
lemma zero_sum (n : kNat) : kNat.zero.sum n = n :=
begin
  induction n,
  case kNat.zero {
    simp,
  },
  case kNat.s : m hm {
    simp [hm],
  },
end

/-- The equation for the sum of a successor also works to the left -/
lemma s_sum (n m : kNat) : n.s.sum m = (n.sum m).s :=
begin
  induction m,
  case kNat.zero {
    simp,
  },
  case kNat.s : m hm {
    simp [hm],
  },
end

/-- The sum of Nat numbers is commutative (on constructor terms) -/
lemma sum_comm (n m : kNat) : n.sum m = m.sum n :=
begin
  induction m,
  case kNat.zero {
    simp [zero_sum n],
  },
  case kNat.s : o ih {
    simp [ih], -- equational reduction and induction hypothesis in the LHS
    simp [s_sum o n], -- apply s_sum on the RHS
  },
end
