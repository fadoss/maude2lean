--
-- Proof that consensus can be reached from any configuration in this
-- population protocol and counterexample showing that not every possible
-- execution arrives to consensus. As extension, we could prove that
-- all fair executions arrive to consensus.
--
-- First, we define consensus with a Lean predicate and a function count
-- (of the number of ninjas of each kind) that will be very relevant in
-- the whole proof, and then we introduce some auxiliary lemmas. The proof
-- of the reachable consensus starts around line 470 and the counterexample
-- around line 800.
--

import .ninjas
open Maude

-- Make Lean infer than equality is decidable for kMode and kVote
attribute [derive decidable_eq] kMode kVote

-- Is there consensus for a given vote v?
def consensus_for (v: kVote) : kGarden → Prop
  | kGarden.empty       := true
  | (kGarden.join l r)  := consensus_for l ∧ consensus_for r
  | (kGarden.ninja _ w) := w = v

-- Is there consensus?
def consensus (g : kGarden) : Prop :=
  (consensus_for kVote.Y g) ∨ (consensus_for kVote.N g)

-- The other vote (i.e. negation)
def Maude.kVote.other : kVote → kVote
  | kVote.Y := kVote.N
  | kVote.N := kVote.Y

-- How many ninjas with the current mode and vote are there?
def count (m : kMode) (v : kVote) : kGarden → ℕ
  | kGarden.empty         := 0
  | (kGarden.join l r)    := count l + count r
  | (kGarden.ninja m' v') := (if m = m' ∧ v = v' then 1 else 0)

-- Relation between counts and consensus
lemma zero_count_consensus {g : kGarden} {v : kVote}
  (ha : count kMode.A v g = 0) (hp : count kMode.P v g = 0)
  : consensus_for v.other g :=
begin
  induction g with m w,
  -- Consensus hold trivially in an empty configuration
  case kGarden.empty {
    rw consensus_for,
    trivial,
  },
  -- There is always consensus with a single ninja, but perhaps not the right one
  case kGarden.ninja {
    simp only [consensus_for],
    by_cases he : v = w,
    {
      -- This is not possible because count would be positive for one mode
      simp [he, count] at ha hp,
      cases m,
      all_goals { contradiction, },
    },
    {
      -- If the votes are different, the goal (w = v.other) holds,
      -- but we need to do a case distinction to conclude it
      cases v; -- ; means "apply the next tactic to all goals spawned by the statement"
      cases w,
      any_goals { simp [Maude.kVote.other], },
      any_goals { contradiction, },
    }
  },
  case kGarden.join : l r hl hr {
    -- By definition, we must prove that there is consensus for v in both sides
    rw count at *,
    rw consensus_for,
    -- By the statement hypothesis, a sum of two non-negative numbers is zero,
    -- so both should be zero and we can apply induction hypothesis 
    split,
    {
      exact hl (nat.eq_zero_of_add_eq_zero_right ha)
               (nat.eq_zero_of_add_eq_zero_right hp),
    },
    {
      exact hr (nat.eq_zero_of_add_eq_zero_left ha)
               (nat.eq_zero_of_add_eq_zero_left hp),
    }
  },
end

-- Equality modulo axioms in kMode means syntactic equality
lemma mode_eqa_eq {m₁ m₂ : kMode} (h : m₁ =A m₂) : m₁ = m₂ :=
begin
  induction h,
  case kMode.eqa.refl { refl, },
  all_goals { simp only [*], },
end

-- Equality modulo axioms in kVote means syntactic equality
lemma vote_eqa_eq {v₁ v₂ : kVote} (h : v₁ =A v₂) : v₁ = v₂ :=
begin
  induction h,
  case kVote.eqa.refl { refl, },
  all_goals { simp only [*], },
end

-- Count is invariant by =A
lemma count_eqa {g c : kGarden} (m : kMode) (v : kVote) (h : g =A c)
  : count m v g = count m v c :=
begin
  -- The proof is a straighforward induction
  induction h,
  case kGarden.eqa.refl { refl, },
  case kGarden.eqa.symm : _ _ _ ih {
    symmetry,
    exact ih,
  },
  case kGarden.eqa.trans : _ _ _ _ _ h₁ h₂ {
    exact eq.trans h₁ h₂,
  },
  case kGarden.eqa.eqa_ninja : _ _ _ _ h₁ h₂ {
    rw [mode_eqa_eq h₁, vote_eqa_eq h₂],
  },
  case kGarden.eqa.eqa_join : _ _ _ _ _ _ h₁ h₂  {
    simp only [count, h₁, h₂],
  },
  case kGarden.eqa.join_comm {
    simp only [count, nat.add_comm],
  },
  case kGarden.eqa.join_assoc {
    simp only [count, nat.add_assoc],
  },
  case kGarden.eqa.join_left_id {
    simp only [count, nat.zero_add],
  },
  case kGarden.eqa.join_right_id {
    simp only [count, nat.add_zero],
  },
end

-- count in a ninja is positive only if their arguments coincide
lemma count_ninja {m m' : kMode} {v v' : kVote}
  (h : count m v (kGarden.ninja m' v') > 0) : m = m' ∧ v = v' :=
begin
  rw count at h,
  by_cases hc : m = m' ∧ v = v',
  { exact hc, },
  { simp [hc] at h, have no_h := nat.lt_irrefl 0, contradiction, },
end

-- If the count of join is positive, so is one of its branches
lemma count_join_pos {l r : kGarden} {m : kMode} {v : kVote} (h : count m v (l.join r) > 0)
  : count m v l > 0 ∨ count m v r > 0 :=
begin
  rw count at h,
  by_cases hc : count m v l > 0,
  {
    simp only [hc, or.inl],
  },
  {
    -- If the count is not positive, it must be zero and the other addend must be positive
    have count_zero : count m v l = 0 := or.resolve_right (nat.eq_zero_or_pos _) hc,
    simp only [count_zero, nat.zero_add] at h,
    simp only [h, or.inr],
  },
end

-- Any ninja can appear first in the multiset
lemma ninja_first {g : kGarden} {m : kMode} {v : kVote} (h : count m v g > 0)
  : ∃ c, g =A (kGarden.ninja m v).join c :=
begin
  induction g,
  -- An empty garden cannot satisfy premise h
  case kGarden.empty {
    rw count at h,
    cases h,
  },
  -- For the single ninja, we take c = empty if the arguments coincide
  case kGarden.ninja : m' v' {
    existsi kGarden.empty,
    simp [kGarden.eqa.join_right_id],
    -- m' = m and v' = v, so we are done
    simp only [count_ninja h],
  },
  case kGarden.join : l r hl hr {
    by_cases hcl : count m v l > 0,
    {
      -- Replace l by induction hypothesis and obtain
      -- a term of the expected shape by associativity
      cases hl hcl with c hc,
      existsi (c.join r),
      simp only [kGarden.eqa.join_assoc, hc],
    },
    {
      -- The same with r, but commutativity and more
      -- transformations are needed
      have hcr : count m v r > 0 := or.resolve_left (count_join_pos h) hcl,
      cases hr hcr with c hc,
      existsi (l.join c),
      simp only [kGarden.eqa.join_assoc, kGarden.eqa.join_comm, hc],
    },
  },
end

-- Corollary of th previous lemma with a selected ninja for each argument
-- of a join term that can be put ahead
lemma pair_join {l r : kGarden} {m₁ m₂ : kMode} {v₁ v₂ : kVote}
  (hl : count m₁ v₁ l > 0) (hr : count m₂ v₂ r > 0)
  : ∃ c, l.join r =A ((kGarden.ninja m₁ v₁).join (kGarden.ninja m₂ v₂)).join c :=
begin
  -- Apply ninja_first in both arguments
  cases (ninja_first hl) with cl hcl,
  cases (ninja_first hr) with cr hcr,
  -- c can be cl.join cr after some arrangements
  existsi (cl.join cr),
  simp [hcl, hcr, kGarden.eqa.join_assoc],
  apply kGarden.eqa.eqa_join,
  {
    transitivity (kGarden.ninja m₁ v₁).join (cl.join (kGarden.ninja m₂ v₂)),
    { simp only [kGarden.eqa.join_assoc], },
    { simp only [@kGarden.eqa.join_comm cl (kGarden.ninja m₂ v₂)],
      simp only [kGarden.eqa.join_assoc], },
  },
  { refl, }
end

-- Any pair of ninjas can appear first in the multiset
-- (we require that the ninjas are distinct for simplicity, but
-- what we actually want to express is that one is not counted twice)
lemma pair_first {g : kGarden} {m₁ m₂ : kMode} {v₁ v₂ : kVote}
  (d : m₁ ≠ m₂ ∨ v₁ ≠ v₂) (h₁ : count m₁ v₁ g > 0) (h₂ : count m₂ v₂ g > 0)
  : ∃ c, g =A ((kGarden.ninja m₁ v₁).join (kGarden.ninja m₂ v₂)).join c :=
begin
  induction g,
  case kGarden.empty {
    -- The premises cannot hold
    rw count at h₁,
    cases h₁,
  },
  case kGarden.ninja : m v {
    -- The single ninja cannot be 1 and 2 at the same time
    simp [count_ninja h₁, count_ninja h₂] at d,
    contradiction,
  },
  case kGarden.join : l r hl hr {
    by_cases hcl₁ : count m₁ v₁ l > 0,
    {
      by_cases hcl₂ : count m₂ v₂ l > 0,
      {
        -- (Case 1) Both ninjas are in the first argument, so we can apply
        -- induction hypothesis to obtain a subterm with the two ninjas in the
        -- first positions and adapt it by associativity to the desired shape
        cases hl hcl₁ hcl₂ with c hc,
        existsi (c.join r),
        simp only [kGarden.eqa.join_assoc, hc],
      },
      {
        -- (Case 2) The ninjas 1 and 2 are in different arguments, so we have to apply
        -- ninja_first twice to put the ninjas on top of their corresponding arguments
        -- and then readapt the term to the desired shape (this is done by pair_join)
        have hcr₂ : count m₂ v₂ r > 0 := or.resolve_left (count_join_pos h₂) hcl₂,
        exact pair_join hcl₁ hcr₂,
      }
    },
    {
      have hcr₁ : count m₁ v₁ r > 0 := or.resolve_left (count_join_pos h₁) hcl₁,
      by_cases hcl₂ : count m₂ v₂ l > 0,
      {
        -- (Case 2) Like the previous case, but ninja 2 is in the left argument and
        -- we have to apply commutativity to obtain the desired pattern
        simp [@kGarden.eqa.join_comm (kGarden.ninja m₁ v₁) (kGarden.ninja m₂ v₂)],
        exact pair_join hcl₂ hcr₁,
      },
      {
        -- (Case 1) Dual of the previous case 1, both ninjas are in the second
        -- argument (a few more adaptations are needed to obtain the desired shape)
        have hcr₂ : count m₂ v₂ r > 0 := or.resolve_left (count_join_pos h₂) hcl₂,
        cases hr hcr₁ hcr₂ with c hc,
        existsi (l.join c),
        -- simp alone times out, so we help with comm
        simp only [@kGarden.eqa.join_comm l r, @kGarden.eqa.join_comm l c],
        simp only [kGarden.eqa.join_assoc, hc],
      }
    }
  },
end

--
-- The three rules in terms of count
--
-- We follow the same pattern with all these proofs: pair_first is applied
-- first to obtain a term ({M₁, V₁} {M₂, V₂}) G in whose left argument we
-- can apply the rule, then we check the assertions routinely. count_eqa
-- (count is preserved by =A) is essential to prove the count assertions.
--

-- First rule in terms of count
lemma r1_count {g : kGarden}
  (hy : count kMode.A kVote.Y g > 0) (hn : count kMode.A kVote.N g > 0)
  : ∃ c, g =>1 c
  ∧ (count kMode.A kVote.Y c + 1 = count kMode.A kVote.Y g)
  ∧ (count kMode.A kVote.N c + 1 = count kMode.A kVote.N g)
  ∧ (count kMode.P kVote.Y c = count kMode.P kVote.Y g)
  ∧ (count kMode.P kVote.N c = count kMode.P kVote.N g + 2) :=
begin
  have d : kMode.A ≠ kMode.A ∨ kVote.Y ≠ kVote.N, { right, simp, },
  cases pair_first d hy hn with gs hg,
  existsi ((kGarden.ninja kMode.P kVote.N).join (kGarden.ninja kMode.P kVote.N)).join gs,
  split,
  {
    -- There is a rewrite, apply r1 on the left subterm
    simp [hg],
    apply kGarden.rw_one.sub_join₀,
    exact kGarden.rw_one.rl_r1,
  },
  simp [count, nat.zero_add, nat.add_zero, hg],
  split,
  -- count A Y
  {
    have hay := count_eqa kMode.A kVote.Y hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at hay,
    simp [hay],
    rw nat.add_comm,
  },
  split,
  -- count A N
  {
    have han := count_eqa kMode.A kVote.N hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at han,
    simp [han],
    rw nat.add_comm,
  },
  split,
  -- count P Y
  {
    have hpy := count_eqa kMode.P kVote.Y hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at hpy,
    symmetry,
    exact hpy,
  },
  -- count P N
  {
    have hpn := count_eqa kMode.P kVote.N hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at hpn,
    simp [hpn],
    rw nat.add_comm,
  },
end

-- Second rule in terms of count
lemma r2_count {g : kGarden} {v : kVote}
  (hy : count kMode.A v g > 0) (hn : count kMode.P v.other g > 0)
  : ∃ c, g =>1 c
  ∧ (count kMode.A v c = count kMode.A v g)
  ∧ (count kMode.A v.other c = count kMode.A v.other g)
  ∧ (count kMode.P v c = count kMode.P v g + 1)
  ∧ (count kMode.P v.other c + 1 = count kMode.P v.other g) :=
begin
  have d : kMode.A ≠ kMode.P ∨ v ≠ v.other, { left, simp, },
  cases pair_first d hy hn with gs hg,
  existsi ((kGarden.ninja kMode.A v).join (kGarden.ninja kMode.P v)).join gs,
  split,
  {
    -- There is a rewrite, apply r1 on the left argument
    simp [hg],
    apply kGarden.rw_one.sub_join₀,
    exact kGarden.rw_one.rl_r2,
  },
  simp [count, nat.zero_add, nat.add_zero, hg],
  split,
  -- count A v
  {
    have hay := count_eqa kMode.A v hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at hay,
    simp [hay],
  },
  split,
  -- count A v.other
  {
    have han := count_eqa kMode.A v.other hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at han,
    simp [han],
  },
  -- Auxiliary results for the next to cases
  have hts : v ≠ v.other ∧ v.other ≠ v, {
    cases v,
    all_goals { simp [Maude.kVote.other], },
  },
  split,
  -- count P v
  {
    have hpy := count_eqa kMode.P v hg,
    simp [count, nat.zero_add, nat.add_zero, hg, hts] at hpy,
    rw nat.add_comm,
    simp [hpy],
  },
  -- count P v.other
  {
    have hpn := count_eqa kMode.P v.other hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at hpn,
    simp [hpn, hts, nat.zero_add],
    rw nat.add_comm,
  },
end

-- Third rule in terms of count
lemma r3_count {g : kGarden}
  (hy : count kMode.P kVote.Y g > 0) (hn : count kMode.P kVote.N g > 0)
  : ∃ c, g =>1 c
  ∧ (count kMode.A kVote.Y c = count kMode.A kVote.Y g)
  ∧ (count kMode.A kVote.N c = count kMode.A kVote.N g)
  ∧ (count kMode.P kVote.Y c + 1 = count kMode.P kVote.Y g)
  ∧ (count kMode.P kVote.N c = count kMode.P kVote.N g + 1) :=
begin
  have d : kMode.P ≠ kMode.P ∨ kVote.Y ≠ kVote.N, { right, simp, },
  cases pair_first d hy hn with gs hg,
  existsi ((kGarden.ninja kMode.P kVote.N).join (kGarden.ninja kMode.P kVote.N)).join gs,
  split,
  {
    -- There is a rewrite, apply r1 on the left argument
    simp [hg],
    apply kGarden.rw_one.sub_join₀,
    exact kGarden.rw_one.rl_r3,
  },
  simp [count, nat.zero_add, nat.add_zero, hg],
  split,
  -- count A Y
  {
    have hay := count_eqa kMode.A kVote.Y hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at hay,
    simp [hay],
  },
  split,
  -- count A N
  {
    have han := count_eqa kMode.A kVote.N hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at han,
    simp [han],
  },
  split,
  -- count P Y
  {
    have hpy := count_eqa kMode.P kVote.Y hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at hpy,
    simp [hpy],
    rw nat.add_comm,
  },
  -- count P N
  {
    have hpn := count_eqa kMode.P kVote.N hg,
    simp [count, nat.zero_add, nat.add_zero, hg] at hpn,
    simp [hpn],
    rw nat.add_comm (1 + count kMode.P kVote.N gs) 1,
    simp [nat.add_assoc],
  },
end

--
-- Consensus can be obtained from every configuration
--

-- Auxiliary lemma for the next proof
lemma add_lt_add {n m k : ℕ} : n + k < m + k → n < m :=
begin
  intro h,
  -- n < m is defined as n.succ ≤ m
  change (n + k).succ ≤ m + k at h,
  rw ← nat.add_succ at h,
  rw ← nat.succ_add_eq_succ_add at h,
  exact nat.le_of_add_le_add_right h,
end

-- Successors are positive
lemma eq_succ_lt_zero {n m : ℕ} : n = m.succ → n > 0 :=
begin
  intro h,
  rw h,
  exact nat.zero_lt_succ m,
end

-- Eliminate all {A, v.other} nijas using {A, v} ninjas
lemma eliminate_ax {g : kGarden} {v : kVote}
  (h : count kMode.A v g ≥ count kMode.A v.other g)
  : ∃ c, g =>* c
         ∧ count kMode.A v c = (count kMode.A v g - count kMode.A v.other g)
         ∧ count kMode.A v.other c = 0
         -- In another proof we need that count P N c is positive if either count P N g or count A y g
         -- are, so we have introduced this statement (can be an equality with + 2 *)
         ∧ (v = kVote.N → count kMode.P kVote.N c ≥ count kMode.P kVote.N g + count kMode.A kVote.Y g) :=
begin
  -- By induction on the number of {A, v.other} ninjas
  induction ih : (count kMode.A v.other g) generalizing g,
  case nat.zero {
    -- The initial term does not contain {A, v.other} ninjas, so it can be c
    existsi g,
    rw ih at h,
    simp only [nat.sub_zero, nat.add_zero],
    -- =>* is reflexive and everything else is in the premises
    have last : v = kVote.N → count kMode.P kVote.N g ≥ count kMode.P kVote.N g + count kMode.A kVote.Y g, {
      intro vn,
      simp only [vn, Maude.kVote.other] at ih,
      simp only [ih, nat.add_zero],
      exact nat.le_refl _,
    },
    exact ⟨kGarden.rw_star.refl (kGarden.eqe_refl g), eq.refl _, ih, last⟩,
  },
  case nat.succ : n ih g h han {
    -- Lets apply rule 1 (by preparing the premises first)
    have cav_pos : count kMode.A v g > 0, {
      -- Follows from count kMode.A v g ≥ count kMode.A v.other g
      -- and the positiveness of the second term
      cases nat.eq_zero_or_pos (count kMode.A v.other g) with hz hz,
      {
        rw han at h,
        cases nat.eq_zero_or_pos n with hzz hzz,
        { rw hzz at h, exact h, },
        { exact nat.lt_trans hzz h, },
      },
      { exact nat.le_trans hz h, },
    },
    -- Follows from count kMode.A kVote.N g = n.succ
    have cao_pos : count kMode.A v.other g > 0 := eq_succ_lt_zero han,
    -- Rephrase the results in terms of v and v.other to Y and N
    have ca_pos : count kMode.A kVote.Y g > 0 ∧ count kMode.A kVote.N g > 0, {
      cases v,
      case kVote.Y { exact ⟨cav_pos, cao_pos⟩, },
      case kVote.N { exact ⟨cao_pos, cav_pos⟩, },
    },
    cases r1_count ca_pos.left ca_pos.right with g1 hg1,
    -- The following two intermediate results follow by case distinction
    have cay_gt_can : count kMode.A v g1 ≥ count kMode.A v.other g1, {
      -- Follows from the fact that both counts decrease by the application of the rule
      cases v,
      all_goals {
        rw Maude.kVote.other at ⊢ h,
        rw [← hg1.right.left, ← hg1.right.right.left] at h,
        exact nat.le_of_add_le_add_right h,
      },
    },
    have can_n : count kMode.A v.other g1 = n, {
      cases v,
      all_goals {
        rw Maude.kVote.other at ⊢ han,
        simp only [← hg1.right.left, ← hg1.right.right.left] at han,
        injections,
      },
    },
    -- Apply induction hypothesis (its garden will be the desired one)
    cases ih cay_gt_can can_n with g2 hg2,
    existsi g2,
    -- The following results are used to simplify the goal:
    -- hv generalizes from Y and N to v and hm1 does operate with ℕ  
    have hv : count kMode.A v g = count kMode.A v g1 + 1, {
      cases v,
      all_goals { simp only [hg1], },
    },
    rw hv,
    have hm1 : count kMode.A v g1 + 1 - n.succ = count kMode.A v g1 - n, {
      simp only [nat.succ_sub_succ],
    },
    rw hm1,
    -- The last claim of the statement needs some more reasoning
    have last : v = kVote.N → count kMode.P kVote.N g2 ≥ count kMode.P kVote.N g + count kMode.A kVote.Y g, {
      intro vn,
      simp [vn, Maude.kVote.other] at ⊢ hg1 hg2 han can_n,
      -- main is the last claim in the induction hypothesis
      have main : count kMode.P kVote.N g2 ≥ count kMode.P kVote.N g1 + count kMode.A kVote.Y g1 := hg2.right.right.right trivial,
      rw han,
      rw [hg1.right.right.right.right, can_n, nat.add_assoc] at main,
      -- aux only deals with arithmetic
      have aux : n.succ ≤ 2 + n, {
        have le122 : 1 ≤ 2, { exact nat.le_add_right _ _, },
        transitivity 1 + n,
        { rw nat.add_comm, },
        { exact nat.add_le_add_right le122 _, },
      },
      exact nat.le_trans (nat.add_le_add_left aux _) main,
    },
    -- g =>* g2 by transitity and all other facts are in the induction hypothesis
    exact ⟨kGarden.rw_star.trans (kGarden.rw_star.step hg1.left) hg2.left,
           hg2.right.left, hg2.right.right.left, last⟩,
  },
end

-- v.other.other = other
lemma other_other (v : kVote) : v.other.other = v :=
begin
  cases v,
  all_goals {simp only [Maude.kVote.other], }
end

-- Eliminate all {P, v} nijas using {A, v.other} ninjas
lemma eliminate_p_with_a {g : kGarden} {v : kVote} (h : count kMode.A v.other g > 0) :
  ∃ c, g =>* c ∧ count kMode.P v c = 0
               ∧ count kMode.A v c = count kMode.A v g :=
begin
  -- Induction on the number of {P, v} ninjas (we want to reduce it to zero)
  induction hp : (count kMode.P v g) generalizing g,
  case nat.zero {
    existsi g,
    -- =>* is reflexive, the rest is straightforward
    exact ⟨kGarden.rw_star.refl (kGarden.eqe_refl g), hp, eq.refl _⟩,
  },
  -- Lets apply rule 2 to convert one {P, v}
  case nat.succ {
    -- count P v g > 0 to apply the rule
    have cpn_pos : count kMode.P v.other.other g > 0, {
      simp only [other_other],
      exact eq_succ_lt_zero hp,
    },
    cases (r2_count h cpn_pos) with g1 hg1,
    simp [other_other] at hg1,
    -- We want to apply induction hypothesis from g1,
    -- but we need to prove its premises first
    have hay : count kMode.A v.other g1 > 0, {
      simp only [h, hg1],
    },
    have hpn : count kMode.P v g1 = n, {
      rw ← hg1.right.right.right.right at hp,
      injections,
    },
    cases (ih hay hpn) with g2 hg2,
    -- Compose the step from rule 2 and induction hypothesis
    -- (we have converted one ninja with rule 2, then the rest by induction hypothesis)
    existsi g2,
    simp [hg1] at hg2,
    have g_star_g2 : g =>* g2 := kGarden.rw_star.trans (kGarden.rw_star.step hg1.left) hg2.left,
    exact ⟨g_star_g2, hg2.right.left, hg2.right.right⟩,
  },
end

-- < implies ≤ (this should be already available)
lemma lt_to_le {n m : ℕ} : n < m → n ≤ m :=
begin
  intro h,
  apply nat.le_of_succ_le_succ,
  exact nat.le_trans h (nat.le_succ m),
end

-- If there are more active Y-voters, consensus is reachable
lemma to_consensus_y {g : kGarden} (h : count kMode.A kVote.Y g > count kMode.A kVote.N g) :
  ∃ c, g =>* c ∧ consensus_for kVote.Y c :=
begin
  -- Remove {A, N} first
  -- We adjust the first hypothesis to include other and ≤
  have eax_h1 : count kMode.A kVote.Y g ≥ count kMode.A kVote.Y.other g, {
    apply lt_to_le,
    exact h,
  },
  cases eliminate_ax eax_h1 with g1 hg1,
  -- Remove {P, N} then
  -- Adapt the hypothesis, which is essentially hg1.right.left
  have hg1_other : count kMode.A kVote.N.other g1 > 0, {
    have hs := hg1.right.left, -- count A Y g1 is a difference
    rw Maude.kVote.other at ⊢ hs,
    have hz := nat.sub_pos_of_lt h, -- this difference is positive
    rw ← hs at hz,
    exact hz,
  },
  cases eliminate_p_with_a hg1_other with g2 hg2,
  existsi g2,
  split,
  -- g =>* g2
  {
    exact kGarden.rw_star.trans hg1.left hg2.left,
  },
  -- consensus_for Y g2
  {
    have hz : count kMode.A kVote.N g2 = count kMode.A kVote.N g1 := hg2.right.right,
    simp only [Maude.kVote.other] at hg1,
    rw hg1.right.right.left at hz, -- rewrite with count A N g1 = 0
    exact zero_count_consensus hz hg2.right.left,
  }
end

-- Eliminate {P, Y} ninjas with {P, N} ninjas
lemma eliminate_py {g : kGarden} (h : count kMode.P kVote.N g > 0) :
  ∃ c, g =>* c ∧ count kMode.P kVote.Y c = 0
               ∧ count kMode.A kVote.Y c = count kMode.A kVote.Y g :=
begin
  induction hc : count kMode.P kVote.Y g generalizing g,
  case nat.zero {
    existsi g,
    exact ⟨kGarden.rw_star.refl (kGarden.eqe_refl g), hc, eq.refl _⟩,
  },
  case nat.succ {
    -- Lets apply rule 3 (by preparing its hypothesis first)
    have hpy : count kMode.P kVote.Y g > 0 := eq_succ_lt_zero hc,
    cases (r3_count hpy h) with g1 hg1,
    -- Continue removing {P, Y} ninjas with induction hypothesis
    have hpn : count kMode.P kVote.N g1 > 0 := eq_succ_lt_zero hg1.right.right.right.right,
    have hpy : count kMode.P kVote.Y g1 = n, {
      rw ← hg1.right.right.right.left at hc,
      injections,
    },
    cases (ih hpn hpy) with g2 hg2,
    -- Take the result of the induction hypothesis as that of the lemma
    existsi g2,
    rw hg1.right.left at hg2,
    exact ⟨kGarden.rw_star.trans (kGarden.rw_star.step hg1.left) hg2.left,
           hg2.right.left, hg2.right.right⟩,
  },
end

-- Negative consensus can be obtained if the following conditions hold
lemma to_consesus_n {g : kGarden}
  (ha : count kMode.A kVote.Y g ≤ count kMode.A kVote.N g)
  (hn : count kMode.A kVote.N g > 0 ∨ count kMode.P kVote.N g > 0)
  : ∃ c, g =>* c ∧ consensus_for kVote.N c :=
begin
  -- We first apply eliminate_ax
  have ha' : count kMode.A kVote.N.other g ≤ count kMode.A kVote.N g, {
    rw Maude.kVote.other, exact ha,
  },
  cases eliminate_ax ha' with g1 hg1,
  have extra := hg1.right.right.right (eq.refl _), -- count P N g1 is ≥ than a sum
  -- Then we apply eliminate_py or eliminate_p_with_a
  simp [Maude.kVote.other] at hg1,
  by_cases h1 : count kMode.A kVote.N g1 > 0,
  -- There are active negative ninjas (use eliminate_p_with_a)
  {
    have can_pos : count kMode.A kVote.Y.other g1 > 0 := h1,
    cases eliminate_p_with_a can_pos with g2 hg2,
    existsi g2,
    rw hg1.right.right.left at hg2,
    exact ⟨kGarden.rw_star.trans hg1.left hg2.left,
           zero_count_consensus hg2.right.right hg2.right.left⟩,
  },
  -- There are passive negative ninjas (prove this, then apply eliminate_py)
  {
    -- First prove that there are passive negative ninjas
    have can_zero_g1 : count kMode.A kVote.N g1 = 0, {
      simp at h1,
      exact nat.eq_zero_of_le_zero h1,
    },
    have can_eq_cay : count kMode.A kVote.N g = count kMode.A kVote.Y g, {
      have hi := hg1.right.left, -- count A N g1 is a difference
      rw can_zero_g1 at hi, -- but one of its operands is zero
      have n_le_y := nat.le_of_sub_eq_zero (eq.symm hi),
      -- Combine ≤ with ≥ to obtain the equality
      exact nat.le_antisymm n_le_y ha,
    },
    have cpn_pos : count kMode.P kVote.N g1 > 0, {
      cases hn,
      -- count A N g > 0
      {
        rw can_eq_cay at hn,
        exact nat.le_trans hn (nat.le_trans (nat.le_add_left _ _) extra),
      },
      -- count P N g > 0
      {
        exact nat.le_trans hn (nat.le_trans (nat.le_add_right _ _) extra),
      },
    },
    -- Lets apply eliminate_py
    cases eliminate_py cpn_pos with g2 hg2,
    existsi g2,
    rw ← hg2.right.right at hg1,
    -- Follows by transivity and because the counts for Y are zero
    exact ⟨kGarden.rw_star.trans hg1.left hg2.left,
           zero_count_consensus hg1.right.right.left hg2.right.left⟩,
  },
end

-- Consensus is reachable from any configuration
theorem to_consensus (g : kGarden) : ∃ c, g =>* c ∧ consensus c :=
begin
  -- Case distinction to apply either to_consensus_y or to_consensus_n
  by_cases ha : count kMode.A kVote.Y g > count kMode.A kVote.N g,
  {
    cases to_consensus_y ha with c hc,
    existsi c,
    exact ⟨hc.left, or.inl hc.right⟩,
  },
  {
    -- Consensus can still be positive if there is no ninja with a negative vote
    -- (second case). The following hn is the remaining premise of to_consensus_n
    simp at ha,
    by_cases hn : count kMode.A kVote.N g > 0 ∨ count kMode.P kVote.N g > 0,
    {
      cases to_consesus_n ha hn with c hc,
      existsi c,
      exact ⟨hc.left, or.inr hc.right⟩,
    },
    {
      -- There are no N-voters at all, there is already Y-consensus in g
      simp [decidable.not_or_iff_and_not] at hn,
      have hna : count kMode.A kVote.N g = 0 := nat.eq_zero_of_le_zero hn.left,
      have hnp : count kMode.P kVote.N g = 0 := nat.eq_zero_of_le_zero hn.right,
      existsi g,
      split,
      -- g =>* g
      { exact kGarden.rw_star.refl (kGarden.eqe_refl g), },
      -- consensus g (follows directly from hna and hnp)
      { left, exact zero_count_consensus hna hnp, }
    },
  }
end

--
-- Counterexample: there is a infinite path that never reaches consensus
--

-- Rewriting path (not used)
def rw_path (π : ℕ → kGarden) :=
  ∀ n, (π n) =>1 (π (n + 1))

@[inline]
def counter_state1 := ((kGarden.ninja kMode.A kVote.Y).join
                       (kGarden.ninja kMode.P kVote.N)).join
                      (kGarden.ninja kMode.P kVote.N)

@[inline]
def counter_state2 := ((kGarden.ninja kMode.A kVote.Y).join
                       (kGarden.ninja kMode.P kVote.Y)).join
                      (kGarden.ninja kMode.P kVote.N)

-- state1 can be rewritten to state2 in one step
lemma counter_step1 : counter_state1 =>1 counter_state2 :=
begin
  -- Simply apply r2 in the left subterm
  apply kGarden.rw_one.sub_join₀,
  exact kGarden.rw_one.rl_r2,
end

-- state2 can be rewritten to state1 in one step
lemma counter_step2 : counter_state2 =>1 counter_state1 :=
begin
  -- Group the last two ninjas together to apply r3 on them
  have hal : counter_state2 =A (kGarden.ninja kMode.A kVote.Y).join
             ((kGarden.ninja kMode.P kVote.Y).join (kGarden.ninja kMode.P kVote.N)), {
    simp [kGarden.eqa.join_assoc, counter_state2],
  },
  have har : (kGarden.ninja kMode.A kVote.Y).join
             ((kGarden.ninja kMode.P kVote.N).join (kGarden.ninja kMode.P kVote.N)) =A counter_state1, {
    simp [kGarden.eqa.join_assoc, counter_state1],
  },
  apply kGarden.rw_one.eqe_left (kGarden.eqe.from_eqa hal),
  apply kGarden.rw_one.eqe_right _ (kGarden.eqe.from_eqa har),
  -- Get the right argument and apply r3 on it
  apply kGarden.rw_one.sub_join₁,
  exact kGarden.rw_one.rl_r3,
end

-- there is no consensus in state1
lemma counter_not_consensus1 : ¬ consensus counter_state1 :=
begin
  intro h,
  cases h,
  all_goals {
    simp [consensus_for, counter_state1] at h,
    exact h,
  },
end

-- there is no consensus in state2
lemma counter_not_consensus2 : ¬ consensus counter_state2 :=
begin
  intro h,
  cases h,
  all_goals {
    simp [consensus_for, counter_state2] at h,
    exact h,
  },
end

-- Counterxample path
def counter_path : ℕ → kGarden
  | 0                       := counter_state1
  | 1                       := counter_state2
  | (nat.succ (nat.succ n)) := counter_path n

-- Induction principle to facilitate the following proof
lemma zero_one_induction (p : ℕ → Prop) :
  ∀ n, p 0 → p 1 → (∀ m : ℕ, p m → p m.succ.succ) →  p n :=
begin
  intros n h0 h1 hss,
  have h : (p n ∧ p (n.succ)), {
    induction n,
    case nat.zero { exact ⟨h0, h1⟩, },
    case nat.succ : n ih {
      exact ⟨ih.right, hss _ ih.left⟩,
    },
  },
  exact h.left,
end

-- counter_path is a path that never arrives to consensus
theorem is_counter_path (n : ℕ) :
  counter_path n =>1 counter_path (n + 1)
  ∧ ¬ consensus (counter_path n) :=
begin
  split,
  {
    induction n using zero_one_induction with m hm,
    -- n = 0
    { simp [counter_path, counter_step1], },
    -- n = 1
    { simp [counter_path, counter_step2], },
    -- n → s s n
    { simp [counter_path, hm], },
  },
  {
induction n using zero_one_induction with m hm,
    -- n = 0
    { simp [counter_path, counter_not_consensus1], },
    -- n = 1
    { simp [counter_path, counter_not_consensus2], },
    -- n → s s n
    { simp [counter_path, hm], },
  },
end
