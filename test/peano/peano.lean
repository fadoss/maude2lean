namespace Maude

-- Sorts
inductive MSort
	| Bool
	| NzNat
	| Even
	| Nat

-- Generator of the subsort relation
def subsort : MSort → MSort → Prop
	| MSort.NzNat MSort.Nat := true
	| MSort.Even MSort.Nat := true
	| _ _ := false

-- Kinds and their operators

inductive kBool
	| true
	| false
	| and : kBool → kBool → kBool
	| or : kBool → kBool → kBool
	| xor : kBool → kBool → kBool
	| not : kBool → kBool
	| implies : kBool → kBool → kBool

inductive kNat
	| zero
	| s : kNat → kNat
	| sum : kNat → kNat → kNat

-- Kind assignment
def kind : MSort → Type
	| MSort.Bool := kBool
	| MSort.NzNat := kNat
	| MSort.Even := kNat
	| MSort.Nat := kNat

-- Predicates recognizing constructor terms
mutual def kBool.ctor_only, kNat.ctor_only

with kBool.ctor_only : kBool → Prop
	| kBool.true := true
	| kBool.false := true
	| _ := false

with kNat.ctor_only : kNat → Prop
	| kNat.zero := true
	| (kNat.s a) := a.ctor_only
	| _ := false

-- Equality modulo axioms
mutual inductive kBool.eqa, kNat.eqa

with kBool.eqa : kBool → kBool → Prop
	| refl {a} : kBool.eqa a a
	| symm {a b} : kBool.eqa a b → kBool.eqa b a
	| trans {a b c} : kBool.eqa a b → kBool.eqa b c → kBool.eqa a c
	-- Congruence axioms for each operator
	| eqa_and {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.and a₀ a₁) (kBool.and b₀ b₁)
	| eqa_or {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.or a₀ a₁) (kBool.or b₀ b₁)
	| eqa_xor {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.xor a₀ a₁) (kBool.xor b₀ b₁)
	| eqa_not {a b : kBool} : kBool.eqa a b → kBool.eqa (kBool.not a) (kBool.not b)
	| eqa_implies {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.implies a₀ a₁) (kBool.implies b₀ b₁)
	-- Structural axioms
	| and_comm {a b} : kBool.eqa (kBool.and a b) (kBool.and b a)
	| and_assoc {a b c} : kBool.eqa (kBool.and a (kBool.and b c)) (kBool.and (kBool.and a b) c)
	| or_comm {a b} : kBool.eqa (kBool.or a b) (kBool.or b a)
	| or_assoc {a b c} : kBool.eqa (kBool.or a (kBool.or b c)) (kBool.or (kBool.or a b) c)
	| xor_comm {a b} : kBool.eqa (kBool.xor a b) (kBool.xor b a)
	| xor_assoc {a b c} : kBool.eqa (kBool.xor a (kBool.xor b c)) (kBool.xor (kBool.xor a b) c)

with kNat.eqa : kNat → kNat → Prop
	| refl {a} : kNat.eqa a a
	| symm {a b} : kNat.eqa a b → kNat.eqa b a
	| trans {a b c} : kNat.eqa a b → kNat.eqa b c → kNat.eqa a c
	-- Congruence axioms for each operator
	| eqa_s {a b : kNat} : kNat.eqa a b → kNat.eqa (kNat.s a) (kNat.s b)
	| eqa_sum {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.sum a₀ a₁) (kNat.sum b₀ b₁)

-- Sort membership and equality modulo equations

mutual inductive kBool.has_sort, kNat.has_sort, kBool.eqe, kNat.eqe
with kBool.has_sort : kBool → MSort → Prop
	| subsort {t a b} : subsort a b → kBool.has_sort t a → kBool.has_sort t b
	-- Implicit membership axioms (operator declarations)
	| true_decl : kBool.has_sort kBool.true MSort.Bool
	| false_decl : kBool.has_sort kBool.false MSort.Bool
	| and_decl {a₀ a₁ : kBool} : kBool.has_sort a₀ MSort.Bool → kBool.has_sort a₁ MSort.Bool → kBool.has_sort (kBool.and a₀ a₁) MSort.Bool
	| or_decl {a₀ a₁ : kBool} : kBool.has_sort a₀ MSort.Bool → kBool.has_sort a₁ MSort.Bool → kBool.has_sort (kBool.or a₀ a₁) MSort.Bool
	| xor_decl {a₀ a₁ : kBool} : kBool.has_sort a₀ MSort.Bool → kBool.has_sort a₁ MSort.Bool → kBool.has_sort (kBool.xor a₀ a₁) MSort.Bool
	| not_decl {a : kBool} : kBool.has_sort a MSort.Bool → kBool.has_sort (kBool.not a) MSort.Bool
	| implies_decl {a₀ a₁ : kBool} : kBool.has_sort a₀ MSort.Bool → kBool.has_sort a₁ MSort.Bool → kBool.has_sort (kBool.implies a₀ a₁) MSort.Bool

with kNat.has_sort : kNat → MSort → Prop
	| subsort {t a b} : subsort a b → kNat.has_sort t a → kNat.has_sort t b
	-- Implicit membership axioms (operator declarations)
	| zero_decl : kNat.has_sort kNat.zero MSort.Even
	| s_decl {a : kNat} : kNat.has_sort a MSort.Nat → kNat.has_sort (kNat.s a) MSort.NzNat
	| sum_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.sum a₀ a₁) MSort.Nat
	-- Explicit membership axioms
	| mb_s {n} : kNat.has_sort n MSort.Even → kNat.has_sort (kNat.s (kNat.s n)) MSort.Even

with kBool.eqe : kBool → kBool → Prop
	| from_eqa {a b} : kBool.eqa a b → kBool.eqe a b
	| symm {a b} : kBool.eqe a b → kBool.eqe b a
	| trans {a b c} : kBool.eqe a b → kBool.eqe b c → kBool.eqe a c
	-- Congruence axioms for each operator
	| eqe_and {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.and a₀ a₁) (kBool.and b₀ b₁)
	| eqe_or {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.or a₀ a₁) (kBool.or b₀ b₁)
	| eqe_xor {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.xor a₀ a₁) (kBool.xor b₀ b₁)
	| eqe_not {a b : kBool} : kBool.eqe a b → kBool.eqe (kBool.not a) (kBool.not b)
	| eqe_implies {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.implies a₀ a₁) (kBool.implies b₀ b₁)
	-- Equations
	| eq_and₀ {a} : kBool.eqe (kBool.and kBool.true a) a
	| eq_and₁ {a} : kBool.eqe (kBool.and kBool.false a) kBool.false
	| eq_and₂ {a} : kBool.eqe (kBool.and a a) a
	| eq_xor₀ {a} : kBool.eqe (kBool.xor kBool.false a) a
	| eq_xor₁ {a} : kBool.eqe (kBool.xor a a) kBool.false
	| eq_and₃ {a b c} : kBool.eqe (kBool.and a (kBool.xor b c)) (kBool.xor (kBool.and a b) (kBool.and a c))
	| eq_not {a} : kBool.eqe (kBool.not a) (kBool.xor kBool.true a)
	| eq_or {a b} : kBool.eqe (kBool.or a b) (kBool.xor (kBool.and a b) (kBool.xor a b))
	| eq_implies {a b} : kBool.eqe (kBool.implies a b) (kBool.not (kBool.xor a (kBool.and a b)))

with kNat.eqe : kNat → kNat → Prop
	| from_eqa {a b} : kNat.eqa a b → kNat.eqe a b
	| symm {a b} : kNat.eqe a b → kNat.eqe b a
	| trans {a b c} : kNat.eqe a b → kNat.eqe b c → kNat.eqe a c
	-- Congruence axioms for each operator
	| eqe_s {a b : kNat} : kNat.eqe a b → kNat.eqe (kNat.s a) (kNat.s b)
	| eqe_sum {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.sum a₀ a₁) (kNat.sum b₀ b₁)
	-- Equations
	| eq_sum₀ {n} : kNat.eqe (kNat.sum n kNat.zero) n
	| eq_sum₁ {n m} : kNat.eqe (kNat.sum n (kNat.s m)) (kNat.s (kNat.sum n m))

infix (name := kBool_has_sort) ` ⊳ `:40 := kBool.has_sort
infix (name := kNat_has_sort) ` ⊳ `:40 := kNat.has_sort

infix (name := kBool_eqa) ` =A `:40 := kBool.eqa
infix (name := kNat_eqa) ` =A `:40 := kNat.eqa

infix (name := kBool_eqe) ` =E `:40 := kBool.eqe
infix (name := kNat_eqe) ` =E `:40 := kNat.eqe

-- Rewriting relations

mutual inductive kBool.rw_one, kNat.rw_one, kBool.rw_star, kNat.rw_star
with kBool.rw_one : kBool → kBool → Prop
	| eqe_left {a b c : kBool} : a =E b → kBool.rw_one b c → kBool.rw_one a c
	| eqe_right {a b c : kBool} : kBool.rw_one a b → b =E c → kBool.rw_one a c
	-- Axioms for rewriting inside subterms
	| sub_and₀ {a₁ a b} : kBool.rw_one a b →
		kBool.rw_one (kBool.and a a₁) (kBool.and b a₁)
	| sub_and₁ {a₀ a b} : kBool.rw_one a b →
		kBool.rw_one (kBool.and a₀ a) (kBool.and a₀ b)
	| sub_or₀ {a₁ a b} : kBool.rw_one a b →
		kBool.rw_one (kBool.or a a₁) (kBool.or b a₁)
	| sub_or₁ {a₀ a b} : kBool.rw_one a b →
		kBool.rw_one (kBool.or a₀ a) (kBool.or a₀ b)
	| sub_xor₀ {a₁ a b} : kBool.rw_one a b →
		kBool.rw_one (kBool.xor a a₁) (kBool.xor b a₁)
	| sub_xor₁ {a₀ a b} : kBool.rw_one a b →
		kBool.rw_one (kBool.xor a₀ a) (kBool.xor a₀ b)
	| sub_not {a b} : kBool.rw_one a b →
		kBool.rw_one (kBool.not a) (kBool.not b)
	| sub_implies₀ {a₁ a b} : kBool.rw_one a b →
		kBool.rw_one (kBool.implies a a₁) (kBool.implies b a₁)
	| sub_implies₁ {a₀ a b} : kBool.rw_one a b →
		kBool.rw_one (kBool.implies a₀ a) (kBool.implies a₀ b)

with kNat.rw_one : kNat → kNat → Prop
	| eqe_left {a b c : kNat} : a =E b → kNat.rw_one b c → kNat.rw_one a c
	| eqe_right {a b c : kNat} : kNat.rw_one a b → b =E c → kNat.rw_one a c
	-- Axioms for rewriting inside subterms
	| sub_s {a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.s a) (kNat.s b)
	| sub_sum₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.sum a a₁) (kNat.sum b a₁)
	| sub_sum₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.sum a₀ a) (kNat.sum a₀ b)
	-- Rewrite rules
	| rl_cancel {n : kNat} : n ⊳ MSort.NzNat → n ⊳ MSort.Even → kNat.rw_one (kNat.s n) n

with kBool.rw_star : kBool → kBool → Prop
	| step {a b} : kBool.rw_one a b → kBool.rw_star a b
	| refl {a b : kBool} : a =E b → kBool.rw_star a b
	| trans {a b c} : kBool.rw_star a b → kBool.rw_star b c → kBool.rw_star a c

with kNat.rw_star : kNat → kNat → Prop
	| step {a b} : kNat.rw_one a b → kNat.rw_star a b
	| refl {a b : kNat} : a =E b → kNat.rw_star a b
	| trans {a b c} : kNat.rw_star a b → kNat.rw_star b c → kNat.rw_star a c

infix (name := kBool_rw_one) ` =>1 `:40 := kBool.rw_one
infix (name := kNat_rw_one) ` =>1 `:40 := kNat.rw_one

infix (name := kBool_rw_star) ` =>* `:40 := kBool.rw_star
infix (name := kNat_rw_star) ` =>* `:40 := kNat.rw_star

-- Lemmas and aliases

/-- Congruence lemma for generic relations -/
lemma generic_congr {α : Type} {rl ru : α → α → Prop}
	(cleft : ∀ {x y z}, rl x y → ru y z → ru x z)
	(cright : ∀ {x y z}, ru x y → rl y z → ru x z)
	(asymm : ∀ {x y}, rl x y → rl y x)
	{a₀ a₁ b₀ b₁ : α} : rl a₀ b₀ → rl a₁ b₁ → (ru a₀ a₁) = (ru b₀ b₁) :=
begin
	intros h₀ h₁,
	apply iff.to_eq,
	split,
	{ intro h, exact cright (cleft (asymm h₀) h) h₁, },
	{ intro h, exact cright (cleft h₀ h) (asymm h₁), },
end


namespace kBool
	-- Sort membership lemmas

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kBool) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kBool} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kBool} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kBool} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Aliases
	def and_comm := @eqa.and_comm
	def and_assoc := @eqa.and_assoc
	def or_comm := @eqa.or_comm
	def or_assoc := @eqa.or_assoc
	def xor_comm := @eqa.xor_comm
	def xor_assoc := @eqa.xor_assoc
	def true_decl := @has_sort.true_decl
	def false_decl := @has_sort.false_decl
	def and_decl := @has_sort.and_decl
	def or_decl := @has_sort.or_decl
	def xor_decl := @has_sort.xor_decl
	def not_decl := @has_sort.not_decl
	def implies_decl := @has_sort.implies_decl
	def eqa_and := @eqa.eqa_and
	def eqe_and := @eqe.eqe_and
	def eqa_or := @eqa.eqa_or
	def eqe_or := @eqe.eqe_or
	def eqa_xor := @eqa.eqa_xor
	def eqe_xor := @eqe.eqe_xor
	def eqa_not := @eqa.eqa_not
	def eqe_not := @eqe.eqe_not
	def eqa_implies := @eqa.eqa_implies
	def eqe_implies := @eqe.eqe_implies
	def eq_and₀ := @eqe.eq_and₀
	def eq_and₁ := @eqe.eq_and₁
	def eq_and₂ := @eqe.eq_and₂
	def eq_xor₀ := @eqe.eq_xor₀
	def eq_xor₁ := @eqe.eq_xor₁
	def eq_and₃ := @eqe.eq_and₃
	def eq_not := @eqe.eq_not
	def eq_or := @eqe.eq_or
	def eq_implies := @eqe.eq_implies

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_and eqe.eqe_and eqa.eqa_or eqe.eqe_or eqa.eqa_xor eqe.eqe_xor eqa.eqa_not eqe.eqe_not eqa.eqa_implies eqe.eqe_implies eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.true_decl has_sort.false_decl has_sort.and_decl has_sort.or_decl has_sort.xor_decl has_sort.not_decl has_sort.implies_decl eqe.eq_and₀ eqe.eq_and₁ eqe.eq_and₂ eqe.eq_xor₀ eqe.eq_xor₁ eqe.eq_and₃ eqe.eq_not eqe.eq_or eqe.eq_implies
end kBool

namespace kNat
	-- Sort membership lemmas
	lemma subsort_nznat_nat {t : kNat} : t ⊳ MSort.NzNat →
		t ⊳ MSort.Nat := by apply has_sort.subsort; simp [subsort]
	lemma subsort_even_nat {t : kNat} : t ⊳ MSort.Even →
		t ⊳ MSort.Nat := by apply has_sort.subsort; simp [subsort]

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kNat) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kNat} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kNat} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kNat} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Aliases
	def zero_decl := @has_sort.zero_decl
	def s_decl := @has_sort.s_decl
	def sum_decl := @has_sort.sum_decl
	def mb_s := @has_sort.mb_s
	def eqa_s := @eqa.eqa_s
	def eqe_s := @eqe.eqe_s
	def eqa_sum := @eqa.eqa_sum
	def eqe_sum := @eqe.eqe_sum
	def eq_sum₀ := @eqe.eq_sum₀
	def eq_sum₁ := @eqe.eq_sum₁

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_s eqe.eqe_s eqa.eqa_sum eqe.eqe_sum eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.zero_decl has_sort.s_decl has_sort.sum_decl has_sort.mb_s eqe.eq_sum₀ eqe.eq_sum₁ subsort_nznat_nat subsort_even_nat
end kNat

-- Lemmas for the rewriting relation

/-- Repeat a tactic a given number of times -/
meta def repeat_ntimes {α : Type} (t : tactic α) : ℕ → tactic unit
	| 0            := return ()
	| (nat.succ n) := do t, repeat_ntimes n

/-- Tactic to generically prove that =>* can be applied inside subterms -/
meta def infer_sub_star (rl eq : pexpr) : tactic unit :=
do {
	-- Proceed by induction on the =>* relation
	h ← tactic.intro `h,
	[cstep, crefl, ctrans] ← tactic.induction h,
	-- (1) step case: we reproduce the step with =>*
	rso ← tactic.i_to_expr_for_apply ```(rw_star.step),
	tactic.apply rso,
	rosn ← tactic.i_to_expr_for_apply rl,
	tactic.apply rosn,
	hs ← cstep.snd.fst.nth 2, -- case hypothesis
	tactic.exact hs,
	-- (2) refl case: we invoke the refl axiom for =>*
	tactic.reflexivity,
	ha ← crefl.snd.fst.nth 2,
	eqe ← tactic.i_to_expr_for_apply eq,
	tactic.apply eqe,
	subgoals ← tactic.get_goals,
	repeat_ntimes (tactic.reflexivity <|> tactic.exact ha) (subgoals.length - 1),
	-- (3) trans case: we use the induction hypotheses
	tactic.transitivity,
	hab ← ctrans.snd.fst.nth 5, -- a =>* b (induction hypothesis)
	hbc ← ctrans.snd.fst.nth 6, -- b =>* c (induction hypothesis)
	tactic.exact hab,
	tactic.exact hbc,
	return ()
} <|> tactic.fail "infer_sub_fail tactic failed"


namespace kBool
	-- Congruence lemmas
	@[congr] lemma eqe_rw_one_congr {a b c d : kBool} : a =E b → c =E d → (a =>1 c) = (b =>1 d)
		:= generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
	@[congr] lemma eqa_rw_one_congr {a b c d : kBool} : a =A b → c =A d → (a =>1 c) = (b =>1 d)
		:= generic_congr (λ {x y z}, (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
	@[congr] lemma eqe_rw_star_congr {a b c d : kBool} : a =E b → c =E d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
	@[congr] lemma eqa_rw_star_congr {a b c d : kBool} : a =A b → c =A d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] rw_star.refl
	attribute [trans] rw_star.trans

	-- Lemmas for subterm rewriting with =>*
	lemma rw_star_sub_and₀ {a b a₁ : kBool} : a =>* b →
			(and a a₁) =>* (and b a₁) := by infer_sub_star ``(rw_one.sub_and₀) ``(eqe.eqe_and)
	lemma rw_star_sub_and₁ {a₀ a b : kBool} : a =>* b →
			(and a₀ a) =>* (and a₀ b) := by infer_sub_star ``(rw_one.sub_and₁) ``(eqe.eqe_and)
	lemma rw_star_sub_or₀ {a b a₁ : kBool} : a =>* b →
			(or a a₁) =>* (or b a₁) := by infer_sub_star ``(rw_one.sub_or₀) ``(eqe.eqe_or)
	lemma rw_star_sub_or₁ {a₀ a b : kBool} : a =>* b →
			(or a₀ a) =>* (or a₀ b) := by infer_sub_star ``(rw_one.sub_or₁) ``(eqe.eqe_or)
	lemma rw_star_sub_xor₀ {a b a₁ : kBool} : a =>* b →
			(xor a a₁) =>* (xor b a₁) := by infer_sub_star ``(rw_one.sub_xor₀) ``(eqe.eqe_xor)
	lemma rw_star_sub_xor₁ {a₀ a b : kBool} : a =>* b →
			(xor a₀ a) =>* (xor a₀ b) := by infer_sub_star ``(rw_one.sub_xor₁) ``(eqe.eqe_xor)
	lemma rw_star_sub_not {a b : kBool} : a =>* b →
			(not a) =>* (not b) := by infer_sub_star ``(rw_one.sub_not) ``(eqe.eqe_not)
	lemma rw_star_sub_implies₀ {a b a₁ : kBool} : a =>* b →
			(implies a a₁) =>* (implies b a₁) := by infer_sub_star ``(rw_one.sub_implies₀) ``(eqe.eqe_implies)
	lemma rw_star_sub_implies₁ {a₀ a b : kBool} : a =>* b →
			(implies a₀ a) =>* (implies a₀ b) := by infer_sub_star ``(rw_one.sub_implies₁) ``(eqe.eqe_implies)
end kBool

namespace kNat
	-- Congruence lemmas
	@[congr] lemma eqe_rw_one_congr {a b c d : kNat} : a =E b → c =E d → (a =>1 c) = (b =>1 d)
		:= generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
	@[congr] lemma eqa_rw_one_congr {a b c d : kNat} : a =A b → c =A d → (a =>1 c) = (b =>1 d)
		:= generic_congr (λ {x y z}, (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
	@[congr] lemma eqe_rw_star_congr {a b c d : kNat} : a =E b → c =E d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
	@[congr] lemma eqa_rw_star_congr {a b c d : kNat} : a =A b → c =A d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Aliases for rewrite rules
	def rl_cancel := @rw_one.rl_cancel

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] rw_star.refl
	attribute [trans] rw_star.trans

	-- Lemmas for subterm rewriting with =>*
	lemma rw_star_sub_s {a b : kNat} : a =>* b →
			(s a) =>* (s b) := by infer_sub_star ``(rw_one.sub_s) ``(eqe.eqe_s)
	lemma rw_star_sub_sum₀ {a b a₁ : kNat} : a =>* b →
			(sum a a₁) =>* (sum b a₁) := by infer_sub_star ``(rw_one.sub_sum₀) ``(eqe.eqe_sum)
	lemma rw_star_sub_sum₁ {a₀ a b : kNat} : a =>* b →
			(sum a₀ a) =>* (sum a₀ b) := by infer_sub_star ``(rw_one.sub_sum₁) ``(eqe.eqe_sum)
end kNat

-- String conversion

def kBool.repr : kBool → string
	| kBool.true := "true"
	| kBool.false := "false"
	| (kBool.and a₀ a₁) := "_and_(" ++ (a₀.repr) ++ ", " ++ (a₁.repr) ++ ")"
	| (kBool.or a₀ a₁) := "_or_(" ++ (a₀.repr) ++ ", " ++ (a₁.repr) ++ ")"
	| (kBool.xor a₀ a₁) := "_xor_(" ++ (a₀.repr) ++ ", " ++ (a₁.repr) ++ ")"
	| (kBool.not a) := "not_(" ++ (a.repr) ++ ")"
	| (kBool.implies a₀ a₁) := "_implies_(" ++ (a₀.repr) ++ ", " ++ (a₁.repr) ++ ")"

def kNat.repr : kNat → string
	| kNat.zero := "0"
	| (kNat.s a) := "s_(" ++ (a.repr) ++ ")"
	| (kNat.sum a₀ a₁) := "_+_(" ++ (a₀.repr) ++ ", " ++ (a₁.repr) ++ ")"

instance : has_repr kBool := ⟨ kBool.repr ⟩
instance : has_repr kNat := ⟨ kNat.repr ⟩

end Maude
