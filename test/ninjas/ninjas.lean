namespace Maude

-- Sorts
inductive MSort
	| Bool
	| Mode
	| Vote
	| Ninja
	| Garden

-- Generator of the subsort relation
def subsort : MSort → MSort → Prop
	| MSort.Ninja MSort.Garden := true
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

inductive kMode
	| A
	| P

inductive kVote
	| Y
	| N

inductive kGarden
	| ninja : kMode → kVote → kGarden
	| empty
	| join : kGarden → kGarden → kGarden

-- Kind assignment
def kind : MSort → Type
	| MSort.Bool := kBool
	| MSort.Mode := kMode
	| MSort.Vote := kVote
	| MSort.Ninja := kGarden
	| MSort.Garden := kGarden

-- Predicates recognizing constructor terms
mutual def kBool.ctor_only, kMode.ctor_only, kVote.ctor_only, kGarden.ctor_only

with kBool.ctor_only : kBool → Prop
	| kBool.true := true
	| kBool.false := true
	| _ := false

with kMode.ctor_only : kMode → Prop
	| kMode.A := true
	| kMode.P := true

with kVote.ctor_only : kVote → Prop
	| kVote.Y := true
	| kVote.N := true

with kGarden.ctor_only : kGarden → Prop
	| (kGarden.ninja a₀ a₁) := a₀.ctor_only ∧ a₁.ctor_only
	| kGarden.empty := true
	| (kGarden.join a₀ a₁) := a₀.ctor_only ∧ a₁.ctor_only

-- Equality modulo axioms
mutual inductive kBool.eqa, kMode.eqa, kVote.eqa, kGarden.eqa

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

with kMode.eqa : kMode → kMode → Prop
	| refl {a} : kMode.eqa a a
	| symm {a b} : kMode.eqa a b → kMode.eqa b a
	| trans {a b c} : kMode.eqa a b → kMode.eqa b c → kMode.eqa a c
	-- Congruence axioms for each operator

with kVote.eqa : kVote → kVote → Prop
	| refl {a} : kVote.eqa a a
	| symm {a b} : kVote.eqa a b → kVote.eqa b a
	| trans {a b c} : kVote.eqa a b → kVote.eqa b c → kVote.eqa a c
	-- Congruence axioms for each operator

with kGarden.eqa : kGarden → kGarden → Prop
	| refl {a} : kGarden.eqa a a
	| symm {a b} : kGarden.eqa a b → kGarden.eqa b a
	| trans {a b c} : kGarden.eqa a b → kGarden.eqa b c → kGarden.eqa a c
	-- Congruence axioms for each operator
	| eqa_ninja {a₀ b₀ : kMode} {a₁ b₁ : kVote} : kMode.eqa a₀ b₀ → kVote.eqa a₁ b₁ → kGarden.eqa (kGarden.ninja a₀ a₁) (kGarden.ninja b₀ b₁)
	| eqa_join {a₀ b₀ a₁ b₁ : kGarden} : kGarden.eqa a₀ b₀ → kGarden.eqa a₁ b₁ → kGarden.eqa (kGarden.join a₀ a₁) (kGarden.join b₀ b₁)
	-- Structural axioms
	| join_comm {a b} : kGarden.eqa (kGarden.join a b) (kGarden.join b a)
	| join_assoc {a b c} : kGarden.eqa (kGarden.join a (kGarden.join b c)) (kGarden.join (kGarden.join a b) c)
	| join_left_id {a} : kGarden.eqa (kGarden.join kGarden.empty a) a
	| join_right_id {a} : kGarden.eqa (kGarden.join a kGarden.empty) a

-- Sort membership and equality modulo equations

mutual inductive kBool.has_sort, kMode.has_sort, kVote.has_sort, kGarden.has_sort, kBool.eqe, kMode.eqe, kVote.eqe, kGarden.eqe
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

with kMode.has_sort : kMode → MSort → Prop
	| subsort {t a b} : subsort a b → kMode.has_sort t a → kMode.has_sort t b
	-- Implicit membership axioms (operator declarations)
	| A_decl : kMode.has_sort kMode.A MSort.Mode
	| P_decl : kMode.has_sort kMode.P MSort.Mode

with kVote.has_sort : kVote → MSort → Prop
	| subsort {t a b} : subsort a b → kVote.has_sort t a → kVote.has_sort t b
	-- Implicit membership axioms (operator declarations)
	| Y_decl : kVote.has_sort kVote.Y MSort.Vote
	| N_decl : kVote.has_sort kVote.N MSort.Vote

with kGarden.has_sort : kGarden → MSort → Prop
	| subsort {t a b} : subsort a b → kGarden.has_sort t a → kGarden.has_sort t b
	-- Implicit membership axioms (operator declarations)
	| ninja_decl {a₀ : kMode} {a₁ : kVote} : kMode.has_sort a₀ MSort.Mode → kVote.has_sort a₁ MSort.Vote → kGarden.has_sort (kGarden.ninja a₀ a₁) MSort.Ninja
	| empty_decl : kGarden.has_sort kGarden.empty MSort.Garden
	| join_decl {a₀ a₁ : kGarden} : kGarden.has_sort a₀ MSort.Garden → kGarden.has_sort a₁ MSort.Garden → kGarden.has_sort (kGarden.join a₀ a₁) MSort.Garden

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

with kMode.eqe : kMode → kMode → Prop
	| from_eqa {a b} : kMode.eqa a b → kMode.eqe a b
	| symm {a b} : kMode.eqe a b → kMode.eqe b a
	| trans {a b c} : kMode.eqe a b → kMode.eqe b c → kMode.eqe a c
	-- Congruence axioms for each operator

with kVote.eqe : kVote → kVote → Prop
	| from_eqa {a b} : kVote.eqa a b → kVote.eqe a b
	| symm {a b} : kVote.eqe a b → kVote.eqe b a
	| trans {a b c} : kVote.eqe a b → kVote.eqe b c → kVote.eqe a c
	-- Congruence axioms for each operator

with kGarden.eqe : kGarden → kGarden → Prop
	| from_eqa {a b} : kGarden.eqa a b → kGarden.eqe a b
	| symm {a b} : kGarden.eqe a b → kGarden.eqe b a
	| trans {a b c} : kGarden.eqe a b → kGarden.eqe b c → kGarden.eqe a c
	-- Congruence axioms for each operator
	| eqe_ninja {a₀ b₀ : kMode} {a₁ b₁ : kVote} : kMode.eqe a₀ b₀ → kVote.eqe a₁ b₁ → kGarden.eqe (kGarden.ninja a₀ a₁) (kGarden.ninja b₀ b₁)
	| eqe_join {a₀ b₀ a₁ b₁ : kGarden} : kGarden.eqe a₀ b₀ → kGarden.eqe a₁ b₁ → kGarden.eqe (kGarden.join a₀ a₁) (kGarden.join b₀ b₁)

infix (name := kBool_has_sort) ` ⊳ `:40 := kBool.has_sort
infix (name := kMode_has_sort) ` ⊳ `:40 := kMode.has_sort
infix (name := kVote_has_sort) ` ⊳ `:40 := kVote.has_sort
infix (name := kGarden_has_sort) ` ⊳ `:40 := kGarden.has_sort

infix (name := kBool_eqa) ` =A `:40 := kBool.eqa
infix (name := kMode_eqa) ` =A `:40 := kMode.eqa
infix (name := kVote_eqa) ` =A `:40 := kVote.eqa
infix (name := kGarden_eqa) ` =A `:40 := kGarden.eqa

infix (name := kBool_eqe) ` =E `:40 := kBool.eqe
infix (name := kMode_eqe) ` =E `:40 := kMode.eqe
infix (name := kVote_eqe) ` =E `:40 := kVote.eqe
infix (name := kGarden_eqe) ` =E `:40 := kGarden.eqe

-- Rewriting relations

mutual inductive kBool.rw_one, kMode.rw_one, kVote.rw_one, kGarden.rw_one, kBool.rw_star, kMode.rw_star, kVote.rw_star, kGarden.rw_star
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

with kMode.rw_one : kMode → kMode → Prop
	| eqe_left {a b c : kMode} : a =E b → kMode.rw_one b c → kMode.rw_one a c
	| eqe_right {a b c : kMode} : kMode.rw_one a b → b =E c → kMode.rw_one a c
	-- Axioms for rewriting inside subterms

with kVote.rw_one : kVote → kVote → Prop
	| eqe_left {a b c : kVote} : a =E b → kVote.rw_one b c → kVote.rw_one a c
	| eqe_right {a b c : kVote} : kVote.rw_one a b → b =E c → kVote.rw_one a c
	-- Axioms for rewriting inside subterms

with kGarden.rw_one : kGarden → kGarden → Prop
	| eqe_left {a b c : kGarden} : a =E b → kGarden.rw_one b c → kGarden.rw_one a c
	| eqe_right {a b c : kGarden} : kGarden.rw_one a b → b =E c → kGarden.rw_one a c
	-- Axioms for rewriting inside subterms
	| sub_ninja₀ {a₁ a b} : kMode.rw_one a b →
		kGarden.rw_one (kGarden.ninja a a₁) (kGarden.ninja b a₁)
	| sub_ninja₁ {a₀ a b} : kVote.rw_one a b →
		kGarden.rw_one (kGarden.ninja a₀ a) (kGarden.ninja a₀ b)
	| sub_join₀ {a₁ a b} : kGarden.rw_one a b →
		kGarden.rw_one (kGarden.join a a₁) (kGarden.join b a₁)
	| sub_join₁ {a₀ a b} : kGarden.rw_one a b →
		kGarden.rw_one (kGarden.join a₀ a) (kGarden.join a₀ b)
	-- Rewrite rules
	| rl_r1 : kGarden.rw_one (kGarden.join (kGarden.ninja kMode.A kVote.Y) (kGarden.ninja kMode.A kVote.N)) (kGarden.join (kGarden.ninja kMode.P kVote.N) (kGarden.ninja kMode.P kVote.N))
	| rl_r2 {v w : kVote} : kGarden.rw_one (kGarden.join (kGarden.ninja kMode.A v) (kGarden.ninja kMode.P w)) (kGarden.join (kGarden.ninja kMode.A v) (kGarden.ninja kMode.P v))
	| rl_r3 : kGarden.rw_one (kGarden.join (kGarden.ninja kMode.P kVote.Y) (kGarden.ninja kMode.P kVote.N)) (kGarden.join (kGarden.ninja kMode.P kVote.N) (kGarden.ninja kMode.P kVote.N))

with kBool.rw_star : kBool → kBool → Prop
	| step {a b} : kBool.rw_one a b → kBool.rw_star a b
	| refl {a b : kBool} : a =E b → kBool.rw_star a b
	| trans {a b c} : kBool.rw_star a b → kBool.rw_star b c → kBool.rw_star a c

with kMode.rw_star : kMode → kMode → Prop
	| step {a b} : kMode.rw_one a b → kMode.rw_star a b
	| refl {a b : kMode} : a =E b → kMode.rw_star a b
	| trans {a b c} : kMode.rw_star a b → kMode.rw_star b c → kMode.rw_star a c

with kVote.rw_star : kVote → kVote → Prop
	| step {a b} : kVote.rw_one a b → kVote.rw_star a b
	| refl {a b : kVote} : a =E b → kVote.rw_star a b
	| trans {a b c} : kVote.rw_star a b → kVote.rw_star b c → kVote.rw_star a c

with kGarden.rw_star : kGarden → kGarden → Prop
	| step {a b} : kGarden.rw_one a b → kGarden.rw_star a b
	| refl {a b : kGarden} : a =E b → kGarden.rw_star a b
	| trans {a b c} : kGarden.rw_star a b → kGarden.rw_star b c → kGarden.rw_star a c

infix (name := kBool_rw_one) ` =>1 `:40 := kBool.rw_one
infix (name := kMode_rw_one) ` =>1 `:40 := kMode.rw_one
infix (name := kVote_rw_one) ` =>1 `:40 := kVote.rw_one
infix (name := kGarden_rw_one) ` =>1 `:40 := kGarden.rw_one

infix (name := kBool_rw_star) ` =>* `:40 := kBool.rw_star
infix (name := kMode_rw_star) ` =>* `:40 := kMode.rw_star
infix (name := kVote_rw_star) ` =>* `:40 := kVote.rw_star
infix (name := kGarden_rw_star) ` =>* `:40 := kGarden.rw_star

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

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_and eqe.eqe_and eqa.eqa_or eqe.eqe_or eqa.eqa_xor eqe.eqe_xor eqa.eqa_not eqe.eqe_not eqa.eqa_implies eqe.eqe_implies eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.true_decl has_sort.false_decl has_sort.and_decl has_sort.or_decl has_sort.xor_decl has_sort.not_decl has_sort.implies_decl eqe.eq_and₀ eqe.eq_and₁ eqe.eq_and₂ eqe.eq_xor₀ eqe.eq_xor₁ eqe.eq_and₃ eqe.eq_not eqe.eq_or eqe.eq_implies
end kBool

namespace kMode
	-- Sort membership lemmas

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kMode) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kMode} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kMode} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kMode} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.A_decl has_sort.P_decl
end kMode

namespace kVote
	-- Sort membership lemmas

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kVote) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kVote} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kVote} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kVote} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.Y_decl has_sort.N_decl
end kVote

namespace kGarden
	-- Sort membership lemmas
	lemma subsort_ninja_garden {t : kGarden} : t ⊳ MSort.Ninja →
		t ⊳ MSort.Garden := by apply has_sort.subsort; simp [subsort]

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kGarden) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kGarden} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kGarden} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kGarden} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_ninja eqe.eqe_ninja eqa.eqa_join eqe.eqe_join eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.ninja_decl has_sort.empty_decl has_sort.join_decl subsort_ninja_garden
end kGarden

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

namespace kMode
	-- Congruence lemmas
	@[congr] lemma eqe_rw_one_congr {a b c d : kMode} : a =E b → c =E d → (a =>1 c) = (b =>1 d)
		:= generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
	@[congr] lemma eqa_rw_one_congr {a b c d : kMode} : a =A b → c =A d → (a =>1 c) = (b =>1 d)
		:= generic_congr (λ {x y z}, (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
	@[congr] lemma eqe_rw_star_congr {a b c d : kMode} : a =E b → c =E d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
	@[congr] lemma eqa_rw_star_congr {a b c d : kMode} : a =A b → c =A d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] rw_star.refl
	attribute [trans] rw_star.trans

	-- Lemmas for subterm rewriting with =>*
end kMode

namespace kVote
	-- Congruence lemmas
	@[congr] lemma eqe_rw_one_congr {a b c d : kVote} : a =E b → c =E d → (a =>1 c) = (b =>1 d)
		:= generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
	@[congr] lemma eqa_rw_one_congr {a b c d : kVote} : a =A b → c =A d → (a =>1 c) = (b =>1 d)
		:= generic_congr (λ {x y z}, (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
	@[congr] lemma eqe_rw_star_congr {a b c d : kVote} : a =E b → c =E d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
	@[congr] lemma eqa_rw_star_congr {a b c d : kVote} : a =A b → c =A d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] rw_star.refl
	attribute [trans] rw_star.trans

	-- Lemmas for subterm rewriting with =>*
end kVote

namespace kGarden
	-- Congruence lemmas
	@[congr] lemma eqe_rw_one_congr {a b c d : kGarden} : a =E b → c =E d → (a =>1 c) = (b =>1 d)
		:= generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
	@[congr] lemma eqa_rw_one_congr {a b c d : kGarden} : a =A b → c =A d → (a =>1 c) = (b =>1 d)
		:= generic_congr (λ {x y z}, (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
	@[congr] lemma eqe_rw_star_congr {a b c d : kGarden} : a =E b → c =E d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
	@[congr] lemma eqa_rw_star_congr {a b c d : kGarden} : a =A b → c =A d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] rw_star.refl
	attribute [trans] rw_star.trans

	-- Lemmas for subterm rewriting with =>*
	lemma rw_star_sub_ninja₀ {a b : kMode} {a₁ : kVote} : a =>* b →
			(ninja a a₁) =>* (ninja b a₁) := by infer_sub_star ``(rw_one.sub_ninja₀) ``(eqe.eqe_ninja)
	lemma rw_star_sub_ninja₁ {a₀ : kMode} {a b : kVote} : a =>* b →
			(ninja a₀ a) =>* (ninja a₀ b) := by infer_sub_star ``(rw_one.sub_ninja₁) ``(eqe.eqe_ninja)
	lemma rw_star_sub_join₀ {a b a₁ : kGarden} : a =>* b →
			(join a a₁) =>* (join b a₁) := by infer_sub_star ``(rw_one.sub_join₀) ``(eqe.eqe_join)
	lemma rw_star_sub_join₁ {a₀ a b : kGarden} : a =>* b →
			(join a₀ a) =>* (join a₀ b) := by infer_sub_star ``(rw_one.sub_join₁) ``(eqe.eqe_join)
end kGarden

end Maude
