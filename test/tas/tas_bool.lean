namespace Maude

-- Sorts
inductive MSort
	| Pid
	| Label
	| Status
	| Sys

-- Generator of the subsort relation
def subsort : MSort → MSort → Prop
	| _ _ := false

-- Kinds and their operators
constant kPid : Type

inductive kSys
	| init
	| enter : kSys → kPid → kSys
	| leave : kSys → kPid → kSys

inductive kStatus
	| sopen
	| close
	| lock : kSys → kStatus

inductive kLabel
	| rs
	| cs
	| pc : kSys → kPid → kLabel

-- Lean-native replacements of Maude types
-- (enabled by option with-native-bool)

namespace bool
	-- Non-native operators
	constant xor : bool → bool → bool
	constant implies : bool → bool → bool
	constant «~»₀ : kPid → kPid → bool
	constant «~»₁ : kLabel → kLabel → bool
	constant «~»₂ : kStatus → kStatus → bool
	constant csubenter : kSys → kPid → bool
	constant csubleave : kSys → kPid → bool
end bool

-- Kind assignment
def kind : MSort → Type
	| MSort.Pid := kPid
	| MSort.Label := kLabel
	| MSort.Status := kStatus
	| MSort.Sys := kSys

-- Predicates recognizing constructor terms
mutual def kPid.ctor_only, kLabel.ctor_only, kStatus.ctor_only, kSys.ctor_only

with kPid.ctor_only : kPid → Prop
	| _ := true

with kLabel.ctor_only : kLabel → Prop
	| kLabel.rs := true
	| kLabel.cs := true
	| _ := false

with kStatus.ctor_only : kStatus → Prop
	| kStatus.sopen := true
	| kStatus.close := true
	| _ := false

with kSys.ctor_only : kSys → Prop
	| kSys.init := true
	| (kSys.enter a₀ a₁) := a₀.ctor_only ∧ a₁.ctor_only
	| (kSys.leave a₀ a₁) := a₀.ctor_only ∧ a₁.ctor_only

-- Equality modulo axioms
mutual inductive kPid.eqa, kLabel.eqa, kStatus.eqa, kSys.eqa

with kPid.eqa : kPid → kPid → Prop
	| refl {a} : kPid.eqa a a
	| symm {a b} : kPid.eqa a b → kPid.eqa b a
	| trans {a b c} : kPid.eqa a b → kPid.eqa b c → kPid.eqa a c
	-- Congruence axioms for each operator

with kLabel.eqa : kLabel → kLabel → Prop
	| refl {a} : kLabel.eqa a a
	| symm {a b} : kLabel.eqa a b → kLabel.eqa b a
	| trans {a b c} : kLabel.eqa a b → kLabel.eqa b c → kLabel.eqa a c
	-- Congruence axioms for each operator
	| eqa_pc {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqa a₀ b₀ → kPid.eqa a₁ b₁ → kLabel.eqa (kLabel.pc a₀ a₁) (kLabel.pc b₀ b₁)

with kStatus.eqa : kStatus → kStatus → Prop
	| refl {a} : kStatus.eqa a a
	| symm {a b} : kStatus.eqa a b → kStatus.eqa b a
	| trans {a b c} : kStatus.eqa a b → kStatus.eqa b c → kStatus.eqa a c
	-- Congruence axioms for each operator
	| eqa_lock {a b : kSys} : kSys.eqa a b → kStatus.eqa (kStatus.lock a) (kStatus.lock b)

with kSys.eqa : kSys → kSys → Prop
	| refl {a} : kSys.eqa a a
	| symm {a b} : kSys.eqa a b → kSys.eqa b a
	| trans {a b c} : kSys.eqa a b → kSys.eqa b c → kSys.eqa a c
	-- Congruence axioms for each operator
	| eqa_enter {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqa a₀ b₀ → kPid.eqa a₁ b₁ → kSys.eqa (kSys.enter a₀ a₁) (kSys.enter b₀ b₁)
	| eqa_leave {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqa a₀ b₀ → kPid.eqa a₁ b₁ → kSys.eqa (kSys.leave a₀ a₁) (kSys.leave b₀ b₁)

-- Sort membership and equality modulo equations

mutual inductive kPid.has_sort, kLabel.has_sort, kStatus.has_sort, kSys.has_sort, kPid.eqe, kLabel.eqe, kStatus.eqe, kSys.eqe
with kPid.has_sort : kPid → MSort → Prop
	| subsort {t a b} : subsort a b → kPid.has_sort t a → kPid.has_sort t b
	-- Implicit membership axioms (operator declarations)

with kLabel.has_sort : kLabel → MSort → Prop
	| subsort {t a b} : subsort a b → kLabel.has_sort t a → kLabel.has_sort t b
	-- Implicit membership axioms (operator declarations)
	-- op rs : -> Label .
	| rs_decl : kLabel.has_sort kLabel.rs MSort.Label
	-- op cs : -> Label .
	| cs_decl : kLabel.has_sort kLabel.cs MSort.Label
	-- op pc : Sys X$Pid -> Label .
	| pc_decl {a₀ : kSys} {a₁ : kPid} : kSys.has_sort a₀ MSort.Sys → kPid.has_sort a₁ MSort.Pid → kLabel.has_sort (kLabel.pc a₀ a₁) MSort.Label

with kStatus.has_sort : kStatus → MSort → Prop
	| subsort {t a b} : subsort a b → kStatus.has_sort t a → kStatus.has_sort t b
	-- Implicit membership axioms (operator declarations)
	-- op open : -> Status .
	| sopen_decl : kStatus.has_sort kStatus.sopen MSort.Status
	-- op close : -> Status .
	| close_decl : kStatus.has_sort kStatus.close MSort.Status
	-- op lock : Sys -> Status .
	| lock_decl {a : kSys} : kSys.has_sort a MSort.Sys → kStatus.has_sort (kStatus.lock a) MSort.Status

with kSys.has_sort : kSys → MSort → Prop
	| subsort {t a b} : subsort a b → kSys.has_sort t a → kSys.has_sort t b
	-- Implicit membership axioms (operator declarations)
	-- op init : -> Sys .
	| init_decl : kSys.has_sort kSys.init MSort.Sys
	-- op enter : Sys X$Pid -> Sys .
	| enter_decl {a₀ : kSys} {a₁ : kPid} : kSys.has_sort a₀ MSort.Sys → kPid.has_sort a₁ MSort.Pid → kSys.has_sort (kSys.enter a₀ a₁) MSort.Sys
	-- op leave : Sys X$Pid -> Sys .
	| leave_decl {a₀ : kSys} {a₁ : kPid} : kSys.has_sort a₀ MSort.Sys → kPid.has_sort a₁ MSort.Pid → kSys.has_sort (kSys.leave a₀ a₁) MSort.Sys

with kPid.eqe : kPid → kPid → Prop
	| from_eqa {a b} : kPid.eqa a b → kPid.eqe a b
	| symm {a b} : kPid.eqe a b → kPid.eqe b a
	| trans {a b c} : kPid.eqe a b → kPid.eqe b c → kPid.eqe a c
	-- Congruence axioms for each operator

with kLabel.eqe : kLabel → kLabel → Prop
	| from_eqa {a b} : kLabel.eqa a b → kLabel.eqe a b
	| symm {a b} : kLabel.eqe a b → kLabel.eqe b a
	| trans {a b c} : kLabel.eqe a b → kLabel.eqe b c → kLabel.eqe a c
	-- Congruence axioms for each operator
	| eqe_pc {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqe a₀ b₀ → kPid.eqe a₁ b₁ → kLabel.eqe (kLabel.pc a₀ a₁) (kLabel.pc b₀ b₁)
	-- Equations
	-- eq pc(init, I) = rs [metadata "CA-I1"] .
	| eq_pc₀ {i} : kLabel.eqe (kLabel.pc kSys.init i) kLabel.rs
	-- ceq pc(enter(S, I), J) = if I ~ J then cs else pc(S, J) fi if c-enter(S, I) = true .
	| eq_pc₁ {s i j} : (bool.csubenter s i) = tt → kLabel.eqe (kLabel.pc (kSys.enter s i) j) (cond (bool.«~»₀ i j) kLabel.cs (kLabel.pc s j))
	-- ceq pc(leave(S, I), J) = if I ~ J then rs else pc(S, J) fi if c-leave(S, I) = true .
	| eq_pc₂ {s i j} : (bool.csubleave s i) = tt → kLabel.eqe (kLabel.pc (kSys.leave s i) j) (cond (bool.«~»₀ i j) kLabel.rs (kLabel.pc s j))

with kStatus.eqe : kStatus → kStatus → Prop
	| from_eqa {a b} : kStatus.eqa a b → kStatus.eqe a b
	| symm {a b} : kStatus.eqe a b → kStatus.eqe b a
	| trans {a b c} : kStatus.eqe a b → kStatus.eqe b c → kStatus.eqe a c
	-- Congruence axioms for each operator
	| eqe_lock {a b : kSys} : kSys.eqe a b → kStatus.eqe (kStatus.lock a) (kStatus.lock b)
	-- Equations
	-- eq lock(init) = open [metadata "CA-I2"] .
	| eq_lock₀ : kStatus.eqe (kStatus.lock kSys.init) kStatus.sopen
	-- ceq lock(enter(S, I)) = close if c-enter(S, I) = true .
	| eq_lock₁ {s i} : (bool.csubenter s i) = tt → kStatus.eqe (kStatus.lock (kSys.enter s i)) kStatus.close
	-- ceq lock(leave(S, I)) = open if c-leave(S, I) = true .
	| eq_lock₂ {s i} : (bool.csubleave s i) = tt → kStatus.eqe (kStatus.lock (kSys.leave s i)) kStatus.sopen

with kSys.eqe : kSys → kSys → Prop
	| from_eqa {a b} : kSys.eqa a b → kSys.eqe a b
	| symm {a b} : kSys.eqe a b → kSys.eqe b a
	| trans {a b c} : kSys.eqe a b → kSys.eqe b c → kSys.eqe a c
	-- Congruence axioms for each operator
	| eqe_enter {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqe a₀ b₀ → kPid.eqe a₁ b₁ → kSys.eqe (kSys.enter a₀ a₁) (kSys.enter b₀ b₁)
	| eqe_leave {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqe a₀ b₀ → kPid.eqe a₁ b₁ → kSys.eqe (kSys.leave a₀ a₁) (kSys.leave b₀ b₁)
	-- Equations
	-- ceq enter(S, I) = S if not c-enter(S, I) = true .
	| eq_enter {s i} : (¬ (bool.csubenter s i)) = tt → kSys.eqe (kSys.enter s i) s
	-- ceq leave(S, I) = S if not c-leave(S, I) = true .
	| eq_leave {s i} : (¬ (bool.csubleave s i)) = tt → kSys.eqe (kSys.leave s i) s

infix (name := kPid_has_sort) ` ⊳ `:40 := kPid.has_sort
infix (name := kLabel_has_sort) ` ⊳ `:40 := kLabel.has_sort
infix (name := kStatus_has_sort) ` ⊳ `:40 := kStatus.has_sort
infix (name := kSys_has_sort) ` ⊳ `:40 := kSys.has_sort

infix (name := kPid_eqa) ` =A `:40 := kPid.eqa
infix (name := kLabel_eqa) ` =A `:40 := kLabel.eqa
infix (name := kStatus_eqa) ` =A `:40 := kStatus.eqa
infix (name := kSys_eqa) ` =A `:40 := kSys.eqa

infix (name := kPid_eqe) ` =E `:40 := kPid.eqe
infix (name := kLabel_eqe) ` =E `:40 := kLabel.eqe
infix (name := kStatus_eqe) ` =E `:40 := kStatus.eqe
infix (name := kSys_eqe) ` =E `:40 := kSys.eqe

-- Axioms for the native replacements of Maude types
-- (enabled by option with-native-bool)

namespace bool
	-- Congruence axioms
	axiom eqe_xor {a₀ b₀ a₁ b₁ : bool} : a₀ = b₀ → a₁ = b₁ → (bool.xor a₀ a₁) = (bool.xor b₀ b₁)
	axiom eqe_implies {a₀ b₀ a₁ b₁ : bool} : a₀ = b₀ → a₁ = b₁ → (bool.implies a₀ a₁) = (bool.implies b₀ b₁)
	axiom eqe_«~»₀ {a₀ b₀ a₁ b₁ : kPid} : a₀ =E b₀ → a₁ =E b₁ → (bool.«~»₀ a₀ a₁) = (bool.«~»₀ b₀ b₁)
	axiom eqe_«~»₁ {a₀ b₀ a₁ b₁ : kLabel} : a₀ =E b₀ → a₁ =E b₁ → (bool.«~»₁ a₀ a₁) = (bool.«~»₁ b₀ b₁)
	axiom eqe_«~»₂ {a₀ b₀ a₁ b₁ : kStatus} : a₀ =E b₀ → a₁ =E b₁ → (bool.«~»₂ a₀ a₁) = (bool.«~»₂ b₀ b₁)
	axiom eqe_csubenter {a₀ b₀ : kSys} {a₁ b₁ : kPid} : a₀ =E b₀ → a₁ =E b₁ → (bool.csubenter a₀ a₁) = (bool.csubenter b₀ b₁)
	axiom eqe_csubleave {a₀ b₀ : kSys} {a₁ b₁ : kPid} : a₀ =E b₀ → a₁ =E b₁ → (bool.csubleave a₀ a₁) = (bool.csubleave b₀ b₁)
	-- Structural axioms
	axiom xor_comm {a b} : (bool.xor a b) = (bool.xor b a)
	axiom xor_assoc {a b c} : (bool.xor a (bool.xor b c)) = (bool.xor (bool.xor a b) c)
	axiom «~»₀_comm {a b} : (bool.«~»₀ a b) = (bool.«~»₀ b a)
	axiom «~»₁_comm {a b} : (bool.«~»₁ a b) = (bool.«~»₁ b a)
	axiom «~»₂_comm {a b} : (bool.«~»₂ a b) = (bool.«~»₂ b a)
	-- Equations
		-- eq c-enter(S, I) = rs ~ pc(S, I) and open ~ lock(S) .
	axiom eq_csubenter {s : kSys} {i : kPid} : (csubenter s i) = ((«~»₁ kLabel.rs (kLabel.pc s i)) && («~»₂ kStatus.sopen (kStatus.lock s)))
		-- eq c-leave(S, I) = cs ~ pc(S, I) .
	axiom eq_csubleave {s : kSys} {i : kPid} : (csubleave s i) = («~»₁ kLabel.cs (kLabel.pc s i))
		-- eq false xor A:Bool = A:Bool .
	axiom eq_xor₀ {a : bool} : (xor ff a) = a
		-- eq A:Bool xor A:Bool = false .
	axiom eq_xor₁ {a : bool} : (xor a a) = ff
		-- eq A:Bool implies B:Bool = not (A:Bool xor A:Bool and B:Bool) .
	axiom eq_implies {a b : bool} : (implies a b) = (¬ (xor a (a && b)))
		-- eq P:X$Pid ~ P:X$Pid = true .
	axiom eq_«~»₀ {p : kPid} : («~»₀ p p) = tt
		-- ceq R:X$Pid ~ P:X$Pid = true if Q:X$Pid ~ P:X$Pid = true /\ Q:X$Pid ~ R:X$Pid = true [nonexec label X$pid_trans] .
	axiom eq_X_pid_trans {r p q : kPid} : (bool.«~»₀ q p) = tt → (bool.«~»₀ q r) = tt → («~»₀ r p) = tt
		-- eq L:Label ~ L:Label = true .
	axiom eq_«~»₁₀ {l : kLabel} : («~»₁ l l) = tt
		-- eq rs ~ cs = false .
	axiom eq_«~»₁₁ : («~»₁ kLabel.rs kLabel.cs) = ff
		-- eq L:Status ~ L:Status = true .
	axiom eq_«~»₂₀ {l : kStatus} : («~»₂ l l) = tt
		-- eq open ~ close = false .
	axiom eq_«~»₂₁ : («~»₂ kStatus.sopen kStatus.close) = ff
		-- ceq S1:Status ~ S3:Status = true if S1:Status ~ S2:Status = true /\ S3:Status ~ S2:Status = true [nonexec label status_trans] .
	axiom eq_status_trans {s1 s3 s2 : kStatus} : (bool.«~»₂ s1 s2) = tt → (bool.«~»₂ s3 s2) = tt → («~»₂ s1 s3) = tt
end bool

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


namespace kPid
	-- Sort membership lemmas

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kPid) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kPid} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kPid} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kPid} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
end kPid

namespace kLabel
	-- Sort membership lemmas

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kLabel) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kLabel} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kLabel} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kLabel} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_pc eqe.eqe_pc eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.rs_decl has_sort.cs_decl has_sort.pc_decl eqe.eq_pc₀ eqe.eq_pc₁ eqe.eq_pc₂
end kLabel

namespace kStatus
	-- Sort membership lemmas

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kStatus) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kStatus} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kStatus} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kStatus} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_lock eqe.eqe_lock eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.sopen_decl has_sort.close_decl has_sort.lock_decl eqe.eq_lock₀ eqe.eq_lock₁ eqe.eq_lock₂
end kStatus

namespace kSys
	-- Sort membership lemmas

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kSys) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kSys} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kSys} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kSys} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_enter eqe.eqe_enter eqa.eqa_leave eqe.eqe_leave eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.init_decl has_sort.enter_decl has_sort.leave_decl eqe.eq_enter eqe.eq_leave
end kSys

namespace bool
	attribute [congr] eqe_xor eqe_implies eqe_«~»₀ eqe_«~»₁ eqe_«~»₂ eqe_csubenter eqe_csubleave
	attribute [simp] eq_csubenter eq_csubleave eq_xor₀ eq_xor₁ eq_implies eq_«~»₀ eq_X_pid_trans eq_«~»₁₀ eq_«~»₁₁ eq_«~»₂₀ eq_«~»₂₁ eq_status_trans
end bool

end Maude
