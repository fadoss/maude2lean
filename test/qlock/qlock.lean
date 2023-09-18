namespace Maude

-- Sorts
inductive MSort
	| Label
	| ErrPid
	| Pid
	| PidampErr
	| EQueue
	| NeQueue
	| Queue
	| Sys

-- Generator of the subsort relation
def subsort : MSort → MSort → Prop
	| MSort.ErrPid MSort.PidampErr := true
	| MSort.Pid MSort.PidampErr := true
	| MSort.EQueue MSort.Queue := true
	| MSort.NeQueue MSort.Queue := true
	| _ _ := false

-- Kinds and their operators

mutual inductive kPid, kQueue, kSys

with kPid : Type
	| none
	| top : kQueue → kPid

with kQueue : Type
	| empty
	| bar : kPid → kQueue → kQueue
	| enq : kQueue → kPid → kQueue
	| deq : kQueue → kQueue
	| queue : kSys → kQueue

with kSys : Type
	| init
	| want : kSys → kPid → kSys
	| try : kSys → kPid → kSys
	| exit : kSys → kPid → kSys

inductive kLabel
	| rs
	| ws
	| cs
	| pc : kSys → kPid → kLabel

-- Lean-native replacements of Maude types
-- (enabled by option with-native-bool)

namespace bool
	-- Non-native operators
	constant xor : bool → bool → bool
	constant implies : bool → bool → bool
	constant csubwant : kSys → kPid → bool
	constant csubtry : kSys → kPid → bool
	constant csubexit : kSys → kPid → bool
	constant inv1 : kSys → kPid → kPid → bool
	constant inv2 : kSys → kPid → bool
	constant eq₀ : kLabel → kLabel → bool
	constant eq₁ : kPid → kPid → bool
	constant eq₂ : bool → bool → bool
end bool

-- Kind assignment
def kind : MSort → Type
	| MSort.Label := kLabel
	| MSort.ErrPid := kPid
	| MSort.Pid := kPid
	| MSort.PidampErr := kPid
	| MSort.EQueue := kQueue
	| MSort.NeQueue := kQueue
	| MSort.Queue := kQueue
	| MSort.Sys := kSys

-- Predicates recognizing constructor terms
mutual def kLabel.ctor_only, kPid.ctor_only, kQueue.ctor_only, kSys.ctor_only

with kLabel.ctor_only : kLabel → Prop
	| kLabel.rs := true
	| kLabel.ws := true
	| kLabel.cs := true
	| _ := false

with kPid.ctor_only : kPid → Prop
	| kPid.none := true
	| _ := false

with kQueue.ctor_only : kQueue → Prop
	| kQueue.empty := true
	| (kQueue.bar a₀ a₁) := a₀.ctor_only ∧ a₁.ctor_only
	| _ := false

with kSys.ctor_only : kSys → Prop
	| kSys.init := true
	| (kSys.want a₀ a₁) := a₀.ctor_only ∧ a₁.ctor_only
	| (kSys.try a₀ a₁) := a₀.ctor_only ∧ a₁.ctor_only
	| (kSys.exit a₀ a₁) := a₀.ctor_only ∧ a₁.ctor_only

-- Equality modulo axioms
mutual inductive kLabel.eqa, kPid.eqa, kQueue.eqa, kSys.eqa

with kLabel.eqa : kLabel → kLabel → Prop
	| refl {a} : kLabel.eqa a a
	| symm {a b} : kLabel.eqa a b → kLabel.eqa b a
	| trans {a b c} : kLabel.eqa a b → kLabel.eqa b c → kLabel.eqa a c
	-- Congruence axioms for each operator
	| eqa_pc {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqa a₀ b₀ → kPid.eqa a₁ b₁ → kLabel.eqa (kLabel.pc a₀ a₁) (kLabel.pc b₀ b₁)

with kPid.eqa : kPid → kPid → Prop
	| refl {a} : kPid.eqa a a
	| symm {a b} : kPid.eqa a b → kPid.eqa b a
	| trans {a b c} : kPid.eqa a b → kPid.eqa b c → kPid.eqa a c
	-- Congruence axioms for each operator
	| eqa_top {a b : kQueue} : kQueue.eqa a b → kPid.eqa (kPid.top a) (kPid.top b)

with kQueue.eqa : kQueue → kQueue → Prop
	| refl {a} : kQueue.eqa a a
	| symm {a b} : kQueue.eqa a b → kQueue.eqa b a
	| trans {a b c} : kQueue.eqa a b → kQueue.eqa b c → kQueue.eqa a c
	-- Congruence axioms for each operator
	| eqa_bar {a₀ b₀ : kPid} {a₁ b₁ : kQueue} : kPid.eqa a₀ b₀ → kQueue.eqa a₁ b₁ → kQueue.eqa (kQueue.bar a₀ a₁) (kQueue.bar b₀ b₁)
	| eqa_enq {a₀ b₀ : kQueue} {a₁ b₁ : kPid} : kQueue.eqa a₀ b₀ → kPid.eqa a₁ b₁ → kQueue.eqa (kQueue.enq a₀ a₁) (kQueue.enq b₀ b₁)
	| eqa_deq {a b : kQueue} : kQueue.eqa a b → kQueue.eqa (kQueue.deq a) (kQueue.deq b)
	| eqa_queue {a b : kSys} : kSys.eqa a b → kQueue.eqa (kQueue.queue a) (kQueue.queue b)

with kSys.eqa : kSys → kSys → Prop
	| refl {a} : kSys.eqa a a
	| symm {a b} : kSys.eqa a b → kSys.eqa b a
	| trans {a b c} : kSys.eqa a b → kSys.eqa b c → kSys.eqa a c
	-- Congruence axioms for each operator
	| eqa_want {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqa a₀ b₀ → kPid.eqa a₁ b₁ → kSys.eqa (kSys.want a₀ a₁) (kSys.want b₀ b₁)
	| eqa_try {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqa a₀ b₀ → kPid.eqa a₁ b₁ → kSys.eqa (kSys.try a₀ a₁) (kSys.try b₀ b₁)
	| eqa_exit {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqa a₀ b₀ → kPid.eqa a₁ b₁ → kSys.eqa (kSys.exit a₀ a₁) (kSys.exit b₀ b₁)

-- Sort membership and equality modulo equations

mutual inductive kLabel.has_sort, kPid.has_sort, kQueue.has_sort, kSys.has_sort, kLabel.eqe, kPid.eqe, kQueue.eqe, kSys.eqe
with kLabel.has_sort : kLabel → MSort → Prop
	| subsort {t a b} : subsort a b → kLabel.has_sort t a → kLabel.has_sort t b
	-- Implicit membership axioms (operator declarations)
	-- op rs : -> Label .
	| rs_decl : kLabel.has_sort kLabel.rs MSort.Label
	-- op ws : -> Label .
	| ws_decl : kLabel.has_sort kLabel.ws MSort.Label
	-- op cs : -> Label .
	| cs_decl : kLabel.has_sort kLabel.cs MSort.Label
	-- op pc : Sys Pid -> Label .
	| pc_decl {a₀ : kSys} {a₁ : kPid} : kSys.has_sort a₀ MSort.Sys → kPid.has_sort a₁ MSort.Pid → kLabel.has_sort (kLabel.pc a₀ a₁) MSort.Label

with kPid.has_sort : kPid → MSort → Prop
	| subsort {t a b} : subsort a b → kPid.has_sort t a → kPid.has_sort t b
	-- Implicit membership axioms (operator declarations)
	-- op none : -> ErrPid .
	| none_decl : kPid.has_sort kPid.none MSort.ErrPid
	-- op top : EQueue -> ErrPid .
	| top_decl₀ {a : kQueue} : kQueue.has_sort a MSort.EQueue → kPid.has_sort (kPid.top a) MSort.ErrPid
	-- op top : NeQueue -> Pid .
	| top_decl₁ {a : kQueue} : kQueue.has_sort a MSort.NeQueue → kPid.has_sort (kPid.top a) MSort.Pid
	-- op top : Queue -> Pid&Err .
	| top_decl₂ {a : kQueue} : kQueue.has_sort a MSort.Queue → kPid.has_sort (kPid.top a) MSort.PidampErr

with kQueue.has_sort : kQueue → MSort → Prop
	| subsort {t a b} : subsort a b → kQueue.has_sort t a → kQueue.has_sort t b
	-- Implicit membership axioms (operator declarations)
	-- op empty : -> EQueue .
	| empty_decl : kQueue.has_sort kQueue.empty MSort.EQueue
	-- op _|_ : Pid Queue -> NeQueue .
	| bar_decl {a₀ : kPid} {a₁ : kQueue} : kPid.has_sort a₀ MSort.Pid → kQueue.has_sort a₁ MSort.Queue → kQueue.has_sort (kQueue.bar a₀ a₁) MSort.NeQueue
	-- op enq : Queue Pid -> NeQueue .
	| enq_decl {a₀ : kQueue} {a₁ : kPid} : kQueue.has_sort a₀ MSort.Queue → kPid.has_sort a₁ MSort.Pid → kQueue.has_sort (kQueue.enq a₀ a₁) MSort.NeQueue
	-- op deq : Queue -> Queue .
	| deq_decl {a : kQueue} : kQueue.has_sort a MSort.Queue → kQueue.has_sort (kQueue.deq a) MSort.Queue
	-- op queue : Sys -> Queue .
	| queue_decl {a : kSys} : kSys.has_sort a MSort.Sys → kQueue.has_sort (kQueue.queue a) MSort.Queue

with kSys.has_sort : kSys → MSort → Prop
	| subsort {t a b} : subsort a b → kSys.has_sort t a → kSys.has_sort t b
	-- Implicit membership axioms (operator declarations)
	-- op init : -> Sys .
	| init_decl : kSys.has_sort kSys.init MSort.Sys
	-- op want : Sys Pid -> Sys .
	| want_decl {a₀ : kSys} {a₁ : kPid} : kSys.has_sort a₀ MSort.Sys → kPid.has_sort a₁ MSort.Pid → kSys.has_sort (kSys.want a₀ a₁) MSort.Sys
	-- op try : Sys Pid -> Sys .
	| try_decl {a₀ : kSys} {a₁ : kPid} : kSys.has_sort a₀ MSort.Sys → kPid.has_sort a₁ MSort.Pid → kSys.has_sort (kSys.try a₀ a₁) MSort.Sys
	-- op exit : Sys Pid -> Sys .
	| exit_decl {a₀ : kSys} {a₁ : kPid} : kSys.has_sort a₀ MSort.Sys → kPid.has_sort a₁ MSort.Pid → kSys.has_sort (kSys.exit a₀ a₁) MSort.Sys

with kLabel.eqe : kLabel → kLabel → Prop
	| from_eqa {a b} : kLabel.eqa a b → kLabel.eqe a b
	| symm {a b} : kLabel.eqe a b → kLabel.eqe b a
	| trans {a b c} : kLabel.eqe a b → kLabel.eqe b c → kLabel.eqe a c
	-- Congruence axioms for each operator
	| eqe_pc {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqe a₀ b₀ → kPid.eqe a₁ b₁ → kLabel.eqe (kLabel.pc a₀ a₁) (kLabel.pc b₀ b₁)
	-- Equations
	-- eq pc(init, I) = rs .
	| eq_pc₀ {i} : kPid.has_sort i MSort.Pid → kLabel.eqe (kLabel.pc kSys.init i) kLabel.rs
	-- ceq pc(want(S, I), J) = if I = J then ws else pc(S, J) fi if c-want(S, I) = true .
	| eq_pc₁ {s i j} : kSys.has_sort s MSort.Sys → kPid.has_sort i MSort.Pid → kPid.has_sort j MSort.Pid → (bool.csubwant s i) = tt → kLabel.eqe (kLabel.pc (kSys.want s i) j) (cond (bool.eq₁ i j) kLabel.ws (kLabel.pc s j))
	-- ceq pc(try(S, I), J) = if I = J then cs else pc(S, J) fi if c-try(S, I) = true .
	| eq_pc₂ {s i j} : kSys.has_sort s MSort.Sys → kPid.has_sort i MSort.Pid → kPid.has_sort j MSort.Pid → (bool.csubtry s i) = tt → kLabel.eqe (kLabel.pc (kSys.try s i) j) (cond (bool.eq₁ i j) kLabel.cs (kLabel.pc s j))
	-- ceq pc(exit(S, I), J) = if I = J then rs else pc(S, J) fi if c-exit(S, I) = true .
	| eq_pc₃ {s i j} : kSys.has_sort s MSort.Sys → kPid.has_sort i MSort.Pid → kPid.has_sort j MSort.Pid → (bool.csubexit s i) = tt → kLabel.eqe (kLabel.pc (kSys.exit s i) j) (cond (bool.eq₁ i j) kLabel.rs (kLabel.pc s j))

with kPid.eqe : kPid → kPid → Prop
	| from_eqa {a b} : kPid.eqa a b → kPid.eqe a b
	| symm {a b} : kPid.eqe a b → kPid.eqe b a
	| trans {a b c} : kPid.eqe a b → kPid.eqe b c → kPid.eqe a c
	-- Congruence axioms for each operator
	| eqe_top {a b : kQueue} : kQueue.eqe a b → kPid.eqe (kPid.top a) (kPid.top b)
	-- Equations
	-- eq top(empty) = none .
	| eq_top₀ : kPid.eqe (kPid.top kQueue.empty) kPid.none
	-- eq top(X:Pid | Q:Queue) = X:Pid .
	| eq_top₁ {x q} : kPid.has_sort x MSort.Pid → kQueue.has_sort q MSort.Queue → kPid.eqe (kPid.top (kQueue.bar x q)) x

with kQueue.eqe : kQueue → kQueue → Prop
	| from_eqa {a b} : kQueue.eqa a b → kQueue.eqe a b
	| symm {a b} : kQueue.eqe a b → kQueue.eqe b a
	| trans {a b c} : kQueue.eqe a b → kQueue.eqe b c → kQueue.eqe a c
	-- Congruence axioms for each operator
	| eqe_bar {a₀ b₀ : kPid} {a₁ b₁ : kQueue} : kPid.eqe a₀ b₀ → kQueue.eqe a₁ b₁ → kQueue.eqe (kQueue.bar a₀ a₁) (kQueue.bar b₀ b₁)
	| eqe_enq {a₀ b₀ : kQueue} {a₁ b₁ : kPid} : kQueue.eqe a₀ b₀ → kPid.eqe a₁ b₁ → kQueue.eqe (kQueue.enq a₀ a₁) (kQueue.enq b₀ b₁)
	| eqe_deq {a b : kQueue} : kQueue.eqe a b → kQueue.eqe (kQueue.deq a) (kQueue.deq b)
	| eqe_queue {a b : kSys} : kSys.eqe a b → kQueue.eqe (kQueue.queue a) (kQueue.queue b)
	-- Equations
	-- eq queue(init) = empty .
	| eq_queue₀ : kQueue.eqe (kQueue.queue kSys.init) kQueue.empty
	-- ceq queue(want(S, I)) = enq(queue(S), I) if c-want(S, I) = true .
	| eq_queue₁ {s i} : kSys.has_sort s MSort.Sys → kPid.has_sort i MSort.Pid → (bool.csubwant s i) = tt → kQueue.eqe (kQueue.queue (kSys.want s i)) (kQueue.enq (kQueue.queue s) i)
	-- eq queue(try(S, I)) = queue(S) .
	| eq_queue₂ {s i} : kSys.has_sort s MSort.Sys → kPid.has_sort i MSort.Pid → kQueue.eqe (kQueue.queue (kSys.try s i)) (kQueue.queue s)
	-- ceq queue(exit(S, I)) = deq(queue(S)) if c-exit(S, I) = true .
	| eq_queue₃ {s i} : kSys.has_sort s MSort.Sys → kPid.has_sort i MSort.Pid → (bool.csubexit s i) = tt → kQueue.eqe (kQueue.queue (kSys.exit s i)) (kQueue.deq (kQueue.queue s))
	-- eq enq(empty, X:Pid) = X:Pid | empty .
	| eq_enq₀ {x} : kPid.has_sort x MSort.Pid → kQueue.eqe (kQueue.enq kQueue.empty x) (kQueue.bar x kQueue.empty)
	-- eq enq(Y:Pid | Q:Queue, X:Pid) = Y:Pid | enq(Q:Queue, X:Pid) .
	| eq_enq₁ {y q x} : kPid.has_sort y MSort.Pid → kQueue.has_sort q MSort.Queue → kPid.has_sort x MSort.Pid → kQueue.eqe (kQueue.enq (kQueue.bar y q) x) (kQueue.bar y (kQueue.enq q x))
	-- eq deq(empty) = empty .
	| eq_deq₀ : kQueue.eqe (kQueue.deq kQueue.empty) kQueue.empty
	-- eq deq(X:Pid | Q:Queue) = Q:Queue .
	| eq_deq₁ {x q} : kPid.has_sort x MSort.Pid → kQueue.has_sort q MSort.Queue → kQueue.eqe (kQueue.deq (kQueue.bar x q)) q

with kSys.eqe : kSys → kSys → Prop
	| from_eqa {a b} : kSys.eqa a b → kSys.eqe a b
	| symm {a b} : kSys.eqe a b → kSys.eqe b a
	| trans {a b c} : kSys.eqe a b → kSys.eqe b c → kSys.eqe a c
	-- Congruence axioms for each operator
	| eqe_want {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqe a₀ b₀ → kPid.eqe a₁ b₁ → kSys.eqe (kSys.want a₀ a₁) (kSys.want b₀ b₁)
	| eqe_try {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqe a₀ b₀ → kPid.eqe a₁ b₁ → kSys.eqe (kSys.try a₀ a₁) (kSys.try b₀ b₁)
	| eqe_exit {a₀ b₀ : kSys} {a₁ b₁ : kPid} : kSys.eqe a₀ b₀ → kPid.eqe a₁ b₁ → kSys.eqe (kSys.exit a₀ a₁) (kSys.exit b₀ b₁)
	-- Equations
	-- ceq want(S, I) = S if not c-want(S, I) = true .
	| eq_want {s i} : kSys.has_sort s MSort.Sys → kPid.has_sort i MSort.Pid → (¬ (bool.csubwant s i)) = tt → kSys.eqe (kSys.want s i) s
	-- ceq try(S, I) = S if not c-try(S, I) = true .
	| eq_try {s i} : kSys.has_sort s MSort.Sys → kPid.has_sort i MSort.Pid → (¬ (bool.csubtry s i)) = tt → kSys.eqe (kSys.try s i) s
	-- ceq exit(S, I) = S if not c-exit(S, I) = true .
	| eq_exit {s i} : kSys.has_sort s MSort.Sys → kPid.has_sort i MSort.Pid → (¬ (bool.csubexit s i)) = tt → kSys.eqe (kSys.exit s i) s

infix (name := kLabel_has_sort) ` ⊳ `:40 := kLabel.has_sort
infix (name := kPid_has_sort) ` ⊳ `:40 := kPid.has_sort
infix (name := kQueue_has_sort) ` ⊳ `:40 := kQueue.has_sort
infix (name := kSys_has_sort) ` ⊳ `:40 := kSys.has_sort

infix (name := kLabel_eqa) ` =A `:40 := kLabel.eqa
infix (name := kPid_eqa) ` =A `:40 := kPid.eqa
infix (name := kQueue_eqa) ` =A `:40 := kQueue.eqa
infix (name := kSys_eqa) ` =A `:40 := kSys.eqa

infix (name := kLabel_eqe) ` =E `:40 := kLabel.eqe
infix (name := kPid_eqe) ` =E `:40 := kPid.eqe
infix (name := kQueue_eqe) ` =E `:40 := kQueue.eqe
infix (name := kSys_eqe) ` =E `:40 := kSys.eqe

-- Axioms for the native replacements of Maude types
-- (enabled by option with-native-bool)

namespace bool
	-- Congruence axioms
	axiom eqe_xor {a₀ b₀ a₁ b₁ : bool} : a₀ = b₀ → a₁ = b₁ → (bool.xor a₀ a₁) = (bool.xor b₀ b₁)
	axiom eqe_implies {a₀ b₀ a₁ b₁ : bool} : a₀ = b₀ → a₁ = b₁ → (bool.implies a₀ a₁) = (bool.implies b₀ b₁)
	axiom eqe_csubwant {a₀ b₀ : kSys} {a₁ b₁ : kPid} : a₀ =E b₀ → a₁ =E b₁ → (bool.csubwant a₀ a₁) = (bool.csubwant b₀ b₁)
	axiom eqe_csubtry {a₀ b₀ : kSys} {a₁ b₁ : kPid} : a₀ =E b₀ → a₁ =E b₁ → (bool.csubtry a₀ a₁) = (bool.csubtry b₀ b₁)
	axiom eqe_csubexit {a₀ b₀ : kSys} {a₁ b₁ : kPid} : a₀ =E b₀ → a₁ =E b₁ → (bool.csubexit a₀ a₁) = (bool.csubexit b₀ b₁)
	axiom eqe_inv1 {a₀ b₀ : kSys} {a₁ b₁ a₂ b₂ : kPid} : a₀ =E b₀ → a₁ =E b₁ → a₂ =E b₂ → (bool.inv1 a₀ a₁ a₂) = (bool.inv1 b₀ b₁ b₂)
	axiom eqe_inv2 {a₀ b₀ : kSys} {a₁ b₁ : kPid} : a₀ =E b₀ → a₁ =E b₁ → (bool.inv2 a₀ a₁) = (bool.inv2 b₀ b₁)
	axiom eqe_eq₀ {a₀ b₀ a₁ b₁ : kLabel} : a₀ =E b₀ → a₁ =E b₁ → (bool.eq₀ a₀ a₁) = (bool.eq₀ b₀ b₁)
	axiom eqe_eq₁ {a₀ b₀ a₁ b₁ : kPid} : a₀ =E b₀ → a₁ =E b₁ → (bool.eq₁ a₀ a₁) = (bool.eq₁ b₀ b₁)
	axiom eqe_eq₂ {a₀ b₀ a₁ b₁ : bool} : a₀ = b₀ → a₁ = b₁ → (bool.eq₂ a₀ a₁) = (bool.eq₂ b₀ b₁)
	-- Structural axioms
	axiom xor_comm {a b} : (bool.xor a b) = (bool.xor b a)
	axiom xor_assoc {a b c} : (bool.xor a (bool.xor b c)) = (bool.xor (bool.xor a b) c)
	axiom eq₀_comm {a b} : (bool.eq₀ a b) = (bool.eq₀ b a)
	axiom eq₁_comm {a b} : (bool.eq₁ a b) = (bool.eq₁ b a)
	axiom eq₂_comm {a b} : (bool.eq₂ a b) = (bool.eq₂ b a)
	-- Equations
		-- eq c-want(S, I) = rs = pc(S, I) .
	axiom eq_csubwant {s : kSys} {i : kPid} : s ⊳ MSort.Sys → i ⊳ MSort.Pid → (csubwant s i) = (eq₀ kLabel.rs (kLabel.pc s i))
		-- eq c-try(S, I) = ws = pc(S, I) and I = top(queue(S)) .
	axiom eq_csubtry {s : kSys} {i : kPid} : s ⊳ MSort.Sys → i ⊳ MSort.Pid → (csubtry s i) = ((eq₀ kLabel.ws (kLabel.pc s i)) && (eq₁ i (kPid.top (kQueue.queue s))))
		-- eq c-exit(S, I) = cs = pc(S, I) .
	axiom eq_csubexit {s : kSys} {i : kPid} : s ⊳ MSort.Sys → i ⊳ MSort.Pid → (csubexit s i) = (eq₀ kLabel.cs (kLabel.pc s i))
		-- eq inv1(S, I, J) = cs = pc(S, I) and cs = pc(S, J) implies I = J .
	axiom eq_inv1 {s : kSys} {i j : kPid} : s ⊳ MSort.Sys → i ⊳ MSort.Pid → j ⊳ MSort.Pid → (inv1 s i j) = (implies ((eq₀ kLabel.cs (kLabel.pc s i)) && (eq₀ kLabel.cs (kLabel.pc s j))) (eq₁ i j))
		-- eq inv2(S, I) = cs = pc(S, I) implies I = top(queue(S)) .
	axiom eq_inv2 {s : kSys} {i : kPid} : s ⊳ MSort.Sys → i ⊳ MSort.Pid → (inv2 s i) = (implies (eq₀ kLabel.cs (kLabel.pc s i)) (eq₁ i (kPid.top (kQueue.queue s))))
		-- eq false xor A:Bool = A:Bool .
	axiom eq_xor₀ {a : bool} : (xor ff a) = a
		-- eq A:Bool xor A:Bool = false .
	axiom eq_xor₁ {a : bool} : (xor a a) = ff
		-- eq A:Bool implies B:Bool = not (A:Bool xor A:Bool and B:Bool) .
	axiom eq_implies {a b : bool} : (implies a b) = (¬ (xor a (a && b)))
		-- eq B:Bool = B:Bool = true .
	axiom eq_eq₂₀ {b : bool} : (eq₂ b b) = tt
		-- eq true = false = false .
	axiom eq_eq₂₁ : (eq₂ tt ff) = ff
		-- eq L:Label = L:Label = true .
	axiom eq_eq₀₀ {l : kLabel} : l ⊳ MSort.Label → (eq₀ l l) = tt
		-- eq rs = ws = false .
	axiom eq_eq₀₁ : (eq₀ kLabel.rs kLabel.ws) = ff
		-- eq rs = cs = false .
	axiom eq_eq₀₂ : (eq₀ kLabel.rs kLabel.cs) = ff
		-- eq ws = cs = false .
	axiom eq_eq₀₃ : (eq₀ kLabel.ws kLabel.cs) = ff
		-- eq PE:Pid&Err = PE:Pid&Err = true .
	axiom eq_eq₁₀ {pe : kPid} : pe ⊳ MSort.PidampErr → (eq₁ pe pe) = tt
		-- eq I = EI:ErrPid = false .
	axiom eq_eq₁₁ {i ei : kPid} : i ⊳ MSort.Pid → ei ⊳ MSort.ErrPid → (eq₁ i ei) = ff
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
	attribute [simp] has_sort.rs_decl has_sort.ws_decl has_sort.cs_decl has_sort.pc_decl eqe.eq_pc₀ eqe.eq_pc₁ eqe.eq_pc₂ eqe.eq_pc₃
end kLabel

namespace kPid
	-- Sort membership lemmas
	lemma subsort_errpid_pidamperr {t : kPid} : t ⊳ MSort.ErrPid →
		t ⊳ MSort.PidampErr := by apply has_sort.subsort; simp [subsort]
	lemma subsort_pid_pidamperr {t : kPid} : t ⊳ MSort.Pid →
		t ⊳ MSort.PidampErr := by apply has_sort.subsort; simp [subsort]

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
	attribute [congr] eqa.eqa_top eqe.eqe_top eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.none_decl has_sort.top_decl₀ has_sort.top_decl₁ has_sort.top_decl₂ eqe.eq_top₀ eqe.eq_top₁ subsort_errpid_pidamperr subsort_pid_pidamperr
end kPid

namespace kQueue
	-- Sort membership lemmas
	lemma subsort_equeue_queue {t : kQueue} : t ⊳ MSort.EQueue →
		t ⊳ MSort.Queue := by apply has_sort.subsort; simp [subsort]
	lemma subsort_nequeue_queue {t : kQueue} : t ⊳ MSort.NeQueue →
		t ⊳ MSort.Queue := by apply has_sort.subsort; simp [subsort]

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kQueue) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kQueue} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kQueue} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kQueue} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_bar eqe.eqe_bar eqa.eqa_enq eqe.eqe_enq eqa.eqa_deq eqe.eqe_deq eqa.eqa_queue eqe.eqe_queue eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.empty_decl has_sort.bar_decl has_sort.enq_decl has_sort.deq_decl has_sort.queue_decl eqe.eq_queue₀ eqe.eq_queue₁ eqe.eq_queue₂ eqe.eq_queue₃ eqe.eq_enq₀ eqe.eq_enq₁ eqe.eq_deq₀ eqe.eq_deq₁ subsort_equeue_queue subsort_nequeue_queue
end kQueue

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
	attribute [congr] eqa.eqa_want eqe.eqe_want eqa.eqa_try eqe.eqe_try eqa.eqa_exit eqe.eqe_exit eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.init_decl has_sort.want_decl has_sort.try_decl has_sort.exit_decl eqe.eq_want eqe.eq_try eqe.eq_exit
end kSys

namespace bool
	attribute [congr] eqe_xor eqe_implies eqe_csubwant eqe_csubtry eqe_csubexit eqe_inv1 eqe_inv2 eqe_eq₀ eqe_eq₁ eqe_eq₂
	attribute [simp] eq_csubwant eq_csubtry eq_csubexit eq_inv1 eq_inv2 eq_xor₀ eq_xor₁ eq_implies eq_eq₂₀ eq_eq₂₁ eq_eq₀₀ eq_eq₀₁ eq_eq₀₂ eq_eq₀₃ eq_eq₁₀ eq_eq₁₁
end bool

end Maude
