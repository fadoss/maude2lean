namespace Maude

-- Sorts
inductive MSort
	| Bool
	| Zero
	| NzNat
	| Nat
	| Obj
	| Phil
	| Being
	| List
	| Table

-- Generator of the subsort relation
def subsort : MSort → MSort → Prop
	| MSort.Zero MSort.Nat := true
	| MSort.NzNat MSort.Nat := true
	| MSort.Obj MSort.Being := true
	| MSort.Phil MSort.Being := true
	| MSort.Being MSort.List := true
	| _ _ := false

-- Kinds and their operators

inductive kNat
	| zero
	| s : kNat → kNat
	| sum : kNat → kNat → kNat
	| sd : kNat → kNat → kNat
	| mul : kNat → kNat → kNat
	| quo : kNat → kNat → kNat
	| rem : kNat → kNat → kNat
	| pow : kNat → kNat → kNat
	| modExp : kNat → kNat → kNat → kNat
	| gcd : kNat → kNat → kNat
	| lcm : kNat → kNat → kNat
	| min : kNat → kNat → kNat
	| max : kNat → kNat → kNat
	| xor : kNat → kNat → kNat
	| bw_and : kNat → kNat → kNat
	| bw_or : kNat → kNat → kNat
	| rshift : kNat → kNat → kNat
	| lshift : kNat → kNat → kNat

inductive kBool
	| true
	| false
	| and : kBool → kBool → kBool
	| or : kBool → kBool → kBool
	| xor : kBool → kBool → kBool
	| not : kBool → kBool
	| implies : kBool → kBool → kBool
	| lt : kNat → kNat → kBool
	| lteq : kNat → kNat → kBool
	| gt : kNat → kNat → kBool
	| gteq : kNat → kNat → kBool
	| divides : kNat → kNat → kBool

inductive kList
	| phil : kList → kNat → kList → kList
	| o
	| fork
	| empty
	| join : kList → kList → kList
	| initialList : kNat → kList

inductive kTable
	| table : kList → kTable
	| initial : kNat → kTable

-- Kind assignment
def kind : MSort → Type
	| MSort.Bool := kBool
	| MSort.Zero := kNat
	| MSort.NzNat := kNat
	| MSort.Nat := kNat
	| MSort.Obj := kList
	| MSort.Phil := kList
	| MSort.Being := kList
	| MSort.List := kList
	| MSort.Table := kTable

-- Predicates recognizing constructor terms
mutual def kBool.ctor_only, kNat.ctor_only, kList.ctor_only, kTable.ctor_only

with kBool.ctor_only : kBool → Prop
	| kBool.true := true
	| kBool.false := true
	| _ := false

with kNat.ctor_only : kNat → Prop
	| kNat.zero := true
	| (kNat.s a) := a.ctor_only
	| _ := false

with kList.ctor_only : kList → Prop
	| (kList.phil a₀ a₁ a₂) := a₀.ctor_only ∧ a₁.ctor_only ∧ a₂.ctor_only
	| kList.o := true
	| kList.fork := true
	| kList.empty := true
	| (kList.join a₀ a₁) := a₀.ctor_only ∧ a₁.ctor_only
	| _ := false

with kTable.ctor_only : kTable → Prop
	| (kTable.table a) := a.ctor_only
	| _ := false

-- Equality modulo axioms
mutual inductive kBool.eqa, kNat.eqa, kList.eqa, kTable.eqa

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
	| eqa_lt {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kBool.eqa (kBool.lt a₀ a₁) (kBool.lt b₀ b₁)
	| eqa_lteq {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kBool.eqa (kBool.lteq a₀ a₁) (kBool.lteq b₀ b₁)
	| eqa_gt {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kBool.eqa (kBool.gt a₀ a₁) (kBool.gt b₀ b₁)
	| eqa_gteq {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kBool.eqa (kBool.gteq a₀ a₁) (kBool.gteq b₀ b₁)
	| eqa_divides {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kBool.eqa (kBool.divides a₀ a₁) (kBool.divides b₀ b₁)
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
	| eqa_sd {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.sd a₀ a₁) (kNat.sd b₀ b₁)
	| eqa_mul {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.mul a₀ a₁) (kNat.mul b₀ b₁)
	| eqa_quo {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.quo a₀ a₁) (kNat.quo b₀ b₁)
	| eqa_rem {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.rem a₀ a₁) (kNat.rem b₀ b₁)
	| eqa_pow {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.pow a₀ a₁) (kNat.pow b₀ b₁)
	| eqa_modExp {a₀ b₀ a₁ b₁ a₂ b₂ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa a₂ b₂ → kNat.eqa (kNat.modExp a₀ a₁ a₂) (kNat.modExp b₀ b₁ b₂)
	| eqa_gcd {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.gcd a₀ a₁) (kNat.gcd b₀ b₁)
	| eqa_lcm {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.lcm a₀ a₁) (kNat.lcm b₀ b₁)
	| eqa_min {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.min a₀ a₁) (kNat.min b₀ b₁)
	| eqa_max {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.max a₀ a₁) (kNat.max b₀ b₁)
	| eqa_xor {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.xor a₀ a₁) (kNat.xor b₀ b₁)
	| eqa_bw_and {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.bw_and a₀ a₁) (kNat.bw_and b₀ b₁)
	| eqa_bw_or {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.bw_or a₀ a₁) (kNat.bw_or b₀ b₁)
	| eqa_rshift {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.rshift a₀ a₁) (kNat.rshift b₀ b₁)
	| eqa_lshift {a₀ b₀ a₁ b₁ : kNat} : kNat.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kNat.eqa (kNat.lshift a₀ a₁) (kNat.lshift b₀ b₁)
	-- Structural axioms
	| sum_comm {a b} : kNat.eqa (kNat.sum a b) (kNat.sum b a)
	| sum_assoc {a b c} : kNat.eqa (kNat.sum a (kNat.sum b c)) (kNat.sum (kNat.sum a b) c)
	| sd_comm {a b} : kNat.eqa (kNat.sd a b) (kNat.sd b a)
	| mul_comm {a b} : kNat.eqa (kNat.mul a b) (kNat.mul b a)
	| mul_assoc {a b c} : kNat.eqa (kNat.mul a (kNat.mul b c)) (kNat.mul (kNat.mul a b) c)
	| gcd_comm {a b} : kNat.eqa (kNat.gcd a b) (kNat.gcd b a)
	| gcd_assoc {a b c} : kNat.eqa (kNat.gcd a (kNat.gcd b c)) (kNat.gcd (kNat.gcd a b) c)
	| lcm_comm {a b} : kNat.eqa (kNat.lcm a b) (kNat.lcm b a)
	| lcm_assoc {a b c} : kNat.eqa (kNat.lcm a (kNat.lcm b c)) (kNat.lcm (kNat.lcm a b) c)
	| min_comm {a b} : kNat.eqa (kNat.min a b) (kNat.min b a)
	| min_assoc {a b c} : kNat.eqa (kNat.min a (kNat.min b c)) (kNat.min (kNat.min a b) c)
	| max_comm {a b} : kNat.eqa (kNat.max a b) (kNat.max b a)
	| max_assoc {a b c} : kNat.eqa (kNat.max a (kNat.max b c)) (kNat.max (kNat.max a b) c)
	| xor_comm {a b} : kNat.eqa (kNat.xor a b) (kNat.xor b a)
	| xor_assoc {a b c} : kNat.eqa (kNat.xor a (kNat.xor b c)) (kNat.xor (kNat.xor a b) c)
	| bw_and_comm {a b} : kNat.eqa (kNat.bw_and a b) (kNat.bw_and b a)
	| bw_and_assoc {a b c} : kNat.eqa (kNat.bw_and a (kNat.bw_and b c)) (kNat.bw_and (kNat.bw_and a b) c)
	| bw_or_comm {a b} : kNat.eqa (kNat.bw_or a b) (kNat.bw_or b a)
	| bw_or_assoc {a b c} : kNat.eqa (kNat.bw_or a (kNat.bw_or b c)) (kNat.bw_or (kNat.bw_or a b) c)

with kList.eqa : kList → kList → Prop
	| refl {a} : kList.eqa a a
	| symm {a b} : kList.eqa a b → kList.eqa b a
	| trans {a b c} : kList.eqa a b → kList.eqa b c → kList.eqa a c
	-- Congruence axioms for each operator
	| eqa_phil {a₀ b₀ : kList} {a₁ b₁ : kNat} {a₂ b₂ : kList} : kList.eqa a₀ b₀ → kNat.eqa a₁ b₁ → kList.eqa a₂ b₂ → kList.eqa (kList.phil a₀ a₁ a₂) (kList.phil b₀ b₁ b₂)
	| eqa_join {a₀ b₀ a₁ b₁ : kList} : kList.eqa a₀ b₀ → kList.eqa a₁ b₁ → kList.eqa (kList.join a₀ a₁) (kList.join b₀ b₁)
	| eqa_initialList {a b : kNat} : kNat.eqa a b → kList.eqa (kList.initialList a) (kList.initialList b)
	-- Structural axioms
	| join_assoc {a b c} : kList.eqa (kList.join a (kList.join b c)) (kList.join (kList.join a b) c)
	| join_left_id {a} : kList.eqa (kList.join kList.empty a) a
	| join_right_id {a} : kList.eqa (kList.join a kList.empty) a

with kTable.eqa : kTable → kTable → Prop
	| refl {a} : kTable.eqa a a
	| symm {a b} : kTable.eqa a b → kTable.eqa b a
	| trans {a b c} : kTable.eqa a b → kTable.eqa b c → kTable.eqa a c
	-- Congruence axioms for each operator
	| eqa_table {a b : kList} : kList.eqa a b → kTable.eqa (kTable.table a) (kTable.table b)
	| eqa_initial {a b : kNat} : kNat.eqa a b → kTable.eqa (kTable.initial a) (kTable.initial b)

-- Sort membership and equality modulo equations

mutual inductive kBool.has_sort, kNat.has_sort, kList.has_sort, kTable.has_sort, kBool.eqe, kNat.eqe, kList.eqe, kTable.eqe
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
	| lt_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kBool.has_sort (kBool.lt a₀ a₁) MSort.Bool
	| lteq_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kBool.has_sort (kBool.lteq a₀ a₁) MSort.Bool
	| gt_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kBool.has_sort (kBool.gt a₀ a₁) MSort.Bool
	| gteq_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kBool.has_sort (kBool.gteq a₀ a₁) MSort.Bool
	| divides_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.NzNat → kNat.has_sort a₁ MSort.Nat → kBool.has_sort (kBool.divides a₀ a₁) MSort.Bool

with kNat.has_sort : kNat → MSort → Prop
	| subsort {t a b} : subsort a b → kNat.has_sort t a → kNat.has_sort t b
	-- Implicit membership axioms (operator declarations)
	| zero_decl : kNat.has_sort kNat.zero MSort.Zero
	| s_decl {a : kNat} : kNat.has_sort a MSort.Nat → kNat.has_sort (kNat.s a) MSort.NzNat
	| sum_decl₀ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.NzNat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.sum a₀ a₁) MSort.NzNat
	| sum_decl₁ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.sum a₀ a₁) MSort.Nat
	| sum_decl₂ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.NzNat → kNat.has_sort (kNat.sum a₀ a₁) MSort.NzNat
	| sd_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.sd a₀ a₁) MSort.Nat
	| mul_decl₀ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.NzNat → kNat.has_sort a₁ MSort.NzNat → kNat.has_sort (kNat.mul a₀ a₁) MSort.NzNat
	| mul_decl₁ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.mul a₀ a₁) MSort.Nat
	| quo_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.NzNat → kNat.has_sort (kNat.quo a₀ a₁) MSort.Nat
	| rem_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.NzNat → kNat.has_sort (kNat.rem a₀ a₁) MSort.Nat
	| pow_decl₀ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.pow a₀ a₁) MSort.Nat
	| pow_decl₁ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.NzNat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.pow a₀ a₁) MSort.NzNat
	| gcd_decl₀ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.NzNat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.gcd a₀ a₁) MSort.NzNat
	| gcd_decl₁ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.gcd a₀ a₁) MSort.Nat
	| gcd_decl₂ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.NzNat → kNat.has_sort (kNat.gcd a₀ a₁) MSort.NzNat
	| lcm_decl₀ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.NzNat → kNat.has_sort a₁ MSort.NzNat → kNat.has_sort (kNat.lcm a₀ a₁) MSort.NzNat
	| lcm_decl₁ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.lcm a₀ a₁) MSort.Nat
	| min_decl₀ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.NzNat → kNat.has_sort a₁ MSort.NzNat → kNat.has_sort (kNat.min a₀ a₁) MSort.NzNat
	| min_decl₁ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.min a₀ a₁) MSort.Nat
	| max_decl₀ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.NzNat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.max a₀ a₁) MSort.NzNat
	| max_decl₁ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.max a₀ a₁) MSort.Nat
	| max_decl₂ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.NzNat → kNat.has_sort (kNat.max a₀ a₁) MSort.NzNat
	| xor_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.xor a₀ a₁) MSort.Nat
	| bw_and_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.bw_and a₀ a₁) MSort.Nat
	| bw_or_decl₀ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.NzNat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.bw_or a₀ a₁) MSort.NzNat
	| bw_or_decl₁ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.bw_or a₀ a₁) MSort.Nat
	| bw_or_decl₂ {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.NzNat → kNat.has_sort (kNat.bw_or a₀ a₁) MSort.NzNat
	| rshift_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.rshift a₀ a₁) MSort.Nat
	| lshift_decl {a₀ a₁ : kNat} : kNat.has_sort a₀ MSort.Nat → kNat.has_sort a₁ MSort.Nat → kNat.has_sort (kNat.lshift a₀ a₁) MSort.Nat

with kList.has_sort : kList → MSort → Prop
	| subsort {t a b} : subsort a b → kList.has_sort t a → kList.has_sort t b
	-- Implicit membership axioms (operator declarations)
	| phil_decl {a₀ : kList} {a₁ : kNat} {a₂ : kList} : kList.has_sort a₀ MSort.Obj → kNat.has_sort a₁ MSort.Nat → kList.has_sort a₂ MSort.Obj → kList.has_sort (kList.phil a₀ a₁ a₂) MSort.Phil
	| o_decl : kList.has_sort kList.o MSort.Obj
	| fork_decl : kList.has_sort kList.fork MSort.Obj
	| empty_decl : kList.has_sort kList.empty MSort.List
	| join_decl {a₀ a₁ : kList} : kList.has_sort a₀ MSort.List → kList.has_sort a₁ MSort.List → kList.has_sort (kList.join a₀ a₁) MSort.List
	| initialList_decl {a : kNat} : kNat.has_sort a MSort.Nat → kList.has_sort (kList.initialList a) MSort.List

with kTable.has_sort : kTable → MSort → Prop
	| subsort {t a b} : subsort a b → kTable.has_sort t a → kTable.has_sort t b
	-- Implicit membership axioms (operator declarations)
	| table_decl {a : kList} : kList.has_sort a MSort.List → kTable.has_sort (kTable.table a) MSort.Table
	| initial_decl {a : kNat} : kNat.has_sort a MSort.Nat → kTable.has_sort (kTable.initial a) MSort.Table

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
	| eqe_lt {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kBool.eqe (kBool.lt a₀ a₁) (kBool.lt b₀ b₁)
	| eqe_lteq {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kBool.eqe (kBool.lteq a₀ a₁) (kBool.lteq b₀ b₁)
	| eqe_gt {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kBool.eqe (kBool.gt a₀ a₁) (kBool.gt b₀ b₁)
	| eqe_gteq {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kBool.eqe (kBool.gteq a₀ a₁) (kBool.gteq b₀ b₁)
	| eqe_divides {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kBool.eqe (kBool.divides a₀ a₁) (kBool.divides b₀ b₁)
	-- Equations
	| eq_and₀ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.and kBool.true a) a
	| eq_and₁ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.and kBool.false a) kBool.false
	| eq_and₂ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.and a a) a
	| eq_xor₀ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.xor kBool.false a) a
	| eq_xor₁ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.xor a a) kBool.false
	| eq_and₃ {a b c} : kBool.has_sort a MSort.Bool → kBool.has_sort b MSort.Bool → kBool.has_sort c MSort.Bool → kBool.eqe (kBool.and a (kBool.xor b c)) (kBool.xor (kBool.and a b) (kBool.and a c))
	| eq_not {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.not a) (kBool.xor kBool.true a)
	| eq_or {a b} : kBool.has_sort a MSort.Bool → kBool.has_sort b MSort.Bool → kBool.eqe (kBool.or a b) (kBool.xor (kBool.and a b) (kBool.xor a b))
	| eq_implies {a b} : kBool.has_sort a MSort.Bool → kBool.has_sort b MSort.Bool → kBool.eqe (kBool.implies a b) (kBool.not (kBool.xor a (kBool.and a b)))

with kNat.eqe : kNat → kNat → Prop
	| from_eqa {a b} : kNat.eqa a b → kNat.eqe a b
	| symm {a b} : kNat.eqe a b → kNat.eqe b a
	| trans {a b c} : kNat.eqe a b → kNat.eqe b c → kNat.eqe a c
	-- Congruence axioms for each operator
	| eqe_s {a b : kNat} : kNat.eqe a b → kNat.eqe (kNat.s a) (kNat.s b)
	| eqe_sum {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.sum a₀ a₁) (kNat.sum b₀ b₁)
	| eqe_sd {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.sd a₀ a₁) (kNat.sd b₀ b₁)
	| eqe_mul {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.mul a₀ a₁) (kNat.mul b₀ b₁)
	| eqe_quo {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.quo a₀ a₁) (kNat.quo b₀ b₁)
	| eqe_rem {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.rem a₀ a₁) (kNat.rem b₀ b₁)
	| eqe_pow {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.pow a₀ a₁) (kNat.pow b₀ b₁)
	| eqe_modExp {a₀ b₀ a₁ b₁ a₂ b₂ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe a₂ b₂ → kNat.eqe (kNat.modExp a₀ a₁ a₂) (kNat.modExp b₀ b₁ b₂)
	| eqe_gcd {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.gcd a₀ a₁) (kNat.gcd b₀ b₁)
	| eqe_lcm {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.lcm a₀ a₁) (kNat.lcm b₀ b₁)
	| eqe_min {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.min a₀ a₁) (kNat.min b₀ b₁)
	| eqe_max {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.max a₀ a₁) (kNat.max b₀ b₁)
	| eqe_xor {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.xor a₀ a₁) (kNat.xor b₀ b₁)
	| eqe_bw_and {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.bw_and a₀ a₁) (kNat.bw_and b₀ b₁)
	| eqe_bw_or {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.bw_or a₀ a₁) (kNat.bw_or b₀ b₁)
	| eqe_rshift {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.rshift a₀ a₁) (kNat.rshift b₀ b₁)
	| eqe_lshift {a₀ b₀ a₁ b₁ : kNat} : kNat.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kNat.eqe (kNat.lshift a₀ a₁) (kNat.lshift b₀ b₁)

with kList.eqe : kList → kList → Prop
	| from_eqa {a b} : kList.eqa a b → kList.eqe a b
	| symm {a b} : kList.eqe a b → kList.eqe b a
	| trans {a b c} : kList.eqe a b → kList.eqe b c → kList.eqe a c
	-- Congruence axioms for each operator
	| eqe_phil {a₀ b₀ : kList} {a₁ b₁ : kNat} {a₂ b₂ : kList} : kList.eqe a₀ b₀ → kNat.eqe a₁ b₁ → kList.eqe a₂ b₂ → kList.eqe (kList.phil a₀ a₁ a₂) (kList.phil b₀ b₁ b₂)
	| eqe_join {a₀ b₀ a₁ b₁ : kList} : kList.eqe a₀ b₀ → kList.eqe a₁ b₁ → kList.eqe (kList.join a₀ a₁) (kList.join b₀ b₁)
	| eqe_initialList {a b : kNat} : kNat.eqe a b → kList.eqe (kList.initialList a) (kList.initialList b)
	-- Equations
	| eq_initialList₀ : kList.eqe (kList.initialList kNat.zero) kList.empty
	| eq_initialList₁ {n} : kNat.has_sort n MSort.Nat → kList.eqe (kList.initialList (kNat.s n)) (kList.join (kList.initialList n) (kList.join (kList.phil kList.o n kList.o) kList.fork))

with kTable.eqe : kTable → kTable → Prop
	| from_eqa {a b} : kTable.eqa a b → kTable.eqe a b
	| symm {a b} : kTable.eqe a b → kTable.eqe b a
	| trans {a b c} : kTable.eqe a b → kTable.eqe b c → kTable.eqe a c
	-- Congruence axioms for each operator
	| eqe_table {a b : kList} : kList.eqe a b → kTable.eqe (kTable.table a) (kTable.table b)
	| eqe_initial {a b : kNat} : kNat.eqe a b → kTable.eqe (kTable.initial a) (kTable.initial b)
	-- Equations
	| eq_initial {n} : kNat.has_sort n MSort.Nat → kTable.eqe (kTable.initial n) (kTable.table (kList.initialList n))
	| eq_table {l p} : kList.has_sort l MSort.List → kList.has_sort p MSort.Phil → kTable.eqe (kTable.table (kList.join kList.fork (kList.join l p))) (kTable.table (kList.join l (kList.join p kList.fork)))

infix (name := kBool_has_sort) ` ⊳ `:40 := kBool.has_sort
infix (name := kNat_has_sort) ` ⊳ `:40 := kNat.has_sort
infix (name := kList_has_sort) ` ⊳ `:40 := kList.has_sort
infix (name := kTable_has_sort) ` ⊳ `:40 := kTable.has_sort

infix (name := kBool_eqa) ` =A `:40 := kBool.eqa
infix (name := kNat_eqa) ` =A `:40 := kNat.eqa
infix (name := kList_eqa) ` =A `:40 := kList.eqa
infix (name := kTable_eqa) ` =A `:40 := kTable.eqa

infix (name := kBool_eqe) ` =E `:40 := kBool.eqe
infix (name := kNat_eqe) ` =E `:40 := kNat.eqe
infix (name := kList_eqe) ` =E `:40 := kList.eqe
infix (name := kTable_eqe) ` =E `:40 := kTable.eqe

-- Rewriting relations

mutual inductive kBool.rw_one, kNat.rw_one, kList.rw_one, kTable.rw_one, kBool.rw_star, kNat.rw_star, kList.rw_star, kTable.rw_star
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
	| sub_lt₀ {a₁ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.lt a a₁) (kBool.lt b a₁)
	| sub_lt₁ {a₀ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.lt a₀ a) (kBool.lt a₀ b)
	| sub_lteq₀ {a₁ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.lteq a a₁) (kBool.lteq b a₁)
	| sub_lteq₁ {a₀ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.lteq a₀ a) (kBool.lteq a₀ b)
	| sub_gt₀ {a₁ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.gt a a₁) (kBool.gt b a₁)
	| sub_gt₁ {a₀ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.gt a₀ a) (kBool.gt a₀ b)
	| sub_gteq₀ {a₁ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.gteq a a₁) (kBool.gteq b a₁)
	| sub_gteq₁ {a₀ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.gteq a₀ a) (kBool.gteq a₀ b)
	| sub_divides₀ {a₁ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.divides a a₁) (kBool.divides b a₁)
	| sub_divides₁ {a₀ a b} : kNat.rw_one a b →
		kBool.rw_one (kBool.divides a₀ a) (kBool.divides a₀ b)

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
	| sub_sd₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.sd a a₁) (kNat.sd b a₁)
	| sub_sd₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.sd a₀ a) (kNat.sd a₀ b)
	| sub_mul₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.mul a a₁) (kNat.mul b a₁)
	| sub_mul₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.mul a₀ a) (kNat.mul a₀ b)
	| sub_quo₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.quo a a₁) (kNat.quo b a₁)
	| sub_quo₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.quo a₀ a) (kNat.quo a₀ b)
	| sub_rem₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.rem a a₁) (kNat.rem b a₁)
	| sub_rem₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.rem a₀ a) (kNat.rem a₀ b)
	| sub_pow₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.pow a a₁) (kNat.pow b a₁)
	| sub_pow₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.pow a₀ a) (kNat.pow a₀ b)
	| sub_modExp₀ {a₁ a₂ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.modExp a a₁ a₂) (kNat.modExp b a₁ a₂)
	| sub_modExp₁ {a₀ a₂ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.modExp a₀ a a₂) (kNat.modExp a₀ b a₂)
	| sub_modExp₂ {a₀ a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.modExp a₀ a₁ a) (kNat.modExp a₀ a₁ b)
	| sub_gcd₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.gcd a a₁) (kNat.gcd b a₁)
	| sub_gcd₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.gcd a₀ a) (kNat.gcd a₀ b)
	| sub_lcm₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.lcm a a₁) (kNat.lcm b a₁)
	| sub_lcm₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.lcm a₀ a) (kNat.lcm a₀ b)
	| sub_min₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.min a a₁) (kNat.min b a₁)
	| sub_min₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.min a₀ a) (kNat.min a₀ b)
	| sub_max₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.max a a₁) (kNat.max b a₁)
	| sub_max₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.max a₀ a) (kNat.max a₀ b)
	| sub_xor₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.xor a a₁) (kNat.xor b a₁)
	| sub_xor₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.xor a₀ a) (kNat.xor a₀ b)
	| sub_bw_and₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.bw_and a a₁) (kNat.bw_and b a₁)
	| sub_bw_and₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.bw_and a₀ a) (kNat.bw_and a₀ b)
	| sub_bw_or₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.bw_or a a₁) (kNat.bw_or b a₁)
	| sub_bw_or₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.bw_or a₀ a) (kNat.bw_or a₀ b)
	| sub_rshift₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.rshift a a₁) (kNat.rshift b a₁)
	| sub_rshift₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.rshift a₀ a) (kNat.rshift a₀ b)
	| sub_lshift₀ {a₁ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.lshift a a₁) (kNat.lshift b a₁)
	| sub_lshift₁ {a₀ a b} : kNat.rw_one a b →
		kNat.rw_one (kNat.lshift a₀ a) (kNat.lshift a₀ b)

with kList.rw_one : kList → kList → Prop
	| eqe_left {a b c : kList} : a =E b → kList.rw_one b c → kList.rw_one a c
	| eqe_right {a b c : kList} : kList.rw_one a b → b =E c → kList.rw_one a c
	-- Axioms for rewriting inside subterms
	| sub_phil₀ {a₁ a₂ a b} : kList.rw_one a b →
		kList.rw_one (kList.phil a a₁ a₂) (kList.phil b a₁ a₂)
	| sub_phil₁ {a₀ a₂ a b} : kNat.rw_one a b →
		kList.rw_one (kList.phil a₀ a a₂) (kList.phil a₀ b a₂)
	| sub_phil₂ {a₀ a₁ a b} : kList.rw_one a b →
		kList.rw_one (kList.phil a₀ a₁ a) (kList.phil a₀ a₁ b)
	| sub_join₀ {a₁ a b} : kList.rw_one a b →
		kList.rw_one (kList.join a a₁) (kList.join b a₁)
	| sub_join₁ {a₀ a b} : kList.rw_one a b →
		kList.rw_one (kList.join a₀ a) (kList.join a₀ b)
	| sub_initialList {a b} : kNat.rw_one a b →
		kList.rw_one (kList.initialList a) (kList.initialList b)
	-- Rewrite rules
	| rl_left {id : kNat} {x : kList} : id ⊳ MSort.Nat → x ⊳ MSort.Obj → kList.rw_one (kList.join kList.fork (kList.phil kList.o id x)) (kList.phil kList.fork id x)
	| rl_right {x : kList} {id : kNat} : x ⊳ MSort.Obj → id ⊳ MSort.Nat → kList.rw_one (kList.join (kList.phil x id kList.o) kList.fork) (kList.phil x id kList.fork)
	| rl_release {id : kNat} : id ⊳ MSort.Nat → kList.rw_one (kList.phil kList.fork id kList.fork) (kList.join kList.fork (kList.join (kList.phil kList.o id kList.o) kList.fork))

with kTable.rw_one : kTable → kTable → Prop
	| eqe_left {a b c : kTable} : a =E b → kTable.rw_one b c → kTable.rw_one a c
	| eqe_right {a b c : kTable} : kTable.rw_one a b → b =E c → kTable.rw_one a c
	-- Axioms for rewriting inside subterms
	| sub_table {a b} : kList.rw_one a b →
		kTable.rw_one (kTable.table a) (kTable.table b)
	| sub_initial {a b} : kNat.rw_one a b →
		kTable.rw_one (kTable.initial a) (kTable.initial b)
	-- Rewrite rules
	| rl_left {id : kNat} {x l : kList} : id ⊳ MSort.Nat → x ⊳ MSort.Obj → l ⊳ MSort.List → kTable.rw_one (kTable.table (kList.join (kList.phil kList.o id x) (kList.join l kList.fork))) (kTable.table (kList.join (kList.phil kList.fork id x) l))

with kBool.rw_star : kBool → kBool → Prop
	| step {a b} : kBool.rw_one a b → kBool.rw_star a b
	| refl {a b : kBool} : a =E b → kBool.rw_star a b
	| trans {a b c} : kBool.rw_star a b → kBool.rw_star b c → kBool.rw_star a c

with kNat.rw_star : kNat → kNat → Prop
	| step {a b} : kNat.rw_one a b → kNat.rw_star a b
	| refl {a b : kNat} : a =E b → kNat.rw_star a b
	| trans {a b c} : kNat.rw_star a b → kNat.rw_star b c → kNat.rw_star a c

with kList.rw_star : kList → kList → Prop
	| step {a b} : kList.rw_one a b → kList.rw_star a b
	| refl {a b : kList} : a =E b → kList.rw_star a b
	| trans {a b c} : kList.rw_star a b → kList.rw_star b c → kList.rw_star a c

with kTable.rw_star : kTable → kTable → Prop
	| step {a b} : kTable.rw_one a b → kTable.rw_star a b
	| refl {a b : kTable} : a =E b → kTable.rw_star a b
	| trans {a b c} : kTable.rw_star a b → kTable.rw_star b c → kTable.rw_star a c

infix (name := kBool_rw_one) ` =>1 `:40 := kBool.rw_one
infix (name := kNat_rw_one) ` =>1 `:40 := kNat.rw_one
infix (name := kList_rw_one) ` =>1 `:40 := kList.rw_one
infix (name := kTable_rw_one) ` =>1 `:40 := kTable.rw_one

infix (name := kBool_rw_star) ` =>* `:40 := kBool.rw_star
infix (name := kNat_rw_star) ` =>* `:40 := kNat.rw_star
infix (name := kList_rw_star) ` =>* `:40 := kList.rw_star
infix (name := kTable_rw_star) ` =>* `:40 := kTable.rw_star

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
	def lt_decl := @has_sort.lt_decl
	def lteq_decl := @has_sort.lteq_decl
	def gt_decl := @has_sort.gt_decl
	def gteq_decl := @has_sort.gteq_decl
	def divides_decl := @has_sort.divides_decl
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
	def eqa_lt := @eqa.eqa_lt
	def eqe_lt := @eqe.eqe_lt
	def eqa_lteq := @eqa.eqa_lteq
	def eqe_lteq := @eqe.eqe_lteq
	def eqa_gt := @eqa.eqa_gt
	def eqe_gt := @eqe.eqe_gt
	def eqa_gteq := @eqa.eqa_gteq
	def eqe_gteq := @eqe.eqe_gteq
	def eqa_divides := @eqa.eqa_divides
	def eqe_divides := @eqe.eqe_divides
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
	attribute [congr] eqa.eqa_and eqe.eqe_and eqa.eqa_or eqe.eqe_or eqa.eqa_xor eqe.eqe_xor eqa.eqa_not eqe.eqe_not eqa.eqa_implies eqe.eqe_implies eqa.eqa_lt eqe.eqe_lt eqa.eqa_lteq eqe.eqe_lteq eqa.eqa_gt eqe.eqe_gt eqa.eqa_gteq eqe.eqe_gteq eqa.eqa_divides eqe.eqe_divides eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.true_decl has_sort.false_decl has_sort.and_decl has_sort.or_decl has_sort.xor_decl has_sort.not_decl has_sort.implies_decl has_sort.lt_decl has_sort.lteq_decl has_sort.gt_decl has_sort.gteq_decl has_sort.divides_decl eqe.eq_and₀ eqe.eq_and₁ eqe.eq_and₂ eqe.eq_xor₀ eqe.eq_xor₁ eqe.eq_and₃ eqe.eq_not eqe.eq_or eqe.eq_implies
end kBool

namespace kNat
	-- Sort membership lemmas
	lemma subsort_zero_nat {t : kNat} : t ⊳ MSort.Zero →
		t ⊳ MSort.Nat := by apply has_sort.subsort; simp [subsort]
	lemma subsort_nznat_nat {t : kNat} : t ⊳ MSort.NzNat →
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
	def sum_comm := @eqa.sum_comm
	def sum_assoc := @eqa.sum_assoc
	def sd_comm := @eqa.sd_comm
	def mul_comm := @eqa.mul_comm
	def mul_assoc := @eqa.mul_assoc
	def gcd_comm := @eqa.gcd_comm
	def gcd_assoc := @eqa.gcd_assoc
	def lcm_comm := @eqa.lcm_comm
	def lcm_assoc := @eqa.lcm_assoc
	def min_comm := @eqa.min_comm
	def min_assoc := @eqa.min_assoc
	def max_comm := @eqa.max_comm
	def max_assoc := @eqa.max_assoc
	def xor_comm := @eqa.xor_comm
	def xor_assoc := @eqa.xor_assoc
	def bw_and_comm := @eqa.bw_and_comm
	def bw_and_assoc := @eqa.bw_and_assoc
	def bw_or_comm := @eqa.bw_or_comm
	def bw_or_assoc := @eqa.bw_or_assoc
	def zero_decl := @has_sort.zero_decl
	def s_decl := @has_sort.s_decl
	def sum_decl₀ := @has_sort.sum_decl₀
	def sum_decl₁ := @has_sort.sum_decl₁
	def sum_decl₂ := @has_sort.sum_decl₂
	def sd_decl := @has_sort.sd_decl
	def mul_decl₀ := @has_sort.mul_decl₀
	def mul_decl₁ := @has_sort.mul_decl₁
	def quo_decl := @has_sort.quo_decl
	def rem_decl := @has_sort.rem_decl
	def pow_decl₀ := @has_sort.pow_decl₀
	def pow_decl₁ := @has_sort.pow_decl₁
	def gcd_decl₀ := @has_sort.gcd_decl₀
	def gcd_decl₁ := @has_sort.gcd_decl₁
	def gcd_decl₂ := @has_sort.gcd_decl₂
	def lcm_decl₀ := @has_sort.lcm_decl₀
	def lcm_decl₁ := @has_sort.lcm_decl₁
	def min_decl₀ := @has_sort.min_decl₀
	def min_decl₁ := @has_sort.min_decl₁
	def max_decl₀ := @has_sort.max_decl₀
	def max_decl₁ := @has_sort.max_decl₁
	def max_decl₂ := @has_sort.max_decl₂
	def xor_decl := @has_sort.xor_decl
	def bw_and_decl := @has_sort.bw_and_decl
	def bw_or_decl₀ := @has_sort.bw_or_decl₀
	def bw_or_decl₁ := @has_sort.bw_or_decl₁
	def bw_or_decl₂ := @has_sort.bw_or_decl₂
	def rshift_decl := @has_sort.rshift_decl
	def lshift_decl := @has_sort.lshift_decl
	def eqa_s := @eqa.eqa_s
	def eqe_s := @eqe.eqe_s
	def eqa_sum := @eqa.eqa_sum
	def eqe_sum := @eqe.eqe_sum
	def eqa_sd := @eqa.eqa_sd
	def eqe_sd := @eqe.eqe_sd
	def eqa_mul := @eqa.eqa_mul
	def eqe_mul := @eqe.eqe_mul
	def eqa_quo := @eqa.eqa_quo
	def eqe_quo := @eqe.eqe_quo
	def eqa_rem := @eqa.eqa_rem
	def eqe_rem := @eqe.eqe_rem
	def eqa_pow := @eqa.eqa_pow
	def eqe_pow := @eqe.eqe_pow
	def eqa_modExp := @eqa.eqa_modExp
	def eqe_modExp := @eqe.eqe_modExp
	def eqa_gcd := @eqa.eqa_gcd
	def eqe_gcd := @eqe.eqe_gcd
	def eqa_lcm := @eqa.eqa_lcm
	def eqe_lcm := @eqe.eqe_lcm
	def eqa_min := @eqa.eqa_min
	def eqe_min := @eqe.eqe_min
	def eqa_max := @eqa.eqa_max
	def eqe_max := @eqe.eqe_max
	def eqa_xor := @eqa.eqa_xor
	def eqe_xor := @eqe.eqe_xor
	def eqa_bw_and := @eqa.eqa_bw_and
	def eqe_bw_and := @eqe.eqe_bw_and
	def eqa_bw_or := @eqa.eqa_bw_or
	def eqe_bw_or := @eqe.eqe_bw_or
	def eqa_rshift := @eqa.eqa_rshift
	def eqe_rshift := @eqe.eqe_rshift
	def eqa_lshift := @eqa.eqa_lshift
	def eqe_lshift := @eqe.eqe_lshift

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_s eqe.eqe_s eqa.eqa_sum eqe.eqe_sum eqa.eqa_sd eqe.eqe_sd eqa.eqa_mul eqe.eqe_mul eqa.eqa_quo eqe.eqe_quo eqa.eqa_rem eqe.eqe_rem eqa.eqa_pow eqe.eqe_pow eqa.eqa_modExp eqe.eqe_modExp eqa.eqa_gcd eqe.eqe_gcd eqa.eqa_lcm eqe.eqe_lcm eqa.eqa_min eqe.eqe_min eqa.eqa_max eqe.eqe_max eqa.eqa_xor eqe.eqe_xor eqa.eqa_bw_and eqe.eqe_bw_and eqa.eqa_bw_or eqe.eqe_bw_or eqa.eqa_rshift eqe.eqe_rshift eqa.eqa_lshift eqe.eqe_lshift eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.zero_decl has_sort.s_decl has_sort.sum_decl₀ has_sort.sum_decl₁ has_sort.sum_decl₂ has_sort.sd_decl has_sort.mul_decl₀ has_sort.mul_decl₁ has_sort.quo_decl has_sort.rem_decl has_sort.pow_decl₀ has_sort.pow_decl₁ has_sort.gcd_decl₀ has_sort.gcd_decl₁ has_sort.gcd_decl₂ has_sort.lcm_decl₀ has_sort.lcm_decl₁ has_sort.min_decl₀ has_sort.min_decl₁ has_sort.max_decl₀ has_sort.max_decl₁ has_sort.max_decl₂ has_sort.xor_decl has_sort.bw_and_decl has_sort.bw_or_decl₀ has_sort.bw_or_decl₁ has_sort.bw_or_decl₂ has_sort.rshift_decl has_sort.lshift_decl subsort_zero_nat subsort_nznat_nat
end kNat

namespace kList
	-- Sort membership lemmas
	lemma subsort_being_list {t : kList} : t ⊳ MSort.Being →
		t ⊳ MSort.List := by apply has_sort.subsort; simp [subsort]
	lemma subsort_obj_being {t : kList} : t ⊳ MSort.Obj →
		t ⊳ MSort.Being := by apply has_sort.subsort; simp [subsort]
	lemma subsort_phil_being {t : kList} : t ⊳ MSort.Phil →
		t ⊳ MSort.Being := by apply has_sort.subsort; simp [subsort]

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kList) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kList} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kList} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kList} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Aliases
	def join_assoc := @eqa.join_assoc
	def phil_decl := @has_sort.phil_decl
	def o_decl := @has_sort.o_decl
	def fork_decl := @has_sort.fork_decl
	def empty_decl := @has_sort.empty_decl
	def join_decl := @has_sort.join_decl
	def initialList_decl := @has_sort.initialList_decl
	def eqa_phil := @eqa.eqa_phil
	def eqe_phil := @eqe.eqe_phil
	def eqa_join := @eqa.eqa_join
	def eqe_join := @eqe.eqe_join
	def eqa_initialList := @eqa.eqa_initialList
	def eqe_initialList := @eqe.eqe_initialList
	def eq_initialList₀ := @eqe.eq_initialList₀
	def eq_initialList₁ := @eqe.eq_initialList₁

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_phil eqe.eqe_phil eqa.eqa_join eqe.eqe_join eqa.eqa_initialList eqe.eqe_initialList eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.phil_decl has_sort.o_decl has_sort.fork_decl has_sort.empty_decl has_sort.join_decl has_sort.initialList_decl eqe.eq_initialList₀ eqe.eq_initialList₁ subsort_being_list subsort_obj_being subsort_phil_being
end kList

namespace kTable
	-- Sort membership lemmas

	-- Reflexivity and congruence lemmas
	@[refl] lemma eqe_refl (a : kTable) : a =E a := eqe.from_eqa eqa.refl
	lemma eqa_congr {a b c d : kTable} : a =A b → c =A d → (a =A c) = (b =A d)
		:= generic_congr @eqa.trans @eqa.trans @eqa.symm
	lemma eqe_congr {a b c d : kTable} : a =E b → c =E d → (a =E c) = (b =E d)
		:= generic_congr @eqe.trans @eqe.trans @eqe.symm
	lemma eqa_eqe_congr {a b c d : kTable} : a =A b → c =A d → (a =E c) = (b =E d)
		:= generic_congr (λ {x y z}, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Aliases
	def table_decl := @has_sort.table_decl
	def initial_decl := @has_sort.initial_decl
	def eqa_table := @eqa.eqa_table
	def eqe_table := @eqe.eqe_table
	def eqa_initial := @eqa.eqa_initial
	def eqe_initial := @eqe.eqe_initial
	def eq_initial := @eqe.eq_initial
	def eq_table := @eqe.eq_table

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] eqa.refl
	attribute [symm] eqa.symm eqe.symm
	attribute [trans] eqa.trans eqe.trans
	attribute [congr] eqa.eqa_table eqe.eqe_table eqa.eqa_initial eqe.eqe_initial eqa_congr eqe_congr eqa_eqe_congr
	attribute [simp] has_sort.table_decl has_sort.initial_decl eqe.eq_initial eqe.eq_table
end kTable

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
	lemma rw_star_sub_lt₀ {a b a₁ : kNat} : a =>* b →
			(lt a a₁) =>* (lt b a₁) := by infer_sub_star ``(rw_one.sub_lt₀) ``(eqe.eqe_lt)
	lemma rw_star_sub_lt₁ {a₀ a b : kNat} : a =>* b →
			(lt a₀ a) =>* (lt a₀ b) := by infer_sub_star ``(rw_one.sub_lt₁) ``(eqe.eqe_lt)
	lemma rw_star_sub_lteq₀ {a b a₁ : kNat} : a =>* b →
			(lteq a a₁) =>* (lteq b a₁) := by infer_sub_star ``(rw_one.sub_lteq₀) ``(eqe.eqe_lteq)
	lemma rw_star_sub_lteq₁ {a₀ a b : kNat} : a =>* b →
			(lteq a₀ a) =>* (lteq a₀ b) := by infer_sub_star ``(rw_one.sub_lteq₁) ``(eqe.eqe_lteq)
	lemma rw_star_sub_gt₀ {a b a₁ : kNat} : a =>* b →
			(gt a a₁) =>* (gt b a₁) := by infer_sub_star ``(rw_one.sub_gt₀) ``(eqe.eqe_gt)
	lemma rw_star_sub_gt₁ {a₀ a b : kNat} : a =>* b →
			(gt a₀ a) =>* (gt a₀ b) := by infer_sub_star ``(rw_one.sub_gt₁) ``(eqe.eqe_gt)
	lemma rw_star_sub_gteq₀ {a b a₁ : kNat} : a =>* b →
			(gteq a a₁) =>* (gteq b a₁) := by infer_sub_star ``(rw_one.sub_gteq₀) ``(eqe.eqe_gteq)
	lemma rw_star_sub_gteq₁ {a₀ a b : kNat} : a =>* b →
			(gteq a₀ a) =>* (gteq a₀ b) := by infer_sub_star ``(rw_one.sub_gteq₁) ``(eqe.eqe_gteq)
	lemma rw_star_sub_divides₀ {a b a₁ : kNat} : a =>* b →
			(divides a a₁) =>* (divides b a₁) := by infer_sub_star ``(rw_one.sub_divides₀) ``(eqe.eqe_divides)
	lemma rw_star_sub_divides₁ {a₀ a b : kNat} : a =>* b →
			(divides a₀ a) =>* (divides a₀ b) := by infer_sub_star ``(rw_one.sub_divides₁) ``(eqe.eqe_divides)
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
	lemma rw_star_sub_sd₀ {a b a₁ : kNat} : a =>* b →
			(sd a a₁) =>* (sd b a₁) := by infer_sub_star ``(rw_one.sub_sd₀) ``(eqe.eqe_sd)
	lemma rw_star_sub_sd₁ {a₀ a b : kNat} : a =>* b →
			(sd a₀ a) =>* (sd a₀ b) := by infer_sub_star ``(rw_one.sub_sd₁) ``(eqe.eqe_sd)
	lemma rw_star_sub_mul₀ {a b a₁ : kNat} : a =>* b →
			(mul a a₁) =>* (mul b a₁) := by infer_sub_star ``(rw_one.sub_mul₀) ``(eqe.eqe_mul)
	lemma rw_star_sub_mul₁ {a₀ a b : kNat} : a =>* b →
			(mul a₀ a) =>* (mul a₀ b) := by infer_sub_star ``(rw_one.sub_mul₁) ``(eqe.eqe_mul)
	lemma rw_star_sub_quo₀ {a b a₁ : kNat} : a =>* b →
			(quo a a₁) =>* (quo b a₁) := by infer_sub_star ``(rw_one.sub_quo₀) ``(eqe.eqe_quo)
	lemma rw_star_sub_quo₁ {a₀ a b : kNat} : a =>* b →
			(quo a₀ a) =>* (quo a₀ b) := by infer_sub_star ``(rw_one.sub_quo₁) ``(eqe.eqe_quo)
	lemma rw_star_sub_rem₀ {a b a₁ : kNat} : a =>* b →
			(rem a a₁) =>* (rem b a₁) := by infer_sub_star ``(rw_one.sub_rem₀) ``(eqe.eqe_rem)
	lemma rw_star_sub_rem₁ {a₀ a b : kNat} : a =>* b →
			(rem a₀ a) =>* (rem a₀ b) := by infer_sub_star ``(rw_one.sub_rem₁) ``(eqe.eqe_rem)
	lemma rw_star_sub_pow₀ {a b a₁ : kNat} : a =>* b →
			(pow a a₁) =>* (pow b a₁) := by infer_sub_star ``(rw_one.sub_pow₀) ``(eqe.eqe_pow)
	lemma rw_star_sub_pow₁ {a₀ a b : kNat} : a =>* b →
			(pow a₀ a) =>* (pow a₀ b) := by infer_sub_star ``(rw_one.sub_pow₁) ``(eqe.eqe_pow)
	lemma rw_star_sub_modExp₀ {a b a₁ a₂ : kNat} : a =>* b →
			(modExp a a₁ a₂) =>* (modExp b a₁ a₂) := by infer_sub_star ``(rw_one.sub_modExp₀) ``(eqe.eqe_modExp)
	lemma rw_star_sub_modExp₁ {a₀ a b a₂ : kNat} : a =>* b →
			(modExp a₀ a a₂) =>* (modExp a₀ b a₂) := by infer_sub_star ``(rw_one.sub_modExp₁) ``(eqe.eqe_modExp)
	lemma rw_star_sub_modExp₂ {a₀ a₁ a b : kNat} : a =>* b →
			(modExp a₀ a₁ a) =>* (modExp a₀ a₁ b) := by infer_sub_star ``(rw_one.sub_modExp₂) ``(eqe.eqe_modExp)
	lemma rw_star_sub_gcd₀ {a b a₁ : kNat} : a =>* b →
			(gcd a a₁) =>* (gcd b a₁) := by infer_sub_star ``(rw_one.sub_gcd₀) ``(eqe.eqe_gcd)
	lemma rw_star_sub_gcd₁ {a₀ a b : kNat} : a =>* b →
			(gcd a₀ a) =>* (gcd a₀ b) := by infer_sub_star ``(rw_one.sub_gcd₁) ``(eqe.eqe_gcd)
	lemma rw_star_sub_lcm₀ {a b a₁ : kNat} : a =>* b →
			(lcm a a₁) =>* (lcm b a₁) := by infer_sub_star ``(rw_one.sub_lcm₀) ``(eqe.eqe_lcm)
	lemma rw_star_sub_lcm₁ {a₀ a b : kNat} : a =>* b →
			(lcm a₀ a) =>* (lcm a₀ b) := by infer_sub_star ``(rw_one.sub_lcm₁) ``(eqe.eqe_lcm)
	lemma rw_star_sub_min₀ {a b a₁ : kNat} : a =>* b →
			(min a a₁) =>* (min b a₁) := by infer_sub_star ``(rw_one.sub_min₀) ``(eqe.eqe_min)
	lemma rw_star_sub_min₁ {a₀ a b : kNat} : a =>* b →
			(min a₀ a) =>* (min a₀ b) := by infer_sub_star ``(rw_one.sub_min₁) ``(eqe.eqe_min)
	lemma rw_star_sub_max₀ {a b a₁ : kNat} : a =>* b →
			(max a a₁) =>* (max b a₁) := by infer_sub_star ``(rw_one.sub_max₀) ``(eqe.eqe_max)
	lemma rw_star_sub_max₁ {a₀ a b : kNat} : a =>* b →
			(max a₀ a) =>* (max a₀ b) := by infer_sub_star ``(rw_one.sub_max₁) ``(eqe.eqe_max)
	lemma rw_star_sub_xor₀ {a b a₁ : kNat} : a =>* b →
			(xor a a₁) =>* (xor b a₁) := by infer_sub_star ``(rw_one.sub_xor₀) ``(eqe.eqe_xor)
	lemma rw_star_sub_xor₁ {a₀ a b : kNat} : a =>* b →
			(xor a₀ a) =>* (xor a₀ b) := by infer_sub_star ``(rw_one.sub_xor₁) ``(eqe.eqe_xor)
	lemma rw_star_sub_bw_and₀ {a b a₁ : kNat} : a =>* b →
			(bw_and a a₁) =>* (bw_and b a₁) := by infer_sub_star ``(rw_one.sub_bw_and₀) ``(eqe.eqe_bw_and)
	lemma rw_star_sub_bw_and₁ {a₀ a b : kNat} : a =>* b →
			(bw_and a₀ a) =>* (bw_and a₀ b) := by infer_sub_star ``(rw_one.sub_bw_and₁) ``(eqe.eqe_bw_and)
	lemma rw_star_sub_bw_or₀ {a b a₁ : kNat} : a =>* b →
			(bw_or a a₁) =>* (bw_or b a₁) := by infer_sub_star ``(rw_one.sub_bw_or₀) ``(eqe.eqe_bw_or)
	lemma rw_star_sub_bw_or₁ {a₀ a b : kNat} : a =>* b →
			(bw_or a₀ a) =>* (bw_or a₀ b) := by infer_sub_star ``(rw_one.sub_bw_or₁) ``(eqe.eqe_bw_or)
	lemma rw_star_sub_rshift₀ {a b a₁ : kNat} : a =>* b →
			(rshift a a₁) =>* (rshift b a₁) := by infer_sub_star ``(rw_one.sub_rshift₀) ``(eqe.eqe_rshift)
	lemma rw_star_sub_rshift₁ {a₀ a b : kNat} : a =>* b →
			(rshift a₀ a) =>* (rshift a₀ b) := by infer_sub_star ``(rw_one.sub_rshift₁) ``(eqe.eqe_rshift)
	lemma rw_star_sub_lshift₀ {a b a₁ : kNat} : a =>* b →
			(lshift a a₁) =>* (lshift b a₁) := by infer_sub_star ``(rw_one.sub_lshift₀) ``(eqe.eqe_lshift)
	lemma rw_star_sub_lshift₁ {a₀ a b : kNat} : a =>* b →
			(lshift a₀ a) =>* (lshift a₀ b) := by infer_sub_star ``(rw_one.sub_lshift₁) ``(eqe.eqe_lshift)
end kNat

namespace kList
	-- Congruence lemmas
	@[congr] lemma eqe_rw_one_congr {a b c d : kList} : a =E b → c =E d → (a =>1 c) = (b =>1 d)
		:= generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
	@[congr] lemma eqa_rw_one_congr {a b c d : kList} : a =A b → c =A d → (a =>1 c) = (b =>1 d)
		:= generic_congr (λ {x y z}, (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
	@[congr] lemma eqe_rw_star_congr {a b c d : kList} : a =E b → c =E d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
	@[congr] lemma eqa_rw_star_congr {a b c d : kList} : a =A b → c =A d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Aliases for rewrite rules
	def rl_left := @rw_one.rl_left
	def rl_right := @rw_one.rl_right
	def rl_release := @rw_one.rl_release

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] rw_star.refl
	attribute [trans] rw_star.trans

	-- Lemmas for subterm rewriting with =>*
	lemma rw_star_sub_phil₀ {a b : kList} {a₁ : kNat} {a₂ : kList} : a =>* b →
			(phil a a₁ a₂) =>* (phil b a₁ a₂) := by infer_sub_star ``(rw_one.sub_phil₀) ``(eqe.eqe_phil)
	lemma rw_star_sub_phil₁ {a₀ : kList} {a b : kNat} {a₂ : kList} : a =>* b →
			(phil a₀ a a₂) =>* (phil a₀ b a₂) := by infer_sub_star ``(rw_one.sub_phil₁) ``(eqe.eqe_phil)
	lemma rw_star_sub_phil₂ {a₀ : kList} {a₁ : kNat} {a b : kList} : a =>* b →
			(phil a₀ a₁ a) =>* (phil a₀ a₁ b) := by infer_sub_star ``(rw_one.sub_phil₂) ``(eqe.eqe_phil)
	lemma rw_star_sub_join₀ {a b a₁ : kList} : a =>* b →
			(join a a₁) =>* (join b a₁) := by infer_sub_star ``(rw_one.sub_join₀) ``(eqe.eqe_join)
	lemma rw_star_sub_join₁ {a₀ a b : kList} : a =>* b →
			(join a₀ a) =>* (join a₀ b) := by infer_sub_star ``(rw_one.sub_join₁) ``(eqe.eqe_join)
	lemma rw_star_sub_initialList {a b : kNat} : a =>* b →
			(initialList a) =>* (initialList b) := by infer_sub_star ``(rw_one.sub_initialList) ``(eqe.eqe_initialList)
end kList

namespace kTable
	-- Congruence lemmas
	@[congr] lemma eqe_rw_one_congr {a b c d : kTable} : a =E b → c =E d → (a =>1 c) = (b =>1 d)
		:= generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
	@[congr] lemma eqa_rw_one_congr {a b c d : kTable} : a =A b → c =A d → (a =>1 c) = (b =>1 d)
		:= generic_congr (λ {x y z}, (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
	@[congr] lemma eqe_rw_star_congr {a b c d : kTable} : a =E b → c =E d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
	@[congr] lemma eqa_rw_star_congr {a b c d : kTable} : a =A b → c =A d → (a =>* c) = (b =>* d)
		:= generic_congr (λ {x y z}, (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
			(λ {x y z h}, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

	-- Aliases for rewrite rules
	def rl_left := @rw_one.rl_left

	-- Attributes for the Lean simplifier and machinery
	attribute [refl] rw_star.refl
	attribute [trans] rw_star.trans

	-- Lemmas for subterm rewriting with =>*
	lemma rw_star_sub_table {a b : kList} : a =>* b →
			(table a) =>* (table b) := by infer_sub_star ``(rw_one.sub_table) ``(eqe.eqe_table)
	lemma rw_star_sub_initial {a b : kNat} : a =>* b →
			(initial a) =>* (initial b) := by infer_sub_star ``(rw_one.sub_initial) ``(eqe.eqe_initial)
end kTable

end Maude
