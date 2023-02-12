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
