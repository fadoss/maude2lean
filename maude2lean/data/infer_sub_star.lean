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
