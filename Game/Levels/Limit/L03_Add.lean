import Game.Metadata
import Game.Lemmas.Limits.Basic
import Game.Lemmas.Limits.Lemmas
import Game.Lemmas.Limits.LimitLaws
import Game.Lemmas.Inequalities

open Real Topology

World "Limit"

Level 3

Introduction "What you proved in the previous level have been summarized into lemmas, try to use these lemmas to tackle this problem."

Statement : lim x → 0, (sin x + 2 * x) = 0 := by
  Hint "Recall `deriv_add`. Use `lim_add` to deal with the addition of limits"
  rw [lim_add]
  · rw [lim_two_mul_zero, lim_sin_zero]; simp
  · exact HasLimAt_sin_zero
  · exact HasLimAt_two_mul_zero


/-- TODO -/
TheoremDoc lim_add as "lim_add" in "Limit"
/-- TODO -/
TheoremDoc lim_two_mul_zero as "lim_two_mul_zero" in "Proved Lims"
/-- TODO -/
TheoremDoc lim_sin_zero as "lim_sin_zero" in "Proved Lims"
/-- TODO -/
TheoremDoc HasLimAt_two_mul_zero as "HasLimAt_two_mul_zero" in "Proved Lims"
/-- TODO -/
TheoremDoc HasLimAt_sin_zero as "HasLimAt_sin_zero" in "Proved Lims"

NewTheorem lim_two_mul_zero lim_sin_zero HasLimAt_sin_zero HasLimAt_two_mul_zero lim_add
