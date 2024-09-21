import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 7

Title "TBA"

open Real

Statement (x : ℝ) : deriv (fun x : ℝ => x) (x : ℝ) = 1 := by
  Hint "Differentiation of the identity map on ℝ is a known result in Mathlib4, so you can take advantage of this lemma, which is called `deriv_id''`. Besure to check its statement in the right panel. Use tatic `rw` to rewrite the goal or `apply` to apply the lemma."
  rw [deriv_id'']

NewTactic rw apply

/-- The derivative of Identity function $f(x) = x$ on ℝ is $1$ -/
TheoremDoc deriv_id'' as "deriv_id''" in "Derivative"

NewTheorem deriv_id''
