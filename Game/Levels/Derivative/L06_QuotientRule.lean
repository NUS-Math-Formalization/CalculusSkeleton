import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 6

Title "Quotient Rule"

Statement (x : ℝ) : deriv (fun x => (Real.sin x) / (x ^ 2 + 1)) (x : ℝ) =
  ((Real.cos x) * (x ^ 2 + 1) - (Real.sin x) * (2 * x)) / (x ^ 2 + 1) ^ 2 := by
  Hint "To apply the quotient rule, use `deriv_div`"
  rw [deriv_div]
  Hint "To differentiate the sine function, use `Real.deriv_sin`"
  rw [Real.deriv_sin]
  rw [deriv_add]
  rw [deriv_pow']
  rw [deriv_const]
  ring_nf

  exact differentiableAt_pow 2
  exact differentiableAt_const 1
  Hint "To show differentiability of the sine function, use `Real.differentiableAt_sin`."
  exact Real.differentiableAt_sin
  apply DifferentiableAt.add
  exact differentiableAt_pow 2
  exact differentiableAt_const 1

  Hint "To show that $x ^ 2 + 1 ≠ 0,$ you can show $x ^ 2 + 1 ≥ 1$ instead."
  have : x ^ 2 + 1 ≥ 1 := by
    apply le_add_of_nonneg_left
    exact sq_nonneg x
  linarith

/-- Quotient rule: for differentiable functions $f$ and $g$ with $g(x)≠0,$ one has
  $(f/g)'(x)=((f'g-fg')/g^2)(x).$-/
TheoremDoc deriv_div as "deriv_div" in "Derivative"

/-- Derivative of the sine function is the cosine function. -/
TheoremDoc Real.deriv_sin as "Real.deriv_sin" in "Derivative"

/-- The sine function is differentiable. -/
TheoremDoc Real.differentiableAt_sin as "Real.differentiableAt_sin" in "Derivative"

NewTheorem deriv_div Real.deriv_sin Real.differentiableAt_sin
