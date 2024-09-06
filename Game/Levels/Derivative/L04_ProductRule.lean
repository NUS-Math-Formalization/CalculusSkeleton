import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 4

Title "Product Rule"

Statement (x : ℝ) : deriv (fun x => x * Real.exp x) (x : ℝ) = (x + 1) * Real.exp x := by
  Hint "To apply the product rule, use `deriv_mul`."
  rw [deriv_mul]
  Hint "To differentiate the exponential function, use `Real.deriv_exp`."
  rw [Real.deriv_exp]
  rw [deriv_id'']
  ring_nf

  exact differentiableAt_id'
  Hint "To show the exponential function is differentiable, use `Real.differentiableAt_exp`."
  exact Real.differentiableAt_exp

/-- Product rule: for differentiable functions $f$ and $g$, one has $(fg)'=f'g+fg'.$ -/
TheoremDoc deriv_mul as "deriv_mul" in "Derivative"

/-- Derivative of exponential function: $(e^x)'=e^x.$ -/
TheoremDoc Real.deriv_exp as "Real.deriv_exp" in "Derivative"

/-- The exponential function is differentiable. -/
TheoremDoc Real.differentiableAt_exp as "Real.differentiableAt_exp" in "Derivative"

NewTactic ring_nf

NewTheorem deriv_mul Real.deriv_exp Real.differentiableAt_exp
