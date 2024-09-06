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
  rw [deriv_div]
  rw [Real.deriv_sin]
  rw [deriv_add]
  rw [deriv_pow']
  rw [deriv_const]
  ring_nf

  exact differentiableAt_pow 2
  exact differentiableAt_const 1
  exact Real.differentiableAt_sin
  apply DifferentiableAt.add
  exact differentiableAt_pow 2
  exact differentiableAt_const 1

  have : x ^ 2 + 1 ≥ 1 := by
    apply le_add_of_nonneg_left
    exact sq_nonneg x
  linarith
