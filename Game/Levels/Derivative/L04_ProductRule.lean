import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 4

Title "Product Rule"

Statement (x : ℝ) : deriv (fun x => x * Real.exp x) (x : ℝ) = (x + 1) * Real.exp x := by
  rw [deriv_mul]
  rw [Real.deriv_exp]
  rw [deriv_id'']
  rw [one_mul]
  ring_nf

  exact differentiableAt_id'
  exact Real.differentiableAt_exp
