import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 3

Title "Differente Square"

Statement (x : ℝ) : deriv (fun x => x ^ 2 + 3 * x + 1) (x : ℝ) = 2 * x + 3 := by
  Hint "Rewrite the formula using a combination of `derive_add` `derive_pow'` `derive_mul` `derive_mul`, `derive_id`, `derive_const`. You are now recommended to use `simp` to close the goal."
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_pow']
  rw [deriv_mul, deriv_id'']
  rw [deriv_const]
  simp
  Hint "Now show all the differentiability conditions required by previous proof steps."
  exact differentiableAt_const 3
  exact differentiableAt_id'
  exact differentiableAt_pow 2
  apply DifferentiableAt.const_mul
  exact differentiableAt_id'
  apply DifferentiableAt.add
  exact differentiableAt_pow 2
  apply DifferentiableAt.const_mul
  exact differentiableAt_id'
  exact differentiableAt_const 1
  
NewTactic simp apply

TheoremDoc deriv_pow' as "deriv_pow'" in "Derivative"
TheoremDoc deriv_mul as "deriv_mul" in "Derivative"
TheoremDoc differentiableAt_pow as "differentiable_pow" in "Differentiable"
TheoremDoc DifferentiableAt.const_mul as "const_mul" in "Differentiable"
TheoremDoc DifferentiableAt.add as "const_mul" in "Differentiable"

NewTheorem deriv_pow' deriv_mul differentiableAt_pow DifferentiableAt.const_mul DifferentiableAt.add
