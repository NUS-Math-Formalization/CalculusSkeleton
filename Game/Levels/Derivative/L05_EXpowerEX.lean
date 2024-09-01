import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 5

Title "exp to the exp"

Statement (x : ℝ) : deriv (fun x => Real.exp x ^ Real.exp x) (x : ℝ)
  = (Real.exp (x + x * Real.exp x)) * (x + 1) := by
  simp_rw [← Real.exp_mul]
  set g := fun x => x * Real.exp x
  have : (fun x => Real.exp (x * Real.exp x)) = fun x => (Real.exp ∘ g) x := rfl
  rw [this]
  rw [deriv.comp]
  rw [Real.deriv_exp]
  rw [deriv_mul]
  rw [deriv_id'']
  rw [one_mul]
  rw [deriv_exp]
  rw [deriv_id'']
  rw [mul_one]
  rw [Real.exp_add]
  rw [Real.exp_mul]
  rw [mul_add, mul_add]
  rw [add_comm]
  congr 1
  rw [mul_comm]
  nth_rw 3 [mul_comm]
  rw [mul_assoc]
  rw [mul_one]
  rw [mul_comm]
  exact differentiableAt_id'
  exact differentiableAt_id'
  exact Real.differentiableAt_exp
  exact Real.differentiableAt_exp
  apply DifferentiableAt.mul
  exact differentiableAt_id'
  exact Real.differentiableAt_exp

NewTactic nth_rw congr

-- add the theorems later
