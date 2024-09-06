import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 5

Title "exp to the exp"

-- the following are proven in level 4, so this level is just an application of chain rule
lemma deriv_xexpx (x : ℝ) :
  deriv (fun x => x * Real.exp x) (x : ℝ) = (x + 1) * Real.exp x := by sorry

lemma xexpx_differentiable (x : ℝ) : DifferentiableAt ℝ (fun x => x * Real.exp x) x := by sorry

Statement (x : ℝ) : deriv (fun x => Real.exp x ^ Real.exp x) (x : ℝ)
  = (Real.exp (x + x * Real.exp x)) * (x + 1) := by
  simp_rw [← Real.exp_mul]
  set g := fun x => x * Real.exp x
  have : (fun x => Real.exp (x * Real.exp x)) = Real.exp ∘ g := rfl
  rw [this]
  rw [deriv.comp]
  rw [Real.deriv_exp]
  rw [deriv_xexpx]
  rw [mul_comm (x + 1) (Real.exp x)]
  rw [← mul_assoc]
  rw [mul_comm (Real.exp (g x))]
  rw [Real.exp_add]

  exact Real.differentiableAt_exp
  exact xexpx_differentiable x

-- add the theorems later
