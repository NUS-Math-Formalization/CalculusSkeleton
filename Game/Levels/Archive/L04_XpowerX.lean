import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 4

Title "X ^ X"

Statement (x : ℝ) (hx : x > 0) : deriv (fun x => x ^ x) (x : ℝ)
  = (x ^ x) * (Real.log x + 1) := by
  simp_rw [Real.rpow_def_of_pos hx]
  set g := fun x => Real.log x * ((fun y => y) x)
  have (y : ℝ) (hy : y > 0) :
    deriv (fun x => x ^ x) y = deriv (fun x => ((Real.exp ∘ g) x)) y := by
    simp only [Function.comp_apply]
    congr; ext
    rw [Real.rpow_def_of_pos]
    sorry
  rw [this x hx]
  rw [deriv.comp]
  rw [Real.deriv_exp]
  rw [mul_eq_mul_left_iff]
  left
  rw [deriv_mul]
  rw [Real.deriv_log']
  rw [deriv_id'']
  simp only [mul_one]
  rw [inv_mul_cancel (ne_of_gt hx)]
  rw [add_comm]
  apply Real.differentiableAt_log
  exact ne_of_gt hx
  exact differentiableAt_id'
  exact Real.differentiableAt_exp
  apply DifferentiableAt.mul
  apply Real.differentiableAt_log
  exact ne_of_gt hx
  exact differentiableAt_id'
