import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 7

Title "tan test"

--local notation:max "Real.sec (t: 210)" => 1 / Real.cos t

Statement (x : ℝ) : deriv (fun x => Real.tan (1 / (Real.exp x + Real.exp (-x)))) (x : ℝ)
  = 1 / (Real.cos (1 / (Real.exp x + Real.exp (-x))))^2 *
    (- Real.exp x + Real.exp (-x)) / (Real.exp x + Real.exp (-x))^2 := by
  set g := fun x => 1 / (Real.exp x + Real.exp (-x))
  set h := fun x => Real.exp x + Real.exp (-x)
  set l := fun (x : ℝ) => (- 1) * x
  have l1 : (fun x => Real.tan (1 / (Real.exp x + Real.exp (-x)))) = Real.tan ∘ g := by rfl
  have l2 : g = fun x => (h x)⁻¹ := by
    funext
    rw [← one_div]
  have l3 : (fun x => Real.exp (-x)) = Real.exp ∘ l := by
    funext
    rw [← neg_one_mul]
    rfl
  have : Real.exp x + Real.exp (-x) > 0 := by
      apply Right.add_pos
      exact Real.exp_pos x
      exact Real.exp_pos (-x)
  have l4 : h x ≠ 0 := by exact Ne.symm (ne_of_lt this)
  have l5 : 0 < g x := by exact one_div_pos.mpr this
  have l6 : g x ≤ 1 / 2 := by
    have : h x - 2 = (Real.exp (x / 2) - Real.exp (-x / 2)) ^ 2 := by
      ring_nf
      rw [← Real.exp_add]
      rw [← Real.exp_nsmul]
      rw [← Real.exp_nsmul]
      ring_nf
      rw [Real.exp_zero]
      ring_nf
    have : h x - 2 ≥ 0 := by
      rw [this]
      exact sq_nonneg (Real.exp (x / 2) - Real.exp (-x / 2))
    have : h x ≥ 2 := by linarith
    apply one_div_le_one_div_of_le
    norm_num
    exact this
  rw [l1]
  rw [deriv.comp]
  rw [Real.deriv_tan]
  nth_rw 2 [l2]
  rw [mul_div_assoc]
  rw [deriv_inv'']
  congr
  rw [deriv_add]
  rw [l3]
  rw [deriv.comp]
  rw [deriv_exp]
  rw [deriv_exp]
  rw [deriv_id'']
  simp only [mul_one, neg_add_rev]
  rw [deriv_const_mul]
  rw [deriv_id'']
  simp only [mul_one, mul_neg, neg_neg]
  rw [add_comm]
  rw [← neg_one_mul x]

  exact differentiableAt_id'
  exact differentiableAt_id'
  exact differentiableAt_id'
  exact Real.differentiableAt_exp
  apply DifferentiableAt.const_mul
  exact differentiableAt_id'
  exact Real.differentiableAt_exp
  rw [l3]
  apply DifferentiableAt.comp
  exact Real.differentiableAt_exp
  apply DifferentiableAt.const_mul
  exact differentiableAt_id'
  apply DifferentiableAt.add
  exact Real.differentiableAt_exp
  rw [l3]
  apply DifferentiableAt.comp
  exact Real.differentiableAt_exp
  apply DifferentiableAt.const_mul
  exact differentiableAt_id'
  exact l4
  apply Real.differentiableAt_tan.mpr
  apply Real.cos_ne_zero_iff.mpr
  intro k
  by_contra
  have : k > 0 := by sorry
  have : k ≤ 1 / 2 * (1 / Real.pi - 1) := by sorry
  have : k < 0 := by sorry
  linarith
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.inv'
  apply DifferentiableAt.add
  exact Real.differentiableAt_exp
  rw [l3]
  apply DifferentiableAt.comp
  exact Real.differentiableAt_exp
  apply DifferentiableAt.const_mul
  exact differentiableAt_id'
  exact l4
