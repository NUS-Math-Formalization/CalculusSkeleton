import Game.Lemmas.Limits.Basic
import Game.Lemmas.Limits.LimitLaws
import Game.Lemmas.Derivatives.Basic

-- prove derivatives of different functions here...
-- polynomial, exp, ln, trig, inverse trig. that's all :)

variable {c : ℝ}

private lemma id_pre : ∃ δ > 0, ∀ (x : ℝ), 0 < |x - c| ∧ |x - c| < δ → (x - c) / (x - c) = 1 := by
  use 1
  constructor
  . norm_num
  . intro x h
    apply div_self
    exact abs_pos.mp h.left

lemma my_differentiable_id : my_differentiable (fun x => x) c := by
  rw [my_differentiable]
  set f := fun x => (x - c) / (x - c)
  set g := fun (_ : ℝ) => (1 : ℝ)
  have l1 : HasLimAt g c := HasLimAt_const 1
  apply HasLimAt_replacement_rule l1
  exact id_pre

lemma my_deriv_id : my_deriv (fun x => x) c = 1 := by
  rw [my_deriv]
  set f := fun x => (x - c) / (x - c)
  set g := fun (_ : ℝ) => (1 : ℝ)
  have l1 : HasLimAt g c := HasLimAt_const 1
  rw [lim_replacement_rule_fin_fin l1]
  . exact lim_const 1
  . exact id_pre
