import Game.Lemmas.Limits.Basic
import Game.Lemmas.Limits.LimitLaws
import Game.Lemmas.Derivatives.Basic

-- prove derivatives of different functions here...
-- polynomial, exp, ln, trig, inverse trig. that's all :)

lemma my_has_deriv_id (c : ℝ) : my_has_deriv (fun x => x) c 1 := by
  rw [my_has_deriv]
  set f := fun (x : ℝ) => (x - c) / (x - c)
  set g := fun (_ : ℝ) => (1 : ℝ)
  apply my_limit_replacement_rule_deleted f g
  . exact tendsto_const_nhds
  . use 1
    constructor
    . norm_num
    . intro x hx
      rcases hx with ⟨hx0, _⟩
      apply div_self
      exact abs_pos.mp hx0

lemma my_deriv_id (c : ℝ) : my_deriv (fun x => x) c = 1 := by
  apply my_deriv_eq (fun x => x) c 1
  exact my_has_deriv_id c
