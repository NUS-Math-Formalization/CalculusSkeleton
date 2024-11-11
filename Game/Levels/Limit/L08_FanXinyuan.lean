import Game.Metadata
import Mathlib
import Game.Lemmas.Limits.Basic

World "Limit"

Level 8


-- use the ε, δ definition to prove that lim_{x → 1} frac {2x^2 + 3x - 2}{ x+2} =1
open BigOperators

lemma factorExp (x: ℝ): (2*x^2 + 3*x - 2) / (x+2)=(2*x-1)*(x+2)/ (x+2) :=by
  ring
lemma factorCancel (x: ℝ) (h0: x+2 ≠ 0): (2*x-1)*(x+2)/ (x+2) = 2*x-1 :=by
  exact (eq_div_of_mul_eq h0 rfl).symm

--|2*x-1-1|(h0: x+2 ≠ 0)
-- use the ε, δ definition to prove that lim_{x → 1} frac {2x^2 + 3x - 2}{ x+2} =1
Statement : lim x → 1,  (2*x^2 + 3*x - 2)/(x+2) = 1 := by
/-Statement : (h0: x+2 ≠ 0) tendsto (λ x, (2 * x ^ 2 + 3 * x - 2) / (x + 2)) (𝓝 1) (𝓝 1) := by-/
  apply lim_def_fin_fin
  intro ε hε
  use ε/2
  constructor
  linarith
  intro x hx
  have h1 (x:ℝ):|(2 * x ^ 2 + 3 * x - 2) / (x + 2) - 1|=|(2*x-1)*(x+2)/ (x+2)-1| := by ring_nf
  sorry


/-   |(2 * x ^ 2 + 3 * x - 2) / (x + 2) - 1|
    _=|(2*x-1)*(x+2)/ (x+2)-1| := by {rw[factorExp]}
    _=|(2*x-1)-1|:= by {rw[factorCancel]}
    _=|2*x-2|:=by {simp}
    _=|2*(x-1)|:=by {rw[← mul_sub]}
    _=|2|*|x-1|:=by {rw[abs_mul]}
    _=2*|x-1|:=by {rw[abs_two]}
    _ < ε := by linarith-/




  --have h1: ∀(x:ℝ), 2*x^2 + 3*x - 2 = (2*x-1)*(x+2) := by
    --simp_rw[(mul_add), (sub_mul)]
    --ring
    --exact --?
  --have h2: ∀(x:ℝ), (2*x^2 + 3*x - 2) / (x+2)  = (2*x-1) := by
    --rw[h1]
    --simp

NewTactic ring_nf
