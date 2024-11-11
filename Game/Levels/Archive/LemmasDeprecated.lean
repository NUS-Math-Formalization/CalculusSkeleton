import Game.Levels.Limit.Basic
import Game.Levels.Limit.Inequalities

open Real

section Computation

variable {f f₁ f₂ : ℝ → ℝ}

lemma HasLimAt_const (d : ℝ) : HasLimAt (fun x => d) c := sorry

lemma HasLimAt_id : HasLimAt (fun x => x) c := sorry


lemma HasLimAt_add (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) :
  HasLimAt (fun x => f₁ x + f₂ x) c := sorry

lemma HasLimAt_mul (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) : 
  HasLimAt (fun x => f₁ x * f₂ x) c := sorry

lemma HasLimAt_pow (k : ℕ) (h : HasLimAt f c) : HasLimAt (fun x => (f₁ x) ^ k) c := sorry

lemma HasLimAt_mul_const (m : ℝ) (h : HasLimAt f c) : 
  HasLimAt (fun x => m * x) c := sorry

lemma lim_const (d : ℝ) : lim x → c, d = d := by sorry

lemma lim_mul_const (m : ℝ) (h : HasLimAt f c) : 
  lim x → c, m * f x = m * lim x → c, f x := sorry

lemma lim_id : lim x → c, x = c := by sorry

lemma lim_add (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) : 
  lim x → c, (f₁ x + f₂ x) = lim x → c, f₁ x + lim x → c, f₂ x := by sorry

lemma lim_sub (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) : 
  lim x → c, (f₁ x - f₂ x) = lim x → c, f₁ x - lim x → c, f₂ x := by sorry

lemma lim_div (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) 
  (h₀ : lim x → c, f₂ x ≠ 0) : 
  lim x → c, (f₁ x + f₂ x) = lim x → c, f₁ x + lim x → c, f₂ x := by sorry

lemma lim_mul (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) : 
  lim x → c, (f₁ x + f₂ x) = lim x → c, f₁ x + lim x → c, f₂ x := by sorry

lemma lim_pow (k : ℕ) (h : HasLimAt f c) : 
  lim x → c, (f x) ^ k = (lim x → c, f x) ^ k := by sorry

end Computation

section L02_Consequence

lemma HasLimAt_two_mul_zero : HasLimAt (fun x => 2 * x) 0 := sorry

lemma HasLimAt_sin_zero : HasLimAt sin 0 := sorry

lemma lim_sin_zero : lim x → 0, sin x = 0 := sorry

lemma lim_two_mul_zero : lim x → 0, 2 * x = 0 := sorry

section L02_Consequence
