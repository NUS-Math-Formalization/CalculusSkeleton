import Game.Lemmas.Limits.Basic
open Filter Set

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

def continuous (f : ℝ → ℝ) (c : ℝ) := lim x → c, f x = f c

lemma lim_comp (h₁ : continuous f₂ c) (h₂ : HasLimAt f₁ c) :
  lim x → c, (f₂ ∘ f₁) x = f₂ (lim x → c, f₁ x) := by sorry

private lemma replacement_rule_pre (hL : HasLimAt f₂ c)
  (hf₁f₂ : ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → f₁ x = f₂ x) :
  Tendsto (fun x => (f₁ - f₂) x) (nhdsWithin c {c}ᶜ) (nhds 0) := by
  rcases hL with ⟨L, hL1⟩
  rw [epsilon_delta_nhds_nhds_deleted]
  intro ε epos
  rcases hf₁f₂ with ⟨δ1, h2, h3⟩
  rw [epsilon_delta_nhds_nhds_deleted] at hL1
  rcases hL1 ε epos with ⟨δ2, h5, _⟩
  use min δ1 δ2
  constructor
  . exact lt_min h2 h5
  . intro _ h6
    simp only [Pi.sub_apply, sub_zero]
    rw [h3]
    simp only [sub_self, abs_zero]
    exact epos
    constructor
    . exact h6.left
    . exact lt_of_lt_of_le h6.right (min_le_left δ1 δ2)

lemma HasLimAt_replacement_rule (hL : HasLimAt f₂ c)
  (hf₁f₂ : ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → f₁ x = f₂ x) : HasLimAt f₁ c := by
  rw [HasLimAt] at *
  rcases hL with ⟨L, hL1⟩
  use L
  have l1 : Tendsto (fun x => (f₁ - f₂) x) (nhdsWithin c {c}ᶜ) (nhds 0) := by
    apply replacement_rule_pre _ hf₁f₂
    rw [HasLimAt]
    use L
  have l2 : f₁ = (f₁ - f₂) + f₂ := by exact (sub_add_cancel f₁ f₂).symm
  rw [l2, ← zero_add L]
  apply Filter.Tendsto.add
  exact l1; exact hL1

lemma lim_replacement_rule_fin_fin (hL : HasLimAt f₂ c)
  (hf₁f₂ : ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → f₁ x = f₂ x) :
  lim x → c, f₁ x = lim x → c, f₂ x := by
  have l1 := replacement_rule_pre hL hf₁f₂
  have l2 : lim x → c, (f₁ - f₂) x = 0 := by
    apply lim_def_fin_fin
    exact (epsilon_delta_nhds_nhds_deleted (f₁ - f₂) c 0).mp l1
  have : (fun x => f₁ x) = (fun x => (f₁ - f₂) x + f₂ x) := (add_eq_of_eq_sub rfl).symm
  have l3 : lim x → c, f₁ x = lim x → c, (f₁ - f₂) x + lim x → c, f₂ x := by
    nth_rw 1 [this]
    rw [lim_add]
    . use 0
    . exact hL
  rw [l3, l2, zero_add]

-- work on other cases for replacement rules...
end Computation
