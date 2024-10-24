import Game.Lemmas.Limits.Basic
open Filter Set Topology

section Computation

variable {f f₁ f₂ : ℝ → ℝ}

-- first, we deal with the relationship between one-sided limits and two-sided limits.
lemma epsDeltaLeftLimIfLim (L : ℝ) (h: ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ), 0 < |x - c| ∧ |x - c| < δ → |f x - L| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ), 0 < c - x ∧ c - x < δ → |f x - L| < ε := by
  intro ε εpos
  obtain ⟨δ, δpos, hδ⟩ := h ε εpos
  use δ
  refine And.intro δpos ?_
  refine fun x ⟨hx1, hx2⟩ ↦ hδ x ?_
  rw [abs_sub_comm]
  refine And.intro (abs_pos_of_pos hx1) ?_
  refine abs_lt.mpr (And.intro ?_ ?_) <;> linarith

lemma HasLimAt_imp_HasLeftLimAt (h : HasLimAt f c) : HasLeftLimAt f c := by
  rcases h with ⟨l, hl⟩
  use l
  rw [epsilon_delta_nhds_nhds_deleted] at hl
  rw [epsilon_delta_nhds_nhds_left]
  exact epsDeltaLeftLimIfLim _ hl

lemma HasLimAt_imp_HasLeftLimAt' (h₁ : HasLimAt f c) (h₂ : lim x → c, f x = L) :
  lim x → c⁻, f x = L := by
  rcases h₁ with ⟨l, hl⟩
  have hl' := epsilon_delta_nhds_nhds_deleted.mp hl
  have hl'' := lim_def_fin_fin hl'
  rw [← hl'', h₂] at hl'
  apply left_lim_def_fin_fin
  exact epsDeltaLeftLimIfLim _ hl'

-- the following are similar
lemma epsDeltaRightLimIfLim (L : ℝ) (h: ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ), 0 < |x - c| ∧ |x - c| < δ → |f x - L| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ), 0 < x - c ∧ x - c < δ → |f x - L| < ε := by
  intro ε εpos
  obtain ⟨δ, δpos, hδ⟩ := h ε εpos
  use δ
  refine And.intro δpos ?_
  refine fun x ⟨hx1, hx2⟩ ↦ hδ x ?_
  refine And.intro (abs_pos_of_pos hx1) ?_
  refine abs_lt.mpr (And.intro ?_ ?_) <;> linarith

lemma HasLimAt_imp_HasRightLimAt (h : HasLimAt f c) : HasRightLimAt f c := by
  rcases h with ⟨l, hl⟩
  use l
  rw [epsilon_delta_nhds_nhds_deleted] at hl
  rw [epsilon_delta_nhds_nhds_right]
  exact epsDeltaRightLimIfLim _ hl

lemma HasLimAt_imp_HasRightLimAt' (h₁ : HasLimAt f c) (h₂ : lim x → c, f x = L) :
  lim x → c⁺, f x = L := by sorry


lemma left_lim_eq_right_lim (h₁ : HasLeftLimAt f c) (h₂ : HasRightLimAt f c) :
  (lim x → c⁻, f x = lim x → c⁺, f x) ↔ HasLimAt f c := by
  rcases h₁ with ⟨l₁, l₁h⟩
  rcases h₂ with ⟨l₂, l₂h⟩
  apply epsilon_delta_nhds_nhds_left.mp at l₁h
  apply epsilon_delta_nhds_nhds_right.mp at l₂h
  refine Iff.intro ?_ ?_
  . refine fun h ↦ ⟨l₂, ?_⟩
    rw [epsilon_delta_nhds_nhds_deleted]
    intro ε εpos
    obtain ⟨δ₁, δ₁h₁, δ₁h₂⟩ := l₁h ε εpos
    obtain ⟨δ₂, δ₂h₁, δ₂h₂⟩ := l₂h ε εpos
    refine ⟨min δ₁ δ₂, And.intro (lt_min δ₁h₁ δ₂h₁) (fun x ⟨h', h''⟩ ↦ ?_)⟩
    rw [←(left_lim_def_fin_fin l₁h), h, right_lim_def_fin_fin l₂h] at δ₁h₂
    cases lt_abs.mp h'
    . refine δ₂h₂ _ (And.intro h_1 ?_)
      exact lt_of_abs_lt (by linarith [min_le_right δ₁ δ₂])
    . refine δ₁h₂ _ (And.intro (by linarith) ?_)
      have : |x - c| < δ₁ := by linarith [min_le_left δ₁ δ₂]
      rw [abs_sub_comm] at this
      exact lt_of_abs_lt this
  . intro h
    let ⟨l₃, l₃h⟩ := h
    have lim_l₃ := lim_def_fin_fin (epsilon_delta_nhds_nhds_deleted.mp l₃h)
    rw [HasLimAt_imp_HasLeftLimAt' h lim_l₃, HasLimAt_imp_HasRightLimAt' h lim_l₃]

-- one direction is similar to above, the other direction is easy.
lemma left_lim_eq_right_lim' (h₁ : HasLeftLimAt f c) (h₂ : HasRightLimAt f c) (h₃ : HasLimAt f c):
  (lim x → c⁻, f x = L ∧ lim x → c⁺, f x = L) ↔ lim x → c, f x = L := by sorry


-- then subsequently we can just prove the one-sided version to imply the two-sided version
-- example:

lemma HasLeftLimAt_const (d : ℝ) : HasLeftLimAt (fun x => d) c := by
  simp only [HasLeftLimAt]
  use d
  exact tendsto_const_nhds

lemma HasRightLimAt_const (d : ℝ) : HasRightLimAt (fun x => d) c := sorry

lemma leftlim_const (d : ℝ) : lim x → c⁻, d = d := by
  apply left_lim_def_fin_fin
  rw [← epsilon_delta_nhds_nhds_left]
  exact tendsto_const_nhds

lemma rightlim_const (d : ℝ) : lim x → c⁺, d = d := by sorry

lemma HasLimAt_const (d : ℝ) : HasLimAt (fun x => d) c := by
  apply (left_lim_eq_right_lim (HasLeftLimAt_const d) (HasRightLimAt_const d)).mp
  have left := @leftlim_const c d
  have right := @rightlim_const c d
  rw [left, right]

lemma lim_const (d : ℝ) : lim x → c, d = d := (left_lim_eq_right_lim' (HasLeftLimAt_const d)
  (HasRightLimAt_const d) (HasLimAt_const d)).mp (And.intro (leftlim_const d) (rightlim_const d))

lemma HasLimAt_id : HasLimAt (fun x => x) c := sorry

lemma HasLimAt_add (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) :
  HasLimAt (fun x => f₁ x + f₂ x) c := sorry

lemma HasLimAt_mul (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) :
  HasLimAt (fun x => f₁ x * f₂ x) c := sorry

lemma HasLimAt_pow (k : ℕ) (h : HasLimAt f c) : HasLimAt (fun x => (f₁ x) ^ k) c := sorry

lemma HasLimAt_mul_const (m : ℝ) (h : HasLimAt f c) :
  HasLimAt (fun x => m * x) c := sorry


lemma lim_mul_const (m : ℝ) (h : HasLimAt f c) :
  lim x → c, m * f x = m * lim x → c, f x := sorry

lemma lim_id : lim x → c, x = c := by sorry

lemma lim_add (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) :
  lim x → c, (f₁ x + f₂ x) = lim x → c, f₁ x + lim x → c, f₂ x := by sorry

lemma lim_sub (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) :
  lim x → c, (f₁ x - f₂ x) = lim x → c, f₁ x - lim x → c, f₂ x := by sorry

lemma lim_div (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c)
  (h₀ : lim x → c, f₂ x ≠ 0) :
  lim x → c, (f₁ x / f₂ x) = (lim x → c, f₁ x) / (lim x → c, f₂ x) := by sorry

lemma lim_mul (h₁ : HasLimAt f₁ c) (h₂ : HasLimAt f₂ c) :
  lim x → c, (f₁ x * f₂ x) = (lim x → c, f₁ x) * (lim x → c, f₂ x) := by sorry

lemma lim_pow (k : ℕ) (h : HasLimAt f c) :
  lim x → c, (f x) ^ k = (lim x → c, f x) ^ k := by sorry

-- some kind soul pls formalize the one-sided limit statements...
lemma leftlim_mul_const (m : ℝ) (h : HasLeftLimAt f c) :
  lim x → c⁻, m * f x = m * lim x → c⁻, f x := sorry

lemma leftlim_id : lim x → c⁻, x = c := by sorry

lemma leftlim_add (h₁ : HasLeftLimAt f₁ c) (h₂ : HasLeftLimAt f₂ c) :
  lim x → c⁻, (f₁ x + f₂ x) = lim x → c⁻, f₁ x + lim x → c⁻, f₂ x := by sorry

lemma leftlim_sub (h₁ : HasLeftLimAt f₁ c) (h₂ : HasLeftLimAt f₂ c) :
  lim x → c⁻, (f₁ x - f₂ x) = lim x → c⁻, f₁ x - lim x → c⁻, f₂ x := by sorry

lemma leftlim_div (h₁ : HasLeftLimAt f₁ c) (h₂ : HasLeftLimAt f₂ c)
  (h₀ : lim x → c⁻, f₂ x ≠ 0) :
  lim x → c⁻, (f₁ x / f₂ x) = (lim x → c⁻, f₁ x) / (lim x → c⁻, f₂ x) := by sorry

lemma leftlim_mul (h₁ : HasLeftLimAt f₁ c) (h₂ : HasLeftLimAt f₂ c) :
  lim x → c⁻, (f₁ x * f₂ x) = (lim x → c⁻, f₁ x) * (lim x → c⁻, f₂ x) := by sorry

lemma leftlim_pow (k : ℕ) (h : HasLeftLimAt f c) :
  lim x → c⁻, (f x) ^ k = (lim x → c⁻, f x) ^ k := by sorry

def continuous (f : ℝ → ℝ) (c : ℝ) := lim x → c, f x = f c

lemma lim_comp (h₁ : continuous f₂ c) (h₂ : HasLimAt f₁ c) :
  lim x → c, (f₂ ∘ f₁) x = f₂ (lim x → c, f₁ x) := by sorry


-- finally we deal with replacement rules
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
    exact (epsilon_delta_nhds_nhds_deleted).mp l1
  have : (fun x => f₁ x) = (fun x => (f₁ - f₂) x + f₂ x) := (add_eq_of_eq_sub rfl).symm
  have l3 : lim x → c, f₁ x = lim x → c, (f₁ - f₂) x + lim x → c, f₂ x := by
    nth_rw 1 [this]
    rw [lim_add]
    . use 0
    . exact hL
  rw [l3, l2, zero_add]

-- work on other cases for replacement rules...

end Computation
