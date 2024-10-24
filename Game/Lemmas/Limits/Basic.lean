import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.ENNReal.Basic

open Filter Set Classical Topology

noncomputable section LimDef

-- to fix: change to functions defined on intervals
def HasLimAt (f : ℝ → ℝ) (c : ℝ) := ∃ (l₂ : ℝ), Tendsto f (nhdsWithin c {c}ᶜ) (nhds l₂)

def HasLeftLimAt (f : ℝ → ℝ) (c : ℝ) := ∃ (l₂ : ℝ), Tendsto f (nhdsWithin c (Set.Iio c)) (nhds l₂)

def HasRightLimAt (f : ℝ → ℝ) (c : ℝ) := ∃ (l₂ : ℝ), Tendsto f (nhdsWithin c (Set.Ioi c)) (nhds l₂)

def HasLimAtTop (f : ℝ → ℝ) := ∃ (l₂ : ℝ), Tendsto f atTop (nhds l₂)

-- add HasLimAtBot

irreducible_def flim (f : ℝ → ℝ) (l₁ : Filter ℝ) : ℝ :=
  if h : ∃ L, Tendsto f l₁ (nhds L) then h.choose else 0

notation:max "lim " x:40 " → ∞, " r:70 "= ∞" =>
  Tendsto (fun x => r) atTop atTop
notation:max "lim " x:40 " → " c:10 ", " r:70 =>
  flim (fun x => r) (𝓝[≠] c)
notation:max "lim " x:40 " → ∞, " r:70 =>
  flim (fun x => r) atTop
notation:max "lim " x:40 " → " c:10 ", " r:70 " = ∞" =>
  Tendsto (fun x => r) (𝓝[≠] c) atTop
notation:max "lim " x:40 " → " c:10 "⁺, " r:70 =>
  flim (fun x => r) (𝓝[>] c)
notation:max "lim " x:40 " → " c:10 "⁻, " r:70 =>
  flim (fun x => r) (𝓝[<] c)
notation:max "lim " x:40 " → " c:10 "⁺, " r:70 " = ∞" =>
  Tendsto (fun x => r) (𝓝[<] c) atTop
notation:max "lim " x:40 " → " c:10 "⁻, " r:70 " = ∞" =>
  Tendsto (fun x => r) (𝓝[>] c) atTop


variable {c L : ℝ} {f : ℝ → ℝ}

lemma nhds_basis_abs_sub_lt_deleted (a : ℝ) :
    (nhdsWithin a {a}ᶜ).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { b | 0 < |b - a| ∧ |b - a| < ε }
    := by
  have : (fun ε => { b | 0 < |b - a| ∧ |b - a| < ε }) = (fun ε => {b | |b - a| < ε} ∩ {a}ᶜ) := by
    funext ε; ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_compl_iff, mem_singleton_iff, abs_pos, ne_eq]
    rw [and_comm]
    simp only [and_congr_right_iff]
    intro
    exact sub_ne_zero
  rw [this]
  apply nhdsWithin_hasBasis (nhds_basis_abs_sub_lt (α := ℝ) a) ({a}ᶜ)


lemma epsilon_delta_nhds_nhds_deleted : Tendsto f (nhdsWithin c {c}ᶜ) (nhds L) ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → |f x - L| < ε := by
  have NHBD := nhds_basis_abs_sub_lt_deleted c
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHBD) (NHB L), mem_setOf_eq]


lemma lim_def_fin_fin (h : ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → |f x - L| < ε) :
  lim x → c, f x = L := by
  rw [← epsilon_delta_nhds_nhds_deleted] at h
  have hL : ∃ L, Tendsto f (nhdsWithin c {c}ᶜ) (nhds L) := ⟨L, h⟩
  rw [flim, dif_pos hL]
  exact tendsto_nhds_unique hL.choose_spec h


lemma epsilon_delta_nhds_nhds_left : Tendsto f (nhdsWithin c (Set.Iio c)) (nhds L) ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < c - x ∧ c - x < δ → |f x - L| < ε := by
  have : ∃ b, b < c := by use (c - 1); norm_num
  have NHBL := nhdsWithin_Iio_basis' (α := ℝ) this
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHBL) (NHB L), mem_setOf]
  simp only [mem_Ioo, and_imp, gt_iff_lt, sub_pos]
  constructor
  . intro h ε εpos
    have : ∃ ia < c, ∀ x, ia < x → x < c → |f x - L| < ε := by apply h; exact εpos
    rcases this with ⟨ia, iapos, iah⟩
    use (c - ia)
    constructor
    . linarith
    . intro h₁ h₂ h₃
      apply iah; linarith; linarith
  . intro h ε εpos
    have : ∃ δ, 0 < δ ∧ (∀ x, x < c → c - x < δ → |f x - L| < ε) := by apply h; exact εpos
    rcases this with ⟨δ, δpos, δh⟩
    use (c - δ)
    constructor
    . linarith
    . intro u u₁ u₂
      apply δh; linarith; linarith


lemma left_lim_def_fin_fin (h : ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < c - x ∧ c - x < δ → |f x - L| < ε) :
  lim x → c⁻, f x = L := by
  rw [← epsilon_delta_nhds_nhds_left] at h
  have hL : ∃ L, Tendsto f (nhdsWithin c (Set.Iio c)) (nhds L) := ⟨L, h⟩
  rw [flim, dif_pos hL]
  exact tendsto_nhds_unique hL.choose_spec h


lemma epsilon_delta_nhds_nhds_right : Tendsto f (nhdsWithin c (Set.Ioi c)) (nhds L) ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < x - c ∧ x - c < δ → |f x - L| < ε := by sorry


lemma right_lim_def_fin_fin (h : ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < x - c ∧ x - c < δ → |f x - L| < ε) :
  lim x → c⁺, f x = L := by sorry


lemma epsilon_delta_atTop_nhds : Tendsto f atTop (nhds L) ↔
  ∀ ε > 0, ∃ N, ∀ x, x > N → |f x - L| < ε := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB (NHB L), mem_Ioi, true_and, mem_setOf_eq]


lemma lim_def_inf_fin (h : ∀ ε > 0, ∃ N, ∀ x, x > N → |f x - L| < ε) :
  lim x → ∞, f x = L := by
  rw [← epsilon_delta_atTop_nhds] at h
  have hL : ∃ L, Tendsto f atTop (nhds L) := ⟨L, h⟩
  rw [flim, dif_pos hL]
  exact tendsto_nhds_unique hL.choose_spec h


lemma epsilon_delta_nhds_atTop_deleted : Tendsto f (nhdsWithin c {c}ᶜ) atTop ↔
  ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHBD := nhds_basis_abs_sub_lt_deleted c
  simp_rw [HasBasis.tendsto_iff NHBD THB, mem_setOf, forall_true_left, mem_Ioi]


lemma lim_def_fin_inf (h : ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → f x > N ) :
  lim x → c, f x = ∞ := epsilon_delta_nhds_atTop_deleted.mpr h


lemma epsilon_delta_nhds_atTop_left : Tendsto f (nhdsWithin c (Set.Iio c)) atTop ↔
  ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < c - x ∧ c - x < δ → f x > N := by sorry

-- Clarence: I think this should be flipped and iff'ed
lemma left_lim_def_fin_inf (h : ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < c - x ∧ c - x < δ → f x > N) :
  lim x → c⁻, f x = ∞ := by sorry


lemma epsilon_delta_nhds_atTop_right : Tendsto f (nhdsWithin c (Set.Ioi c)) atTop ↔
  ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < x - c ∧ x - c < δ → f x > N := by sorry


lemma right_lim_def_fin_inf (h : ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < x - c ∧ x - c < δ → f x > N) :
  lim x → c⁺, f x = ∞ := by sorry


lemma epsilon_delta_atTop_atTop : Tendsto f atTop atTop ↔
  ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB THB, true_and, forall_true_left, mem_Ioi]


lemma lim_def_inf_inf (h : ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N) :
  lim x → ∞, f x = ∞ := epsilon_delta_atTop_atTop.mpr h

end LimDef
