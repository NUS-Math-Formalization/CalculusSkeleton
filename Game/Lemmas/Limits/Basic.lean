import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
-- import Mathlib.Algebra.Order.Group.Abs
-- import Mathlib.Order.Filter.Basic
import Mathlib.Data.ENNReal.Basic
open Filter Set Classical

noncomputable section LimDef

def HasLimAt (f : ℝ → ℝ) (c : ℝ) := ∃ (l₂ : ℝ), Tendsto f (nhdsWithin c {c}ᶜ) (nhds l₂)

def HasLimAtTop (f : ℝ → ℝ) := ∃ (l₂ : ℝ), Tendsto f atTop (nhds l₂)

irreducible_def flim (f : ℝ → ℝ) (l₁ : Filter ℝ) : ℝ :=
  if h : ∃ L, Tendsto f l₁ (nhds L) then h.choose else 0

-- irreducible_def flim
syntax "lim " term:40 " → " term:10 ", " term:70: term
syntax "lim " term:40 " → ∞, " term:70: term
syntax "lim " term:40 " → " term:10 ", " term:70 " = ∞": term
syntax "lim " term:40 " → ∞, " term:70 " = ∞": term

macro_rules
  | `(lim $x → ∞, $r = ∞) => `(Tendsto (fun $x => $r) atTop atTop)
  | `(lim $x → $c, $r) => `(flim (fun $x => $r) (nhdsWithin $c {($c)}ᶜ))
  | `(lim $x → ∞, $r) =>  `(flim (fun $x => $r) atTop)
  | `(lim $x → $c, $r = ∞) => `(Tendsto (fun $x => $r) (nhdsWithin $c {($c)}ᶜ) atTop)


variable {c L : ℝ} {f : ℝ → ℝ}

lemma nhds_basis_abs_sub_lt_deleted (a : ℝ) :
    (nhdsWithin a {a}ᶜ).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { b | 0 < |b - a| ∧ |b - a| < ε }
    := by
  have : (fun ε => { b | 0 < |b - a| ∧ |b - a| < ε }) = (fun ε => {b | |b - a| < ε} ∩ {a}ᶜ) := by
    funext ε
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_compl_iff, mem_singleton_iff, abs_pos, ne_eq]
    rw [and_comm]
    simp only [and_congr_right_iff]
    intro
    exact sub_ne_zero
  rw [this]
  apply nhdsWithin_hasBasis (nhds_basis_abs_sub_lt (α := ℝ) a) ({a}ᶜ)


lemma epsilon_delta_nhds_nhds_deleted (f : ℝ → ℝ) (c L : ℝ) :
  Tendsto f (nhdsWithin c {c}ᶜ) (nhds L) ↔
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


lemma epsilon_delta_atTop_atTop : Tendsto f atTop atTop ↔
  ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB THB, true_and, forall_true_left, mem_Ioi]


lemma lim_def_inf_inf (h : ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N) :
  lim x → ∞, f x = ∞ := epsilon_delta_atTop_atTop.mpr h

end LimDef

-- there's still one-sided limits to handle lol
-- use the following notations, again need punctured neighbourhoods
-- `𝓝[<] x`: the filter `nhdsWithin x (Set.Iio x)` of punctured left-neighborhoods of `x`;
-- `𝓝[>] x`: the filter `nhdsWithin x (Set.Ioi x)` of punctured right-neighborhoods of `x`;
