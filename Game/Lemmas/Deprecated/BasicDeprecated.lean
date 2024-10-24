import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
-- import Mathlib.Algebra.Order.Group.Abs
-- import Mathlib.Order.Filter.Basic
import Mathlib.Data.ENNReal.Basic
-- import Mathlib.Logic.Basic
open Filter Set
open Classical


noncomputable section LimDef

def HasLimAt (f : ℝ → ℝ) (c : ℝ) := ∃ l₂, Tendsto f (nhds c) l₂

def HasLimAtTop (f : ℝ → ℝ) := ∃ l₂, Tendsto f atTop l₂

irreducible_def flim (f : ℝ → ℝ) (l₁ : Filter ℝ) : ℝ :=
  if h : ∃ L, Tendsto f l₁ (nhds L) then h.choose else 0

-- irreducible_def flim

-- syntax "lim " term:40 " → ∞, " term:70: term
-- syntax "lim " term:40 " → " term:10 ", " term:70 " = ∞": term
-- syntax "lim " term:40 " → ∞, " term:70 " = ∞": term

-- macro_rules
--   | `(lim $x → ∞, $r = ∞) => `(Tendsto (fun $x => $r) atTop atTop)
--   | `(lim $x → $c, $r) => `(flim (fun $x => $r) (nhds $c))
--   | `(lim $x → ∞, $r) =>  `(flim (fun $x => $r) atTop)
--   | `(lim $x → $c, $r = ∞) => `(Tendsto (fun $x => $r) (nhds $c) atTop)

notation:max "lim " x:40 " → ∞, " r:70 "= ∞" => Tendsto (fun x => r) atTop atTop
notation:max "lim " x:40 " → " c:10 ", " r:70 => flim (fun x => r) (nhds c)
notation:max "lim " x:40 " → ∞, " r:70 => flim (fun x => r) atTop
notation:max "lim " x:40 " → " c:10 ", " r:70 " = ∞" => Tendsto (fun x => r) (nhds c) atTop

variable {c L : ℝ} {f : ℝ → ℝ}

lemma epsilon_delta_nhds_nhds : Tendsto f (nhds c) (nhds L) ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - L| < ε := by
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHB c) (NHB L), mem_setOf_eq]


lemma lim_def_fin_fin (h : ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - L| < ε) :
  lim x → c, f x = L := by
  rw [← epsilon_delta_nhds_nhds] at h
  have hL : ∃ L, Tendsto f (nhds c) (nhds L) := ⟨L, h⟩
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


lemma epsilon_delta_nhds_atTop : Tendsto f (nhds c) atTop ↔
  ∀ N : ℝ, ∃ δ > 0, ∀ x, |x - c| < δ → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHB c) THB, mem_setOf, forall_true_left, mem_Ioi]


lemma lim_def_fin_inf (h : ∀ N : ℝ, ∃ δ > 0, ∀ x, |x - c| < δ → f x > N ) :
  lim x → c, f x = ∞ := epsilon_delta_nhds_atTop.mpr h


lemma epsilon_delta_atTop_atTop : Tendsto f atTop atTop ↔
  ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB THB, true_and, forall_true_left, mem_Ioi]


lemma lim_def_inf_inf (h : ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N) :
  lim x → ∞, f x = ∞ := epsilon_delta_atTop_atTop.mpr h

end LimDef
