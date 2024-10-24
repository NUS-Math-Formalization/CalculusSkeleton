import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
-- import Mathlib.Algebra.Order.Group.Abs
-- import Mathlib.Order.Filter.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Logic.Basic
open Filter Set
open Classical


noncomputable section LimDef

def HasLimAt (f : ℝ → ℝ) (c : ℝ) := ∃ l₂, Tendsto f (nhds c) l₂

def HasLimAtTop (f : ℝ → ℝ) := ∃ l₂, Tendsto f atTop l₂

irreducible_def flim (f : ℝ → ℝ) (l₁ : Filter ℝ) : ℝ :=
  if h : ∃ L, Tendsto f l₁ (nhds L) then h.choose else 0

-- irreducible_def flim
syntax "lim " term:40 " → " term:10 ", " term:70: term
syntax "lim " term:40 " → ∞, " term:70: term
syntax "lim " term:40 " → " term:10 ", " term:70 " = ∞": term
syntax "lim " term:40 " → ∞, " term:70 " = ∞": term

macro_rules
  | `(lim $x → ∞, $r = ∞) => `(Tendsto (fun $x => $r) atTop atTop)
  | `(lim $x → $c, $r) => `(flim (fun $x => $r) (nhds $c))
  | `(lim $x → ∞, $r) =>  `(flim (fun $x => $r) atTop)
  | `(lim $x → $c, $r = ∞) => `(Tendsto (fun $x => $r) (nhds $c) atTop)


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

-- lemma HasLimAt_const : (HasLimAt)
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


/-- Notation rewrite -/
example : lim x → 0, 2 * x = 0 := by
  apply lim_def_fin_fin
  simp
  intro ε hε
  use ε / 2
  constructor;
  · linarith
  · intro x hx;
    calc
      _ = 2 * |x| := by rw [abs_mul, abs_two]
      _ < ε := by linarith 

/-- Computational proof -/
example : lim x → 0, (x ^ 2 + 3 * x + 1) = 1 := by
  rw [lim_add, lim_add, lim_pow 2, lim_id, lim_mul_const 3, lim_id, lim_const]
  group
  pick_goal 5
  apply HasLimAt_add
  apply HasLimAt_pow (f := fun x => x) 2
  pick_goal 2
  apply HasLimAt_mul_const (f := fun x => x)
  pick_goal 5
  apply HasLimAt_pow (f := fun x => x) 2
  pick_goal 6
  apply HasLimAt_mul_const (f := fun x => x)
  pick_goal 7
  exact HasLimAt_const 1
  all_goals exact HasLimAt_id  
