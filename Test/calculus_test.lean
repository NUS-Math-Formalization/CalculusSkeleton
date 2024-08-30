import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
-- import Mathlib.Algebra.Order.Group.Abs
-- import Mathlib.Order.Filter.Basic
import Mathlib.Data.ENNReal.Basic
open Filter Set

example : Filter.Tendsto (fun (x : ENNReal) => 2 * x) (nhds 0) (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rw [eventually_nhds_iff]
  use Set.Ico 0 (ε/2)
  constructor;
  · simp; intro x hx;
    calc
      2 * x ≤ 2 * ε/2 := by
        rw [mul_div_assoc]
        rw [ENNReal.mul_le_mul_left];
        · exact le_of_lt hx
        simp; simp
      _ = ε := by 
        rw [mul_comm, ENNReal.mul_div_right_comm, ENNReal.div_mul_cancel]; 
        simp; simp;
  
  . constructor
    · exact ENNReal.isOpen_Ico_zero
    · rw [Set.left_mem_Ico];
      simp; 
      exact ne_of_gt hε.gt

-- open Batteries.ExtendedBinder Lean Meta

def limit (c : ℝ) (f : ℝ → ℝ) : Option EReal := sorry


syntax (name := limit') "lim " term:40 " → " term:10 ", " term:70 " = " term:12 : term
macro_rules (kind := limit')
  | `(lim $x → $c, $r = $L) => `(Tendsto (fun ($x : ℝ) => ($r : ℝ)) (nhds $c) (nhds $L))


-- #check lim x → 0, (x + 1) = 1


def HasLimit (f : ℝ → ℝ) (c L : ℝ) := Tendsto f (nhds c) (nhds L) 

open Classical
noncomputable def limit'' (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  if h : ∃ L, HasLimit f c L then Classical.choose h else 0

lemma epsilon_delta_nhds_nhds (f : ℝ → ℝ) (c L : ℝ) : 
  Tendsto f (nhds c) (nhds L) ↔ 
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - L| < ε := by
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHB c) (NHB L), mem_setOf_eq]


lemma epsilon_delta_atTop_nhds (f : ℝ → ℝ) (L : ℝ) :
  Tendsto f atTop (nhds L) ↔
  ∀ ε > 0, ∃ N, ∀ x, x > N → |f x - L| < ε := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB (NHB L), mem_Ioi, true_and, mem_setOf_eq]


lemma epsilon_delta_nhds_atTop (f : ℝ → ℝ) (c : ℝ) :
  Filter.Tendsto f (nhds c) atTop ↔ 
  ∀ N : ℝ, ∃ δ > 0, ∀ x, |x - c| < δ → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHB c) THB, mem_setOf, forall_true_left, mem_Ioi]


lemma epsilon_delta_atTop_atTop (f : ℝ → ℝ) :
  Filter.Tendsto f atTop atTop ↔
  ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB THB, true_and, forall_true_left, mem_Ioi]


/-- Notation rewrite -/
example : lim x → 0, 2 * x = 0 := by
  simp [epsilon_delta_nhds_nhds]
  intro ε hε
  use ε / 2
  constructor;
  · linarith
  · intro x hx;
    calc
      _ = 2 * |x| := by rw [abs_mul, abs_two]
      _ < ε := by linarith 


