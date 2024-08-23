import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
-- import Mathlib.Algebra.Order.Group.Abs
-- import Mathlib.Order.Filter.Basic
import Mathlib.Data.ENNReal.Basic
open Filter

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


lemma epsilon_delta_1 (f : ℝ → ℝ) (c L : ℝ) : 
  Filter.Tendsto f (nhds x) (nhds L) ↔ 
  ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ), |x - c| ≤ δ → |f x - L| ≤ ε := by sorry
