import Game.Metadata
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

World "DemoWorld"
Level 3

Title "Hello World 3"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides. bhhjfsdlkjsfd"

-- Statement : Tendsto (fun x : ℝ ↦ x + 1) (nhds 6) (nhds 7) := by sorry

example : Filter.Tendsto (fun x : ℝ ↦ x + 1) (nhds 6) (nhds 7) :=  by
  refine Continuous.tendsto' ?hf 6 7 ?h
  . exact continuous_add_right 1
  . norm_num

example : deriv (fun x : ℝ ↦ x ^ 5 + x - 1) 6 = 5 * 6 ^ 4 + 1 := by field_simp
