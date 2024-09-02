import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 6

Title "FTC test"

Statement (a b: ℝ) (f g g': ℝ → ℝ) (hf : Continuous f) (hg : HasDerivAt g (g' b) b):
  deriv (fun (u : ℝ) => ∫ (x : ℝ) in a..(g u), f x) b = f (g b) * (g' b) := by
  set h := (fun (u : ℝ) => ∫ (x : ℝ) in a..u, f x)
  have : (fun (u : ℝ) => ∫ (x : ℝ) in a..(g u), f x) = h ∘ g := by rfl
  rw [this]
  rw [deriv.comp]
  rw [Continuous.deriv_integral]
  simp only [mul_eq_mul_left_iff]
  left
  exact HasDerivAt.deriv hg
  exact hf
  apply differentiableWithinAt_univ.mp
  apply intervalIntegral.differentiableOn_integral_of_continuous
  intro x hx
  apply Continuous.intervalIntegrable
  exact hf
  exact hf
  trivial
  exact HasDerivAt.differentiableAt hg
