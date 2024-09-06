import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 5

Title "exp to the exp"

-- the following are proven in level 4, so this level is just an application of chain rule
lemma deriv_xexpx (x : ℝ) :
  deriv (fun x => x * Real.exp x) (x : ℝ) = (x + 1) * Real.exp x := by sorry

lemma xexpx_differentiable (x : ℝ) : DifferentiableAt ℝ (fun x => x * Real.exp x) x := by sorry

Statement (x : ℝ) : deriv (fun x => Real.exp x ^ Real.exp x) (x : ℝ)
  = (Real.exp (x + x * Real.exp x)) * (x + 1) := by
  -- need some hints to guide students to define g and prove a lemma as follows.
  simp_rw [← Real.exp_mul]
  set g := fun x => x * Real.exp x
  have : (fun x => Real.exp (x * Real.exp x)) = Real.exp ∘ g := rfl
  rw [this]
  rw [deriv.comp]
  rw [Real.deriv_exp]
  rw [deriv_xexpx]
  rw [mul_comm (x + 1) (Real.exp x)]
  rw [← mul_assoc]
  rw [mul_comm (Real.exp (g x))]
  rw [Real.exp_add]

  exact Real.differentiableAt_exp
  exact xexpx_differentiable x


/-- The function $f(x) = xe^x$ is differentiable everywhere on $ℝ$ -/
TheoremDoc xexpx_differentiable as "xexpx_differentiable" in "Derivative"

/-- $(xe^x)'=(x + 1)e^x$ -/
TheoremDoc deriv_xexpx as "deriv_xexpx" in "Derivative"

/-- Chain Rule: $(f ∘ g)'(x)=f'(g(x))g'(x)$ -/
TheoremDoc deriv.comp as "deriv.comp" in "Derivative"

-- for some reasons i cannot put have as a new tactic lul
NewTactic set rfl

NewTheorem xexpx_differentiable deriv_xexpx deriv.comp
