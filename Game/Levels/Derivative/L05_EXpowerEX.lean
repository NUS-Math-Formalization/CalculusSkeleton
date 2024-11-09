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
  Hint "To solve the goal involving the derivative of an exponential function, use `simp_rw [Real.exp_mul]` to rewrite the expression. This will help transform $ \\exp(x) ^ \\exp(x) $ into $ \\exp(x \\cdot \\exp(x)) $, making it easier to differentiate."
  simp_rw [← Real.exp_mul]
  Hint "Introduce a new function `g` defined as `g(x) = x * Real.exp x`. This will help simplify the expression for the derivative by allowing us to focus on `Real.exp (g(x))`. This step is setting up the problem for easier manipulation and differentiation."
  set g := fun x => x * Real.exp x
  Hint "Introduce an auxiliary fact using `have` to recognize that the function $ \\exp(x \\cdot \\exp(x)) $ can be expressed as the composition $ \\exp \\circ g $, where $ g(x) = x \\cdot \\exp(x) $. This simplification can help clarify the structure of the function for differentiation."
  have : (fun x => Real.exp (x * Real.exp x)) = Real.exp ∘ g := rfl
  rw [this]
  Hint "To tackle the goal involving the derivative of a composition of functions, use `rw [deriv.comp]`. This will apply the chain rule, allowing you to express the derivative of the composition as the product of the derivative of the outer function evaluated at the inner function and the derivative of the inner function itself."
  rw [deriv.comp]
  rw [Real.deriv_exp]
  rw [deriv_xexpx]
  Hint "Apply the rewrite rule `mul_comm` to swap the multiplication order in the expression $((x + 1) \\cdot \\exp(x))$. This will help align the left-hand side of the equation with the right-hand side by changing it to $(\\exp(x) \\cdot (x + 1))$."
  rw [mul_comm (x + 1) (Real.exp x)]
  rw [← mul_assoc]
  Hint "To simplify the expression on the left-hand side of the equation, use the `rw [mul_comm]` tactic. This tactic applies the commutative property of multiplication to reorder the terms, swapping `Real.exp (g x)` and `Real.exp x`."
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
