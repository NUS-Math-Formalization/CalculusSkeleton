import Game.Metadata

World "Derivative"

Level 11

Title "The derivative of (x - 1)^4 / (x^2 + 2x)^5"

-- Introduction "This level is about finding the derivative of the function $\\frac\\{(x-1)^4}\\{(x^2+2x)^5}$. This level is done by Daniel Low."
Introduction "This level is about finding the derivative of the function $(x - 1) ^ 4 / (x^2 + 2x) ^ 5$. This level is done by Daniel Low."

lemma differentiableAt_g₂ (x : ℝ): DifferentiableAt ℝ (fun x : ℝ  => x^2 + 2*x) x := by
  apply DifferentiableAt.add
  exact differentiableAt_pow 2
  apply DifferentiableAt.mul
  exact differentiableAt_const 2
  exact differentiableAt_id


Statement (x : ℝ) (hx1 : (x^2 + 2*x)^5 ≠ 0) :
deriv (fun x : ℝ => (x-1)^4 / (x^2 + 2*x)^5) x
= (4*(x-1)^ 3 * (x^2 + 2*x)^5 - (x - 1)^4 * (5*(x^2 + 2*x)^4 * (2*x + 2))) / ((x^2 + 2*x)^5) ^ 2 := by
  derivit
  differentiability

/-- Chain Rule: $(f ∘ g)'(x)=f'(g(x))g'(x)$ -/
TheoremDoc deriv.comp as "deriv.comp" in "Derivative"

/-- Addition Rule: $(f + g)'(x) = f'(x) + g'(x))$ -/
TheoremDoc DifferentiableAt.add as "DifferentiableAt.add" in "Differentiable"

/-- Product Rule: $(f * g)'(x) = f'(x) * g(x) + g'(x) * f(x))$ -/
TheoremDoc DifferentiableAt.mul as "DifferentiableAt.mul" in "Differentiable"

/-- Product Rule: $(c * g)'(x) =  c * g'(x))$ -/
TheoremDoc DifferentiableAt.const_mul as "DifferentiableAt.const_mul" in "Differentiable"

/-- Differentiable for g₂-/
TheoremDoc differentiableAt_g₂ as "differentiableAt_g₂" in "Differentiable"

NewTheorem differentiableAt_g₂
