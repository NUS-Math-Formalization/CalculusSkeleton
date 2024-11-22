import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 6

Title "Quotient Rule"

Statement (x : ℝ) : deriv (fun x => (Real.sin x) / (x ^ 2 + 1)) (x : ℝ) =
  ((Real.cos x) * (x ^ 2 + 1) - (Real.sin x) * (2 * x)) / (x ^ 2 + 1) ^ 2 := by

  Hint "Our current goal is: $$ ( \\frac\{\\sin x}\{x^2 + 1} )' = \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot 2x }\{ (x^2 + 1)^2 }.$$ To apply the quotient rule, use `deriv_div`"
  rw [deriv_div]

  Hint "Our current goal is: $$ \\frac\{ (\\sin x)' \\cdot (x^2 + 1) - \\sin x \\cdot (x^2 + 1)' }\{ (x^2 + 1)^2 } = \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot 2x }\{ (x^2 + 1)^2 }.$$ To differentiate the sine function, use `Real.deriv_sin`"
  rw [Real.deriv_sin]

  Hint "Our current goal is: $$ \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot ( (x^2 + 1)' ) }\{ (x^2 + 1)^2 } = \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot 2x }\{ (x^2 + 1)^2 }.$$ Rewrite the derivative using `deriv_add` to separate it into two distinct derivatives. This helps in dealing with each part of the sum individually, making it easier to simplify and solve the expression."
  rw [deriv_add]

  Hint "Our current goal is: $$ \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot ( (x^2)' + (1)' ) }\{ (x^2 + 1)^2 } = \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot 2x }\{ (x^2 + 1)^2 }.$$ To simplify the expression involving the derivative of a power function, apply the rewrite rule `deriv_pow'`. This will expand the derivative of $x^2$ into $2x$, aligning it with the target expression."
  rw [deriv_pow']

  Hint "Our current goal is: $$ \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot ( 2 x^{2 - 1} + (1)' ) }\{ (x^2 + 1)^2 } = \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot 2x }\{ (x^2 + 1)^2 }.$$ Rewrite using `deriv_const` to simplify the derivative of a constant function to zero. This will help reduce the expression involving the derivative of the constant term in the numerator."
  rw [deriv_const]

  Hint "Our current goal is: $$ \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot ( 2 x^{2 - 1} + 0 ) }\{ (x^2 + 1)^2 } = \\frac\{ \\cos x \\cdot (x^2 + 1) - \\sin x \\cdot 2x }\{ (x^2 + 1)^2 }.$$ Utilize the `ring_nf` tactic to simplify and normalize polynomial-like expressions. This tactic can help in equating complex expressions by reducing them to a canonical form. In this scenario, it assists in recognizing and eliminating unnecessary terms to verify the equality."
  ring_nf

  Hint "To prove the differentiability at a point for the function $x \\mapsto x^2$, use the `exact` tactic with the lemma `differentiableAt_pow 2`. This will directly establish that $x^2$ is differentiable at any real number $x$."
  exact differentiableAt_pow 2

  Hint "Use the tactic `exact differentiableAt_const 1` to conclude that the function $f(x) = 1$ is differentiable at any point $x$ in $\\mathbb\{R}$. This tactic directly applies the fact that constant functions are differentiable everywhere."
  exact differentiableAt_const 1

  Hint "To show differentiability of the sine function, use `Real.differentiableAt_sin`."
  exact Real.differentiableAt_sin

  Hint "To prove the differentiability of a sum of functions, use `apply DifferentiableAt.add`. This tactic splits the goal into proving the differentiability of each individual function, which in this case are $x^2$ and $1$."
  apply DifferentiableAt.add
  exact differentiableAt_pow 2
  exact differentiableAt_const 1

  Hint "To show that $x ^ 2 + 1 ≠ 0,$ you can show $x ^ 2 + 1 ≥ 1$ instead. Use `have : x ^ 2 + 1 ≥ 1` to introduce the assumption."
  have : x ^ 2 + 1 ≥ 1 := by
    Hint "To show that $x^2 + 1 \\geq 1$, we can use the tactic `apply le_add_of_nonneg_left`. This tactic will reduce the problem to proving that the left term $x^2$ is non-negative, which is straightforward since the square of any real number is always non-negative."
    apply le_add_of_nonneg_left
    Hint "`exact sq_nonneg x` shows that the square of a real number is nonnegative, use this to solve this goal!"
    exact sq_nonneg x
  Hint "To complete the computation, we use `linarith` to solve the goal with the witness `this`."
  linarith

/-- Quotient rule: for differentiable functions $f$ and $g$ with $g(x)≠0,$ one has
  $(f/g)'(x)=((f'g-fg')/g^2)(x).$-/
TheoremDoc deriv_div as "deriv_div" in "Derivative"

/-- Derivative of the sine function is the cosine function. -/
TheoremDoc Real.deriv_sin as "Real.deriv_sin" in "Derivative"

/-- The sine function is differentiable. -/
TheoremDoc Real.differentiableAt_sin as "Real.differentiableAt_sin" in "Derivative"

NewTheorem deriv_div Real.deriv_sin Real.differentiableAt_sin
