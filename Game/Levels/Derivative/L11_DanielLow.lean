import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Game.Metadata
import Game.Lemmas.Derivatives.DiffAt

World "Derivative"

Level 11

Title "Derivative of (x-1)^4/(x^2+2x)^5"

-- The derivative of frac{(x-1)^4}{(x^2 +2x)^5}
Statement (x : ℝ) (hx1 : (x^2 + 2*x)^5 ≠ 0) :
deriv (fun x : ℝ => (x-1)^4 / (x^2 + 2*x)^5) x
= (4*(x-1)^ 3 * (x^2 + 2*x)^5 - (x - 1)^4 * (5*(x^2 + 2*x)^4 * (2*x + 2))) / ((x^2 + 2*x)^5) ^ 2 := by
  Hint "##Introduction
  $\\frac\{(x-1)^4}\{(x^2+2x)^5}$We want to use function composition so first we define several functions, one each for (u^4), (x-1), (u^5), (x^2+2x)"
  set f₁ := (fun u : ℝ  => u^4); set g₁ := (fun x : ℝ  => x - 1)
  set f₂ := (fun u : ℝ  => u^5); set g₂ := (fun x : ℝ  => x^2 + 2*x)
  Hint "Prove some lemmas to show that (x-1)^4 is a composition of two functions, and do the same for (x^2 + 2*x)^5, using rfl to prove"
  have top : (fun x => (x-1)^4) = f₁ ∘ g₁
  rfl
  have bottom : (fun x => (x^2 + 2*x)^5) = f₂ ∘ g₂
  rfl
  Hint "We also prove differentiability of (x^2 + 2*x) which will be used later"
  have diff_g₂ : DifferentiableAt ℝ g₂ x := by
    Hint "First use DifferentiableAt.add since it's 2 functions added together, then differentiableAt_pow for the first half"
    apply DifferentiableAt.add; exact differentiableAt_pow 2;
    Hint "Use DifferentiableAt.mul for 2*x part"
    apply DifferentiableAt.mul; exact differentiableAt_const 2
    exact differentiableAt_id
  Hint "Since we are dealing with a quotient, use rw the statement with deriv_div"
  rw [deriv_div]
  Hint "Use rw to replace (x-1)^4 and (x^2 + 2*x)^5 with the composition proven earlier"
  rw [top, bottom]
  Hint "Now apply deriv.comp, which gives the derivative of a composite function"
  rw [deriv.comp, deriv.comp]
  Hint "rw with deriv_pow twice to compute the derivatives of u^4 and u^5"
  rw [deriv_pow, deriv_pow]
  Hint "Now to rw deriv(x-1), use deriv_sub_const for functions with a constant subtracted away"
  rw [deriv_sub_const, deriv_id'']
  Hint "For deriv(x^2 + 2*x), use deriv_add, deriv_const_mul, deriv_id''"
  rw [deriv_add]
  rw [deriv_pow]
  rw [deriv_const_mul, deriv_id'']
  Hint "use simp to reduce to the final answer"
  simp
  Hint "Now to prove the differentiability conditions"
  differentiability
  exact hx1

/-- Reduce DifferentiableAt statements to easier assumptions -/
TacticDoc differentiability

/-- Chain Rule: $(f ∘ g)'(x)=f'(g(x))g'(x)$ -/
TheoremDoc deriv.comp as "deriv.comp" in "Derivative"

/-- Addition Rule: $(f + g)'(x) = f'(x) + g'(x))$ -/
TheoremDoc DifferentiableAt.add as "DifferentiableAt.add" in "Differentiable"

/-- Product Rule: $(f * g)'(x) = f'(x) * g(x) + g'(x) * f(x))$ -/
TheoremDoc DifferentiableAt.mul as "DifferentiableAt.mul" in "Differentiable"

/-- Product Rule: $(c * g)'(x) =  c * g'(x))$ -/
TheoremDoc DifferentiableAt.const_mul as "DifferentiableAt.const_mul" in "Differentiable"

NewTactic differentiability
