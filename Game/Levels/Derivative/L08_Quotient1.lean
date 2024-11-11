import Game.Metadata

World "Derivative"

Level 8

Title "The derivative of (x ^ 3 + x)/(x ^ 4 - 2)"

Introduction "This level is about finding the derivative of the function $(x ^ 3 + x)/(x ^ 4 - 2)$. This level is done by Li Junyi."

-- The derivative of frac {x ^ 3 + x}{x ^ 4 - 2}
Statement (x : ℝ)(DenominatorNotZero: x ^ 4 - 2 ≠ 0) : deriv (fun x => (x ^ 3 + x) / (x ^ 4 - 2)) (x : ℝ) =
  ((3 * x ^ 2 + 1) * (x ^ 4 - 2) - (x ^ 3 + x) * (4 * x ^ 3)) / (x ^ 4 - 2) ^ 2 := by
    Hint "Our current goal is $(\\frac\{x ^ 3 + x}\{x ^ 4 - 2}) ^ \\prime = \\frac\{((3x ^ 2 + 1)(x ^ 4 - 2) - (x ^ 3 + x)(4x ^ 3))}\{(x ^ 4 - 2) ^ 2}$, rewrite the goal using `deriv_div`. `deriv_div` is the shorthand of derivative_division, which applies quotient rule to the current goal."
    rw [deriv_div]
    Hint "Our current goal is $ \\frac\{(x ^ 3 + x) ^ \\prime (x ^ 4 - 2) - (x ^ 3 + x) (x ^ 4 - 2) ^ \\prime}\{(x ^ 4 - 2) ^ 2}= \\frac\{((3 x ^ 2 + 1) (x ^ 4 - 2) - (x ^ 3 + x) (4 x ^ 3))}\{(x ^ 4 - 2) ^ 2}$. Only the numerator has derivatives that need to be calculated, so let's proceed by computing the derivatives from left to right. Lean doesn't have a single tactic to handle all derivatives. It only provides derivative rule for Basic functions. Let's start by rewriting with `deriv_add` to expand the first derivative."
    --Expand the derivative using linearity
    rw [deriv_add]
    Hint "Our current goal is $(\\frac\{((x ^ 3) ^ \\prime + x ^ \\prime) (x ^ 4 - 2) - (x ^ 3 + x) (x ^ 4 - 2) ^ \\prime}\{(x ^ 4 - 2) ^ 2}$. We can now calculate $(x ^ 3) ^ \\prime$ and $x ^ \\prime$! Let's first compute $(x ^ 3) ^ \\prime$ using `rw [deriv_pow']`."
    --Kill derivative in the first term
    rw [deriv_pow']
    Hint "Our current goal is $\\frac\{3 x ^ 2 + x ^ \\prime) (x ^ 4 - 2) - (x ^ 3 + x) (x ^ 4 - 2) ^ \\prime)}\{(x ^ 4 - 2) ^ 2}$. It's worth noticing that a strange `↑` symbol appears in the expression. You can safely ignore it, as it represents a type covercion that does not affect the mathematical meaning of the expression. By `rw [deriv_id'']`, we can now calculate $x ^ \\prime)$!"
    rw [deriv_id'']
    --Kill derivative in the second term
    Hint "Our current goal is $ \\frac\{(3 x ^ 2 + 1) (x ^ 4 - 2) - (x ^ 3 + x) (x ^ 4 - 2) ^ \\prime}\{(x ^ 4 - 2) ^ 2}= \\frac\{((3 x ^ 2 + 1) (x ^ 4 - 2) - (x ^ 3 + x) (4 x ^ 3))}\{(x ^ 4 - 2) ^ 2}$. Let's start by rewriting with `deriv_sub` to expand the only derivative we have here."
    rw [deriv_sub]
    Hint "Our current goal is $ \\frac\{(3 x ^ 2 + 1) (x ^ 4 - 2) - (x ^ 3 + x) ((x ^ 4) ^ \\prime  - (2) ^ \\prime)}\{(x ^ 4 - 2) ^ 2}= \\frac\{((3 x ^ 2 + 1) (x ^ 4 - 2) - (x ^ 3 + x) (4 x ^ 3))}\{(x ^ 4 - 2) ^ 2}$. Try to calculate $(x ^ 4) ^ \\prime$ and $(2) ^ \\prime$! Start by using the tactics we have introduced to compute $(x ^ 4) ^ \\prime$."
    rw [deriv_pow']
    Hint "Our current goal is $ \\frac\{(3 x ^ 2 + 1) (x ^ 4 - 2) - (x ^ 3 + x) (4x ^ 3  - (2) ^ \\prime)}\{(x ^ 4 - 2) ^ 2}= \\frac\{((3 x ^ 2 + 1) (x ^ 4 - 2) - (x ^ 3 + x) (4 x ^ 3))}\{(x ^ 4 - 2) ^ 2}$. Try tactic `deriv_const` to compute $(2) ^ \\prime$!"
    rw [deriv_const]
    Hint "Now we have computed all the derivatives in the numerator, the next step is to simplify the numerator so that it matches the form required in our goal. Let's apply tactic `simp`!"
    simp
    Hint "We have successfully compute the derivative in a purely sytactic way! Now we need to pay the debt, noticing that we have not yet consider the differentiability of the functions when we calculating their derivatives. We need to claim that they are differentiable. Let's handle the first goal by using `exact differentiableAt_pow 4`."
    exact differentiableAt_pow 4
    Hint "Try to solve the goal by using `exact differentiableAt_const 2`"
    exact differentiableAt_const 2
    Hint "We have encoutered a similar case before. Try to solve it using the tactics we have already introduced!"
    exact differentiableAt_pow 3
    Hint "Try to solve the goal by using `exact differentiableAt_id`"
    exact differentiableAt_id
    --Break case hc to two goals
    Hint "Lean doesn't provide a single tactic to establish the defferentiability of a general function. Use `apply DifferentiableAt.add` to split the goal `DifferentiableAt ℝ (fun x => x ^ 3 + x) x` into two subgoals : `DifferentiableAt ℝ (fun y => y ^ 3) x` and `DifferentiableAt ℝ (fun y => y) x`"
    apply DifferentiableAt.add
    /-
    Hint "Now try `differentiableAt_pow 3` to show the differentiablility for $y ^ 3$"
    -/
    exact differentiableAt_pow 3
    /-
    Hint "Try `differentiableAt_id` to show the differentiablility for the const function $y = y$"
    -/
    exact differentiableAt_id
    --Break case hd to two goals
    Hint "Lean doesn't have a single tactic to establish the defferentiability of a general function. Use `apply DifferentiableAt.sub` to split the goal `DifferentiableAt ℝ (fun x => x ^ 4 - 2) x` into two subgoals : `DifferentiableAt ℝ (fun y => y ^ 4) x` and `DifferentiableAt ℝ (fun y => 2) x`"
    apply DifferentiableAt.sub
    /-
    Hint "Now try `differentiableAt_pow 4` to show the differentiablility for $y ^ 4$"
    -/
    exact differentiableAt_pow 4
    /-
    Hint "Try `differentiableAt_const 2` to show the differentiablility for the const function $y = 2$"
    -/
    exact differentiableAt_const 2
    --Show the denominator isn't zero
    Hint "Congratulations! We now have our final goal : `Denominator can't be ZERO`, which is exactly our asspumtion! Use `exact DenominatorNotZero` to solve it!"
    exact DenominatorNotZero
