import Game.Metadata

World "Derivative"

Level 7

Title "The derivative of x^3 + 2x + 4"

Introduction "This level is about finding the derivative of the function $x^3 + 2x + 4$. This level is done by Fang Xinyuan."

-- The derivative of x^3 + 2x + 4
Statement (x : ℝ) : deriv (fun x => x ^ 3 + 2 * x + 4) (x : ℝ) = 3 * x^2 + 2 := by

  Hint "This level is definitely within your reach! Just think back to the similar challenges you've already conquered—those same techniques will help you here. You've got this!"
  Hint "Our current goal is: $$ \\left( x^3 + 2x + 4 \\right)' = 3x^2 + 2.$$ First thing first, Looking at this long string of 'additions', don't you just want to break it apart? That's exactly right! Let's split it into smaller pieces - this will make our work so much easier!"
  rw [deriv_add]

  Hint "Our current goal is: $$ \\left( x^3 + 2x \\right)' + \\left( 4 \\right)' = 3 x^2 + 2. $$"
  rw [deriv_add]

  -- Hint "Recall how we handle powers, constant multiples, and constants!"
  Hint "Our current goal is: $$ \\left( x^3 \\right)' + \\left( 2x \\right)' + \\left( 4 \\right)' = 3 x^2 + 2. $$ Recall how we handle powers, constant multiples, and constants! Use the `rw [deriv_pow]` tactic to rewrite the derivative of the power function. This simplifies the expression $ (x^3) ^ \\prime $ to $ 3 \\cdot x^{3-1} $, making it easier to handle the rest of the expression."
  rw [deriv_pow]

  Hint "Our current goal is: $$ \\uparrow 3 \\cdot x^\{3 - 1} + \\left( 2x \\right)' + \\left( 4 \\right)' = 3 x^2 + 2. $$ To tackle the goal involving derivatives of products, use `rw [deriv_mul]` to apply the product rule. This will break down the derivative of $2x$ into terms involving the derivatives of $2$ and $x$, simplifying the expression."
  rw [deriv_mul]

  Hint "Our current goal is: $$ \\uparrow 3 \\cdot x^\{3 - 1} + \\left( \\left( 2 \\right)' \\cdot x + 2 \\left( x \\right)' \\right) + \\left( 4 \\right)' = 3 x^2 + 2. $$ Use the rewrite tactic with `deriv_const` to simplify derivatives of constant functions. This allows you to replace derivatives of constants with zero, which simplifies the expression significantly."
  rw [deriv_const]

  Hint "Our current goal is: $$ \\uparrow 3 \\cdot x^\{3 - 1} + \\left( 0 \\cdot x + 2 \\left( x \\right)' \\right) + \\left( 4 \\right)' = 3 x^2 + 2. $$ To simplify the goal, use the `rw` tactic with `deriv_id''` to replace the derivative of the identity function with 1. This step helps eliminate the derivative term, making the equation easier to understand and solve."
  rw [deriv_id'']

  Hint "Our current goal is: $$ \\uparrow 3 \\cdot x^\{3 - 1} + \\left( 0 \\cdot x + 2 \\cdot \\left( 1 \\right) \\right) + \\left( 4 \\right)' = 3 x^2 + 2. $$"
  Hint "To simplify the goal involving a constant function's derivative, apply `rw [deriv_const]`. This will replace the derivative of the constant function with zero, as the derivative of a constant is always zero."
  rw [deriv_const]

  Hint "Our current goal is: $$ \\uparrow 3 \\cdot x^\{3 - 1} + \\left( 0 \\cdot x + 2 \\cdot \\left( 1 \\right) \\right) + 0 = 3 x^2 + 2. $$ Take a closer look at our 'Goal' - numbers and variables scattered everywhere... it's quite a mess, isn't it? There's a magical tactic that can clean and 'simplify' this up for us - can you guess what it is?"
  simp --this tactic was introduced

  --Hint "Now show all the differentiability conditions required by previous proof steps."
  Hint "Now show all the differentiability conditions required by previous proof steps. The goal is to prove that the constant function $2$ is differentiable at any point $x$. You can use the fact that constant functions are always differentiable by applying `exact differentiableAt_const 2`. This tactic directly shows the differentiability of the constant function at the given point."
  exact differentiableAt_const 2

  Hint "Use `exact differentiableAt_id'` to directly assert that the function $x \\mapsto x$ is differentiable at any point, including $x$. This tactic instantly resolves the goal by referring to a standard result about the differentiability of the identity function."
  exact differentiableAt_id'

  Hint "In this goal, you need to show that the function $x^3$ is differentiable at $x$. Use the fact that power functions $x^n$ are differentiable everywhere for any natural number $n$. Apply `exact differentiableAt_pow 3` to conclude that $x^3$ is indeed differentiable at any real number $x$."
  exact differentiableAt_pow 3

  -- Hint "When using compound differentiability lemmas like 'const_mul', take note how to spell the lemma, some letters needs capitalisation."
  Hint "When using compound differentiability lemmas like 'const_mul', take note how to spell the lemma, some letters needs capitalisation. To prove the differentiability of a constant multiplied by a function, use `apply DifferentiableAt.const_mul`. This tactic simplifies the problem to showing that the function itself is differentiable, which is often easier to prove."
  apply DifferentiableAt.const_mul --It is 'Differentiable', not 'differentiable'.const_mul
  exact differentiableAt_id'

  Hint "To show that the function $x^3 + 2x$ is differentiable at a point $x$, we can use the `DifferentiableAt.add` lemma. This tactic allows us to express the differentiability of a sum of functions in terms of the differentiability of the individual components. Apply this lemma to break down the goal into proving that each summand, $x^3$ and $2x$, is differentiable at $x$."
  apply DifferentiableAt.add

  Hint "To prove that the function \\( y \\mapsto y^3 \\) is differentiable at a point, you can use the `differentiableAt_pow` lemma. This lemma asserts that power functions are differentiable at any point, provided the exponent is a natural number. Here, apply `exact differentiableAt_pow 3` to directly solve the goal for the cube function."
  exact differentiableAt_pow 3

  Hint "To show that the function $2y$ is differentiable at $x$, use the `apply` tactic with `DifferentiableAt.const_mul`. This leverages the fact that multiplying a differentiable function by a constant results in another differentiable function."
  apply DifferentiableAt.const_mul

  Hint "In this goal, we need to show that the function $y \\mapsto y$ is differentiable at $x$. Use the `exact` tactic with `differentiableAt_id'`, which is a standard lemma stating that the identity function is differentiable everywhere, to directly solve this part of the goal."
  exact differentiableAt_id'

  Hint "Now we can use `exact differentiableAt_const 4` to complete the goal."
  exact differentiableAt_const 4

  --NewTactic norm_num
