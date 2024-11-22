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

  -- Hint "We want to use function composition so first we define several functions, one each for (u^4), (x-1), (u^5), (x^2+2x)"
  Hint "We want to use function composition to do this derivative, so first we define several functions."
  Hint "To make the expression more manageable, use the `set` tactic to define a simpler function, `f₁`, which represents $u \\mapsto u^4$. This can help break down the problem into smaller parts, making it easier to work with derivatives or other transformations later. Try `set f₁ := (fun u : ℝ  => u^4)` to introduce the function we want."
  set f₁ := (fun u : ℝ  => u^4)

  Hint "To simplify and organize our expressions, we can introduce a new function, $g_1(x) = x - 1$, using the `set` tactic. This will allow us to refer to this part of the expression more easily in subsequent steps."
  set g₁ := (fun x : ℝ  => x - 1)

  Hint "To manage the complexity of the expression, introduce a new function $f_2(u) = u^5$ using the `set` tactic. This will help keep your calculations organized as you work through the derivative problem."
  set f₂ := (fun u : ℝ  => u^5)

  Hint "The tactic `set g₂ := (fun x => x ^ 2 + 2 * x)` is used to introduce a new function, `g₂`, for simplifying the expression in your goal. This can help make subsequent calculations more manageable and your code more readable by giving a name to a recurring subexpression, $(x^2 + 2x)$."
  set g₂ := (fun x : ℝ  => x^2 + 2*x)

  Hint "Prove some lemmas to show that (x-1)^4 is a composition of two functions, and do the same for (x^2 + 2*x)^5, using rfl to prove"
  Hint "To facilitate the differentiation of the function, introduce an auxiliary result stating that $(x - 1)^4$ can be expressed as a composition $f_1 \\circ g_1$, where $f_1(u) = u^4$ and $g_1(x) = x - 1$. This step helps to clarify the structure of the function and sets the stage for applying derivative rules more easily. Use `have top : (fun x => (x-1)^4) = f₁ ∘ g₁ := by rfl` to establish this."
  have top : (fun x => (x-1)^4) = f₁ ∘ g₁ := by rfl

  Hint "We want to show that $ (x^2 + 2x)^5 $ can be expressed as a composition of two functions, $ f_2 $ and $ g_2 $. Use `have bottom : (fun x => (x^2 + 2*x)^5) = f₂ ∘ g₂ := by rfl` to introduce a new hypothesis named `bottom` that asserts this equality. This hypothesis is proved by using the `rfl` tactic, which confirms that both sides are indeed the same. This will help us apply the chain rule more conveniently in the differentiation process."
  have bottom : (fun x => (x^2 + 2*x)^5) = f₂ ∘ g₂ := by rfl

  -- Hint "We also prove differentiability of (x^2 + 2*x) which will be used later"
  -- have differentiableAt_g₂ : DifferentiableAt ℝ g₂ x := by

  --   -- Hint "First use DifferentiableAt.add since it's 2 functions added together, then differentiableAt_pow for the first half"
  --   Hint "To prove that $g_2(x) = x^2 + 2x$ is differentiable at $x$, use the `DifferentiableAt.add` tactic. This tactic breaks down the problem of differentiability of a sum into proving the differentiability of each part of the sum separately. You'll now need to show the differentiability of each term in $g_2(x)$, starting with $y^2$."
  --   apply DifferentiableAt.add
  --   Hint "Use the `exact` tactic with `differentiableAt_pow` to directly establish the differentiability of $y^2$ at any real number $x$. This lemma confirms that the function $y^2$ is differentiable at any point on the real line, which satisfies our current goal."
  --   exact differentiableAt_pow 2

  --   -- Hint "Use DifferentiableAt.mul for 2*x part"
  --   Hint "To prove that the function $2 \\cdot y$ is differentiable at $x$, use `DifferentiableAt.mul` to break it down into the differentiability of the constant function $2$ and the identity function $y$. This tactic will help you handle the product of these two functions by focusing on their individual differentiability."
  --   apply DifferentiableAt.mul
  --   Hint "To demonstrate that a constant function is differentiable at any point, use the `exact differentiableAt_const` tactic. This tactic asserts that the derivative of a constant function is zero everywhere, hence it is differentiable at any point."
  --   exact differentiableAt_const 2
  --   Hint "Now we use `exact differentiableAt_id` to prove our assumption on the function $g_2$. "
  --   exact differentiableAt_id

  Hint "Out current goal is : $$ ( \\frac\{ (x - 1)^\{4} }\{ (x^\{2} + 2 x )^\{5} } )' = \\frac\{ 4 (x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 (x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }.$$ Since we are dealing with a quotient, use `rw` to rewrite the statement with `deriv_div`."
  rw [deriv_div]

  -- Hint "Use rw to replace (x-1)^4 and (x^2 + 2*x)^5 with the composition proven earlier"
  Hint "Out current goal is : $$ \\frac\{ ( (x - 1)^\{4} )' \\cdot (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot ( (x^\{2} + 2 x )^\{5} )' }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4 (x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 (x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }. $$ To simplify the current goal, apply the rewrite rules `top` and `bottom`. This will replace the expressions $(x - 1)^4$ and $(x^2 + 2x)^5$ with their respective compositions, $f_1 \\circ g_1$ and $f_2 \\circ g_2$. This transformation makes it easier to handle the derivatives involved by clearly identifying the chain rule applications."
  rw [top, bottom]

  Hint "Out current goal is : $$ \\frac\{ ( f_\{1} \\circ g_\{1} )' \\cdot (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot ( f_\{2} \\circ g_\{2} )'}\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4 (x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 (x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }. $$ Now apply `deriv.comp` twice, which gives the derivative of a composite function"
  rw [deriv.comp, deriv.comp]

  Hint "Out current goal is : $$ \\frac\{ f_\{1}' (g_\{1}) \\cdot g_\{1}' \\cdot (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot f_\{2}' (g_\{2}) \\cdot g_\{2}'}\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4 (x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 (x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }. $$ rw with `deriv_pow` twice to compute the derivatives of u^4 and u^5"
  rw [deriv_pow, deriv_pow]

  Hint "Out current goal is : $$ \\frac\{ 4 \\cdot (g_\{1})^\{4 - 1} \\cdot g_\{1}' \\cdot (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 \\cdot (g_\{2})^\{5 - 1} \\cdot g_\{2}'}\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4 (x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 (x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }. $$ Now to rw deriv(x-1), use deriv_sub_const for functions with a constant subtracted away"
  Hint "To simplify the expression involving derivatives, apply the `deriv_sub_const` tactic. This will help rewrite the derivative of a constant term, allowing you to focus on differentiating the variable component effectively."
  rw [deriv_sub_const]

  Hint "Out current goal is : $$ \\frac\{ 4 \\cdot (g_\{1})^\{4 - 1} \\cdot x' \\cdot (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 \\cdot (g_\{2})^\{5 - 1} \\cdot g_\{2}'}\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4 (x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 (x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }. $$ To simplify the expression involving derivatives, apply the `rw [deriv_id'']` tactic. This will replace $ (\\text\{id}) ^ \\prime $ with the constant function $1$, aligning with the fact that the derivative of $x$ with respect to $x$ is $1$."
  rw [deriv_id'']

  -- Hint "For $ (x^2 + 2*x) ^ \\prime $, use `deriv_add`, `deriv_const_mul`, `deriv_id''`"
  Hint "Out current goal is : $$ \\frac\{ 4 \\cdot (g_\{1})^\{4 - 1} \\cdot 1 \\cdot (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 \\cdot (g_\{2})^\{5 - 1} \\cdot g_\{2}'}\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4 (x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5 (x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }.$$ Our goal involves simplifying the expression for the derivative of a composite function. By applying the `rw [deriv_add]` tactic, we expand the derivative of $g₂$, which is $x^2 + 2x$, into the sum of the derivatives of its terms, specifically $ (x^2) ^ \\prime + (2x) ^ \\prime $. This step will help in matching the given expression to the form we want."
  rw [deriv_add]

  Hint "Out current goal is : $$ \\frac\{\\uparrow 4 \\cdot (g_\{1})^\{4 - 1} \\cdot ( 1 ) \\cdot (x^\{2} + 2 x )^\{5}}\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } - \\frac\{ (x - 1)^\{4} \\cdot \\uparrow 5 \\cdot (g_\{2})^\{5 - 1} \\cdot ( ( x^\{2} )' + ( 2x )' ) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4(x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5(x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }. $$ Rewrite the `deriv_pow` rule to differentiate expressions of the form $x^n$. This will help simplify the derivative of $x^2$ within the given expression."
  rw [deriv_pow]

  Hint "Out current goal is : $$ \\frac\{\\uparrow 4 \\cdot (g_\{1})^\{4 - 1} \\cdot ( 1 ) \\cdot (x^\{2} + 2 x )^\{5}}\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } - \\frac\{ (x - 1)^\{4} \\cdot \\uparrow 5 \\cdot (g_\{2})^\{5 - 1} \\cdot ( 2 x^\{2 - 1} + ( 2x )' ) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4(x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5(x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }. $$ In order to simplify our expression, we use the tactic `rw [deriv_const_mul]`. This rewrites the derivative of a constant multiple of a function by pulling the constant out of the derivative. Specifically, it helps us to manage terms where a constant is multiplied with a derivative, simplifying the expression for further manipulation."
  rw [deriv_const_mul]

  Hint "Out current goal is : $$ \\frac\{\\uparrow 4 \\cdot (g_\{1})^\{4 - 1} \\cdot ( 1 ) \\cdot (x^\{2} + 2 x )^\{5}}\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } - \\frac\{ (x - 1)^\{4} \\cdot \\uparrow 5 \\cdot (g_\{2})^\{5 - 1} \\cdot ( 2 x^\{2 - 1} + 2 \\cdot x' ) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4(x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5(x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }. $$ To simplify the derivative expression involving constant functions, apply `rw [deriv_id'']`. This will rewrite the derivative of the identity function to 1, transforming $(x)'$ into 1, which simplifies your expression."
  rw [deriv_id'']

  Hint "Out current goal is : $$ \\frac\{\\uparrow 4 \\cdot (g_\{1})^\{4 - 1} \\cdot ( 1 ) \\cdot (x^\{2} + 2 x )^\{5}}\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } - \\frac\{ (x - 1)^\{4} \\cdot \\uparrow 5 \\cdot (g_\{2})^\{5 - 1} \\cdot ( 2 x^\{2 - 1} + 2 \\cdot ( 1 ) x ) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} } = \\frac\{ 4(x - 1)^\{3} (x^\{2} + 2 x )^\{5} - (x - 1)^\{4} \\cdot 5(x^\{2} + 2 x )^\{4} (2 x + 2) }\{ ( (x^\{2} + 2 x )^\{5} )^\{2} }. $$ use `simp` to reduce to the final answer"
  simp

-- exact differentiability
  Hint "Now to prove the differentiability conditions"
  Hint "To show that the identity function is differentiable at any point, use `exact differentiableAt_id`. This tactic directly applies the fact that the identity function, $f(x) = x$, is differentiable everywhere, including at the point in question."
  exact differentiableAt_id

  Hint "Use the `exact` tactic with `differentiableAt_pow _` to show that the function $x^2$ is differentiable at $x$. The `differentiableAt_pow` lemma directly applies here, allowing you to conclude differentiability for power functions."
  exact differentiableAt_pow _

  Hint "Use `DifferentiableAt.const_mul` for functions multiplied with a constant"
  apply DifferentiableAt.const_mul

  -- Hint "In this case, the goal is to show that the identity function is differentiable at a given point. You can use the `exact` tactic with `differentiableAt_id`, which is a known fact that the identity function is differentiable everywhere. This tactic directly solves the goal by providing this fact."
  exact differentiableAt_id

  -- Hint "Remember this is just the function u^5 but evaluated at a different value instead of just x"
  Hint "To proceed with proving differentiability, you can use the `differentiableAt_pow` lemma by applying it to the function $f_2(u) = u^5$. This will help establish that $f_2$ is differentiable at the point $g_2(x) = x^2 + 2x$. After applying this lemma, you'll need to show that $g_2(x)$ itself is differentiable at $x$ to complete the proof."
  apply differentiableAt_pow _

  -- Hint "Use the lemma we proved for differentiability of (x^2 + 2*x)"
  Hint "To establish the differentiability of the function $g_2(x) = x^2 + 2x$, apply a lemma `apply differentiableAt_g₂`. This applies the known differentiability of $g_2$ at any point $x$, allowing us to focus next on proving the differentiability of the composed function $f_1(g_1(x))$."
  apply differentiableAt_g₂

  Hint "Same as before, this is just proving differentiability of function u^4 evaluated at some different point"
  apply differentiableAt_pow

  Hint "To show that the function $g_1(x) = x - 1$ is differentiable at $x$, we can apply the `DifferentiableAt.sub_const` lemma. This tactic helps us establish differentiability by recognizing that subtracting a constant from a differentiable function, like the identity function here, preserves differentiability."
  apply DifferentiableAt.sub_const

  Hint "To conclude that the identity function is differentiable at any point, use `exact differentiableAt_id`. This tactic directly applies the fact that the derivative of the identity function is well-defined everywhere."
  exact differentiableAt_id

  Hint "For this, we need to use DifferentiableAt.comp, which requires us to rewrite into a function composition again. Use `rw [top]` to rewrite the function."
  rw [top]

  Hint "Other than that, just have to prove that both functions in the composition are differentiable"
  Hint "To prove the differentiability of the composition $f₁ \\circ g₁$, use the `DifferentiableAt.comp` lemma. This allows you to decompose the problem into showing that both $f₁$ and $g₁$ are differentiable at the relevant points. You already have the differentiability of $g₁$, so focus on $f₁$."
  apply DifferentiableAt.comp

  Hint "To prove that the function $f_1(g_1(x)) = (x-1)^4$ is differentiable at $x$, apply the `differentiableAt_pow` tactic. This tactic allows you to establish differentiability for expressions of the form $u^n$, where you need to ensure that the inner function $g₁(x)=x-1$ is differentiable at the given point."
  apply differentiableAt_pow

  Hint "To prove that the function $g_1(x) = x - 1$ is differentiable at $x$, apply the `DifferentiableAt.sub_const` tactic. This tactic indicates that subtracting a constant from a differentiable function (in this case, the identity function) preserves differentiability."
  apply DifferentiableAt.sub_const

  Hint "To show that the identity function is differentiable at any point, use `exact differentiableAt_id`. This tactic directly applies the fact that the identity function is differentiable everywhere, which addresses the goal of proving differentiability at a specific point."
  exact differentiableAt_id

  Hint "We want to show that the function \\( (x^2 + 2x)^5 \\) is differentiable at \\( x \\). By using the equation `bottom`, you can rewrite the expression as a composition of functions \\( f₂ \\) and \\( g₂ \\). This transformation can help us apply rules for differentiability of compositions, such as the chain rule."
  rw [bottom]

  Hint "To prove the differentiability of a composition of functions, use the `DifferentiableAt.comp` lemma. This allows you to break down the differentiability of the composed function into proving the differentiability of each individual function at the relevant points."
  apply DifferentiableAt.comp

  Hint "To prove that the function $f_2(x) = x^5$ is differentiable at $(x^2 + 2x)$, we can apply the `differentiableAt_pow` lemma. This lemma confirms that a power function is differentiable everywhere, which simplifies our task of showing differentiability at a particular point."
  apply differentiableAt_pow

  Hint "To prove the differentiability of the function $g_2(x) = x^2 + 2x$, use `apply differentiableAt_g₂` is employed. This tactic leverages a predefined lemma or fact that confirms the differentiability of $g_2$ at any point $x$."
  apply differentiableAt_g₂

  Hint "Finally, use our assumption to show that we do not divide by zero by applying `hx1`."
  apply hx1

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
