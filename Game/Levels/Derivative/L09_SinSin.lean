import Game.Metadata

World "Derivative"

Level 9

Title "The derivative of sin(sin(sin x))"

Introduction "This level is about finding the derivative of the function $\\sin(\\sin(\\sin x))$. This level is done by Kun Yu."

lemma deriv_sinsinx (x : ℝ) :
  deriv (fun x => Real.sin ( Real.sin x )) (x : ℝ) = Real.cos x * Real.cos (Real.sin x) := by
  set g := fun x => Real.sin x
  have : (fun x => Real.sin (Real.sin x)) = Real.sin ∘ g := rfl
  rw[this]
  rw[deriv.comp]
  rw[Real.deriv_sin]
  rw[mul_comm]
  exact Real.differentiableAt_sin
  exact Real.differentiableAt_sin


lemma differentiableAt_sinsinx (x : ℝ) : DifferentiableAt ℝ (fun x => Real.sin ( Real.sin x )) x := by sorry

Statement (x : ℝ) : deriv (fun x => Real.sin ( Real.sin ( Real.sin x ) ) ) (x : ℝ) =
  Real.cos x * Real.cos ( Real.sin x ) * Real.cos ( Real.sin ( Real.sin x ) ) := by

  Hint "This is an application of 'Composite Function Derivative', firstly you need to let lean figure out what is the composite function which means you need to set $\\sin(\\sin x)$ as function $g$. Then we can turn the goal into : $derivative of $(\\sin(\\sin(\\sin x)))' = \\sin(g(x))$."
  Hint "To set $\\sin(\\sin x)$ to function $g$, use tactic : `set g := fun x => Real.sin ( Real.sin x )` "
  Hint "In lean we use `Real.sin` in stead of `sin`."
  set g := fun x => Real.sin ( Real.sin x )

  -- Hint "To prove $\\sin(\\sin(\\sin x)) = \\sin(g(x))$, use have and fun x tactic : have : (fun x => Real.sin (Real.sin (Real.sin x))) = Real.sin ∘ g"
  -- Hint "Notice that there is a tap between two sin : Real.sin ( Real.sin ( Real.sin x ) ))"
  Hint "To progress towards proving the goal involving the derivative of nested sine functions, introduce a helper fact with `have` to establish that the function $ \\sin(\\sin(\\sin x)) $ can be expressed as $ \\sin \\circ g $, where $ g(x) = \\sin(\\sin x) $. This will allow you to simplify the derivative calculation by recognizing the composition of functions."
  have : (fun x => Real.sin ( Real.sin ( Real.sin x ) )) = Real.sin ∘ g := rfl

  -- Hint "Now the goal turn into proving: deriv (Real.sin ∘ g) x = Real.cos x * Real.cos (Real.sin x) * Real.cos (Real.sin (Real.sin x))"
  -- Hint "Rewrite the assumption"
  Hint "Our current goal is $$ ( \\sin(\\sin(\\sin x)) )' = \\cos x \\cdot \\cos(\\sin x) \\cdot \\cos(\\sin(\\sin x)). $$ To tackle the goal involving the derivative of a composite sine function, apply the rewrite rule `this` to simplify the expression. This will convert $ (x \\mapsto \\sin(\\sin(\\sin x))) ^ \\prime $ into $ (\\sin \\circ g) ^ \\prime $, where $ g(x) = \\sin(\\sin x) $, making it more straightforward to differentiate using the chain rule."
  rw[this]

  -- Hint "Now we want to prove : deriv (Real.sin ∘ g) = deriv (g) * deriv (Real.sin (g)), use the deriv.comp tactic"
  Hint "Our current goal is $$ ( \\sin(g(x)) )' = \\cos x \\cdot \\cos(\\sin x) \\cdot \\cos(\\sin(\\sin x)). $$ Now we want to prove : $\\sin(g(x)) ^ \\prime = g ^ \\prime * \\sin(g(x))$, try tactic `deriv.comp` to complete the goal."
  rw [deriv.comp]

  -- Hint "Now the goal are : Proving sin'(x)=cos'(x) and proving g'= cos(x)*cos(sin x); Use the Real.deriv_sin tactic"
  Hint "Our current goal is $$ \\cos(g(x)) \\cdot g'(x) = \\cos x \\cdot \\cos(\\sin x) \\cdot \\cos(\\sin(\\sin x)). $$ To tackle the goal involving the derivative of the sine function, apply the rewrite tactic with `Real.deriv_sin`. This will transform the derivative of $\\sin$ into its cosine form, simplifying the left-hand side of the equation."
  rw [Real.deriv_sin]

  -- Hint "To prove g'= cos(x)*cos(sin x), the logic of proving is the same and now suppose we already have the tactic 'deriv_sinsinx'"
  Hint "Our current goal is $$ \\cos(g(x)) \\cdot g'(x) = \\cos x \\cdot \\cos(\\sin x) \\cdot \\cos(\\sin(\\sin x)). $$ To tackle the goal involving the composition of sine functions, apply the rewrite rule `deriv_sinsinx`. This will replace the derivative of the nested sine function with the product of the cosines of the inner functions, simplifying the expression for further manipulation."
  rw [deriv_sinsinx]

  Hint "Our current goal is $$ \\cos(g(x)) \\cdot ( \\cos x \\cdot \\cos(\\sin x) ) = \\cos x \\cdot \\cos(\\sin x) \\cdot \\cos(\\sin(\\sin x)). $$ The remaining problem is just use commutativity of multiplication"
  rw [mul_comm]

  Hint "Now the left two goal is to prove functions sinx and sin(sinx) are differentiable, and you can use the tactic `Real.differentiableAt_sin` and `differentiableAt_sinsinx x` "
  exact Real.differentiableAt_sin

  Hint "Notice that $g(x) = \\sin(\\sin x)$, use tactic `differentiableAt_sinsinx` to complete the last goal!"
  exact differentiableAt_sinsinx x

/-- Compute the derivative of sinsin x -/
TheoremDoc deriv_sinsinx as "deriv_sinsinx" in "Derivative"

/-- Differentiability of sinsinx-/
TheoremDoc differentiableAt_sinsinx as "differentiableAt_sinsinx" in "Differentiable"

NewTheorem deriv_sinsinx differentiableAt_sinsinx
