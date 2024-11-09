import Game.Metadata

World "Derivative"

Level 9

Title "The derivative of sin(sin(sin (x)))"

Introduction "This level is about finding the derivative of the function $sin(sin(sin(x)))$. This level is done by Kun Yu."

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


lemma sinsinx_differentiable (x : ℝ) : DifferentiableAt ℝ (fun x => Real.sin ( Real.sin x )) x := by sorry

Statement (x : ℝ) : deriv (fun x => Real.sin ( Real.sin ( Real.sin x ) ) ) (x : ℝ) =
 Real.cos x * Real.cos ( Real.sin x ) * Real.cos ( Real.sin ( Real.sin x ) ) := by
 Hint "This is an application of 'Composite Function Derivative', firstly you need to let lean figure out what is the composite function which means you need to set sin(sinx) as function g, which means that we need to turn the goal into : derivative of sin(sin(sin x)) = derivative of sin ∘ g  "
 Hint "To make the sin(sin x) into the function g, you need to try tactic: set g := fun x => ..."
 Hint "Remind that sin in lean should be typed as Real.sin"
 set g := fun x => Real.sin ( Real.sin x )
 Hint "To prove sin(sin(sin x)) = sin ∘ g, use the have and fun x tactic : have : (fun x => Real.sin (Real.sin (Real.sin x))) = Real.sin ∘ g"
 Hint "Notice that there is a tap between two sin : Real.sin ( Real.sin ( Real.sin x ) ))"
 have : (fun x => Real.sin ( Real.sin ( Real.sin x ) )) = Real.sin ∘ g := rfl
 Hint "Now the goal turn into proving: deriv (Real.sin ∘ g) x = Real.cos x * Real.cos (Real.sin x) * Real.cos (Real.sin (Real.sin x))"
 Hint "Rewrite the assumption"
 rw[this]
 Hint "Now to prove : deriv (Real.sin ∘ g) = deriv (g) * deriv (Real.sin (g)), use the deriv.comp tactic"
 rw[deriv.comp]
 Hint "Now the goal are : Proving sin'(x)=cos'(x) and proving g'= cos(x)*cos(sin(x)); Use the Real.deriv_sin tactic"
 rw[Real.deriv_sin]
 Hint "To prove g'= cos(x)*cos(sin(x)), the logic of proving is the same and now suppose we already have the tactic 'deriv_sinsinx'"
 rw[deriv_sinsinx]
 Hint "The remaining problem is just use commutativity of multiplication"
 rw[mul_comm]
 Hint "Now the left two goal is to prove functions sinx and sin(sinx) are differentiable, and you can use the tactic 'Real.differentiableAt_sin' and 'sinsinx_differentiable x' "
 exact Real.differentiableAt_sin
 exact sinsinx_differentiable x
