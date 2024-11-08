import Game.Metadata
import Mathlib
import Game.Lemmas.Limits.Basic

World "Limit"

Level 4

-- use the ε, δ definition to prove that lim_{x → 2} (-8x + 7) = -9
Statement:  lim x → 2, (-8*x + 7) = -9 := by
  Hint "`apply` the definition `lim_def_fin_fin` now to translate it into the language of $ε - δ$. "
  apply lim_def_fin_fin
  Hint "This is a 'for all' statement, we can use `intro $ε$ h$ε$ ` to obtain restrictions of $ε$"
  intro ε hε
  Hint "This is an existence statement -- we need to choose a suitable value for $δ$. Think back to Calculus class: `use` a value in relation to $ε$."
  use ε/8
  Hint "Now, what we have left to prove is a conjunction, connected by $∧$, a `constructor` tactic is always powful for splitting the conjunction goals."
  constructor
  Hint "Oh no, the expression looks a bit messy, lets use `linarith` to clean it up for us!"
  linarith
  Hint "Another 'for all' statement here, but this time the restriction is on $x$, remember what to do?"
  intro x hx
  Hint "The thing left for us is to really prove the inequality $|-8 * x + 7 - -9| < ε$, this can be quite complecated to directly modify the goal. I will introduce you a powerful trick -- the `have` tactic! We can use `have` to create a new statement as a goal. Once we prove this new goal, we can use it as an assumption. Pretty cool, right? Let's try it!"
  Hint "The expression $|-8 * x + 7 - -9|$ needs tidying up, naturally, we know $|-8 * x + 7 - -9|=|-8 * x + 16|= |-8*x+(-8)*(-2)|=|-8*(x-2)|$. This chain of equations follows from addition commutativity, distribution law, and other properties of ring arithmetic. Luckily, we have a powerful tactic for this: `ring_nf` tactic, it can help you avoid doing the tedious justification in rings."
  Hint "Thus, we could come up with a have tactic this way: `have h0 $(x: ℝ):|-8 * x + 7 - -9|=|(-8)*(x-2)|$:= by ring_nf`. You can name it whatever you want, but make sure to stay organized, as we'll use it later. Here I've named it `h0`."
  have h0 (x:ℝ):|-8 * x + 7 - -9|=|(-8)*(x-2)|:= by ring_nf
  Hint "To translate this into the form $k*|x-2|$ that we need, there are a few steps left. First, there is a tactic `abs_mul` that helps you bring the $-8$ out, so that you have $|-8|*|x-2|$. Try write out this one on your own with `have` to create a intermediate goal, and use `rw[abs_mul]` to solve it."
  have h1 (x:ℝ):|(-8)*(x-2)| = |-8| * |x-2| :=by rw[abs_mul]
  Hint "Hope you like the power of creating your own goals! Here's the next one: Show that $|-8| * |x-2|= 8* |x-2|$, this can be done by `simp`."
  have h2 (x:ℝ):|-8| * |x-2|= 8* |x-2| := by simp
  Hint "Finally, let's connect everything to replace $|-8 * x + 7 - -9|$ with the simpler form $8* |x-2|$ in our main goal. Just to do it one more time using `have`! With the help of all our previous effort, we can now easily use `rw[h0, h1,h2] to bridge them together!"
  have h3 (x:ℝ):|-8 * x + 7 - -9| = 8* |x-2| := by rw[h0, h1, h2]
  Hint "You've got it! Now simply replace the long expression in the goal using `rw[h3]`, or whatever you named for the assumption."
  rw[h3]
  Hint "With $|x-2|< \\frac\{ε}\{8} $, it is easy to show $8 * |x-2| < ε $. Lean will help you finish it with `linarith`."
  linarith

NewTactic ring_nf 
