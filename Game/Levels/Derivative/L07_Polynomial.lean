import Game.Metadata

World "Derivative"

Level 7

Title "The derivative of x^3 + 2x + 4"

Introduction "This level is about finding the derivative of the function $x^3 + 2x + 4$. This level is done by Fang Xinyuan."

-- The derivative of x^3 + 2x + 4
Statement (x : ℝ) : deriv (fun x => x ^ 3 + 2 * x + 4) (x : ℝ) = 3 * x^2 + 2 := by
  Hint "This level is definitely within your reach! Just think back to the similar challenges you've already conquered—those same techniques will help you here. You've got this!"
  Hint "First thing first, Looking at this long string of 'additions', don't you just want to break it apart? That's exactly right! Let's split it into smaller pieces - this will make our work so much easier!"
  rw[deriv_add]
  rw[deriv_add]
  Hint "Recall how we handle powers, constant multiples, and constants!"
  rw[deriv_pow]
  rw[deriv_mul]
  rw[deriv_const]
  rw[deriv_id'']
  rw[deriv_const]
  Hint "Take a closer look at our 'Goal' - numbers and variables scattered everywhere...
it's quite a mess, isn't it? There's a magical tactic that can clean and 'simplify' this up for us - can you guess what it is?"
  simp --this tactic was introduced
  Hint "Now show all the differentiability conditions required by previous proof steps."
  exact differentiableAt_const 2
  exact differentiableAt_id'
  exact differentiableAt_pow 3
  Hint "When using compound differentiability lemmas like 'const_mul', take note how to spell the lemma, some letters needs capitalisation."
  apply DifferentiableAt.const_mul --It is 'Differentiable', not 'differentiable'.const_mul
  exact differentiableAt_id'
  apply DifferentiableAt.add
  exact differentiableAt_pow 3
  apply DifferentiableAt.const_mul
  exact differentiableAt_id'
  exact differentiableAt_const 4

  --NewTactic norm_num
