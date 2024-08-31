import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Game.Metadata

World "Derivative"

Level 2

Title "A Simple Example"

open Real

Statement (x : ℝ) : deriv (fun x : ℝ => x + 1) (x : ℝ) = 1 := by
  Hint "Rewrite `deriv_add` to distribute the derivation. Note that you will need to show the differentiability for each add-term to make this lemma work."
  rw [deriv_add]
  pick_goal 2
  Hint "Here you need to deal with differentiability for $f(x)=x$. This is an identity map, use `differentiableAt_id'`. Please use tactic `exact` when give the lemma is exactly the proposed goal."
  exact differentiableAt_id'
  pick_goal 2
  Hint "Here you need to prove the differentiability for $f(x)=1$. This is a constant map, use `differentiableAt_const`. Don't forget to pass the constant as a parameter."
  exact differentiableAt_const 1
  Hint "You can try to differentiate either term {x} or term {1}, respectly by `deriv_id''` or `deriv_const`."
  Branch
    rw [deriv_id'']
    Hint "Rewrite to differentiate term {1} now."
    rw [deriv_const]
    Hint "Use tactic `dsimp` to make it friendly."
    dsimp
    Hint "Rewrite `add_zero` to simplify {x} + {0}."
    rw [add_zero]
  rw [deriv_const]
  Hint "Rewrite to differentiate term {x} now."
  rw [deriv_id'']
  dsimp
  rw [add_zero]

/-- Rewrite an expression -/
TacticDoc rw

/-- Simplify a formula by definition -/
TacticDoc dsimp

/-- For any real number $x$, we have $x + 0 = x$ -/
TheoremDoc add_zero as "add_zero" in "Add"

/-- Identity map is always differentiable -/
TheoremDoc differentiableAt_id' as "differentiableAt_id'" in "Differentiable"

/-- Constant map is always differentiable -/
TheoremDoc differentiableAt_const as "differentiableAt_const" in "Differentiable"

/-- If map $f$ and $g$ are differentiable, then $(f + g)' = f' + g'$ -/
TheoremDoc deriv_add as "deriv_add" in "Derivative"

/-- $x' = 1$ -/
TheoremDoc deriv_id'' as "deriv_id''" in "Derivative"

/-- For any constant $c$, $c' = 0$ -/
TheoremDoc deriv_const as "deriv_const" in "Derivative"

NewTactic exact rw dsimp pick_goal rfl

NewTheorem add_zero differentiableAt_id' differentiableAt_const deriv_add deriv_id'' deriv_const
