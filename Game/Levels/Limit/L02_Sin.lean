import Game.Metadata
-- import Mathlib
import Game.Lemmas.Limits.Basic
import Game.Lemmas.Inequalities
--import Game.Lemmas.Limits.delib

World "Limit"

Level 2


open BigOperators Real Topology

/-
Some testing on delib
-/
#check lim_def_fin_fin
#check left_lim_def_fin_fin
#check right_lim_def_fin_fin
#check lim_def_inf_fin
#check lim x → 0, x
#check lim x → ∞, x
#check lim x → ∞, x = ∞

namespace CGame

Statement : (lim x → 0, sin x) = 0 := by
  Hint "Apply definition `lim_def_fin_fin` to rewrite the problem into the ε δ language "
  apply lim_def_fin_fin
  Hint "Now `intro` the $\\epsilon$ and its assumption."
  intro ε hε
  Hint "You always can use `simp` to simplify the goal. "
  simp
  Hint "How can you choose the bound here?"
  Hint "Hint: Consider using  the inequality $|\\sin x| ≤ |x|$."
  use ε
  Hint "Use `constructor` or `And.intro` to split the goal!"
  constructor
  · Hint "Close the goal using assumption."
    assumption
  · intro x _ hx
    Hint "Apply the inequality here."
    apply lt_of_le_of_lt (|x|)
    use abs_sin_le_abs x
    use hx


end CGame

NewTactic assumption refine
/-- $|\sin(x)| \leq |x|$ -/
TheoremDoc CGame.abs_sin_le_abs as "abs_sin_le_abs" in "Inequalities"

/-- $a \leq b$ and $b< c$ imples $a < c$ -/
TheoremDoc CGame.lt_of_le_of_lt as "lt_of_le_of_lt" in "Inequalities"

TheoremDoc And.intro as "And.intro" in "Logic"
TheoremDoc Or.inl as "Or.inl" in "Logic"
TheoremDoc Or.inr as "Or.inr" in "Logic"

NewTheorem CGame.abs_sin_le_abs CGame.lt_of_le_of_lt And.intro Or.inl Or.inr
