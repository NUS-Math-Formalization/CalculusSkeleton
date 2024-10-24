import Game.Metadata
-- import Mathlib
import Game.Lemmas.Limits.Basic
import Game.Lemmas.Inequalities

World "Limit"

Level 2

open Real Topology

Statement : lim x → 0, sin x = 0 := by
  Hint "Apply definition now"
  apply lim_def_fin_fin
  simp
  intro ε hε
  Hint "How can you choose the bound here?"
  use ε
  Hint "Use `constructor` to split the goal!"
  constructor
  · assumption
  · intro x _ hx
    Hint "Apply the inequality here."
    calc
      _ ≤ |x| := abs_sin_le_abs x
      _ < ε := hx

NewTactic assumption Calc

/-- $|sin(x)| \leq |x|$ -/
TheoremDoc Real.abs_sin_le_abs as "abs_sin_le_abs" in "Inequalities"

NewTheorem Real.abs_sin_le_abs
