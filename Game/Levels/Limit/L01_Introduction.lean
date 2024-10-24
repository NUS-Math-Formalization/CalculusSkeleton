import Game.Metadata
import Mathlib
import Game.Lemmas.Limits.Basic

World "Limit"

Level 1

open BigOperators Topology


Statement : lim x → 0, 2 * x = 0 := by
  apply lim_def_fin_fin
  Hint "Use `simp` to simplify zeros."
  simp
  Hint "Use `intro` to obtain restrictions of ε"
  intro ε hε
  Hint "Find a suitable δ now, and insert it into place by `use`"
  use ε/2
  constructor
  · Hint "This inequality is easy. You can solve it manually or try `linarith` for some automation."
    linarith
  · intro x _ hx
    Hint "This inequality is a little bit hard. Use a `calc` block."
    calc
      _ = 2 * |x| := by rw [abs_mul, abs_two]
      _ < ε := by linarith

/-- The definitive equivalence for limits in finite case  -/
TheoremDoc lim_def_fin_fin as "lim_def_fin_fin" in "Definition"

/-- $ |m * x| = |m| * |x| $ -/
TheoremDoc abs_mul as "abs_mul" in "Equalities"

/-- $ |2| = 2 $ -/
TheoremDoc abs_two as "abs_two" in "Equalities"

NewTactic apply rw exact simp use intro constructor linarith
NewTheorem lim_def_fin_fin abs_two abs_mul
