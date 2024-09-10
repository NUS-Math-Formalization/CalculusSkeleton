import Game.Metadata
-- import Mathlib
import Game.Levels.Limit.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

World "Limit"

Level 2

Statement : lim x → 0, Real.sin x = 0 := by
  apply lim_def_fin_fin
  simp
  intro ε hε
  Hint "How can you choose the bound here?"
  use ε
  constructor
  · assumption
  · intro x hx
    calc
      _ ≤ |x| := Real.abs_sin_le_one

