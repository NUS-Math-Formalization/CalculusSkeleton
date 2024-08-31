import Game.Metadata

World "DemoWorld"
Level 3

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

Statement (h : x = 23) (g: y = 46) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  Branch
    Hint "Test"
    rw [g, h]
    -- Hint "You are right!"
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl simp
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
