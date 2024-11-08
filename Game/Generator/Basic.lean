import Lean
import Game.Metadata
-- import Mathlib
import Game.Lemmas.Limits.Basic
import Game.Lemmas.Inequalities
import Game.Generator.API
import Lean.Meta.Tactic.TryThis

open Lean Elab Meta Parser PrettyPrinter Tactic

-- def getNextTactic (pos : String.pos) : Syntax :

def mkPrompt (goalBefore currentTactic goalAfter : String) : List String :=
  let p1 := "I am designing natural language hint for Lean 4 code, as a guidance for beginners to write one line of Lean tactic, I will give you state before tactic, state after tactic, tactic used.
# Example Input
## State before the tactic
x : ℝ
⊢ deriv (fun x => x + 1) x = 1
## Tactic used
rw [deriv_add]
## State after the tactic
x : ℝ
⊢ deriv (fun x => x) x + deriv (fun x => 1) x = 1
case hf
x : ℝ
⊢ DifferentiableAt ℝ (fun x => x) x
case hg
x : ℝ
⊢ DifferentiableAt ℝ (fun x => 1) x
# Example Output
Rewrite deriv_add to distribute the derivation. Note that you will need to show the differentiability for each summand to make this lemma work.

# Your input
## State before the tactic
" ++ goalBefore ++ "
## Tactic used
" ++ currentTactic ++ "
## State after the tactic
" ++ goalAfter
  [p1]

def toSuggestion (hint : String) : TryThis.Suggestion where
  suggestion := s!"Hint \"{hint}\""


open LLMlean

-- syntax (name := generate_hint) "generateHint " tactic : tactic

-- @[command_elab generate_hint]
-- def genhint : CommandElab := fun stx currentTactic =>
--   withMainContext do

--     let goalBefore ← Tactic.getMainGoal
--     logInfo m!"{← ppGoal goalBefore}"
--     Tactic.evalTactic currentTactic
--     logInfo m!"{currentTactic}"
--     let goalAfter ← Tactic.getMainGoal
--     logInfo m!"{← ppGoal goalAfter}"
--     let prompt := mkPrompt (toString (← ppGoal goalBefore)) (toString currentTactic) (toString (← ppGoal goalAfter))
--     logInfo m!"{prompt}"
--     let generationOption : GenerationOptions := {temperature := 0.7, numSamples := 1, «stop» := []}
--     let results ← tacticGenerationOpenAI "" prompt (← getAPI) generationOption
--     let (hint, _) := results[0]!
--     TryThis.addSuggestion currentTactic (toSuggestion hint)

elab "GenerateHint " currentTactic:tactic : tactic => withMainContext do

  let goalBefore ← Tactic.getMainGoal
  logInfo m!"{← ppGoal goalBefore}"
  Tactic.evalTactic currentTactic
  logInfo m!"{currentTactic}"
  let goalAfter ← Tactic.getMainGoal
  logInfo m!"{← ppGoal goalAfter}"
  let prompt := mkPrompt (toString (← ppGoal goalBefore)) (toString currentTactic) (toString (← ppGoal goalAfter))
  logInfo m!"{prompt}"
  let generationOption : GenerationOptions := {temperature := 0.7, numSamples := 1, «stop» := []}
  let results ← tacticGenerationOpenAI "" prompt (← getAPI) generationOption
  let (hint, _) := results[0]!
  let hint := hint ++ (toString (currentTactic.raw))
  TryThis.addSuggestion currentTactic.raw (toSuggestion hint)
  -- toSuggestion hint




World "Limit"

Level 1


open Real Topology

Statement : lim x → 0, sin x = 0 := by
  GenerateHint
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
