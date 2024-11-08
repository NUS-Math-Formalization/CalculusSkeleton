import Lean
import Game.Metadata
-- import Mathlib
import Game.Lemmas.Limits.Basic
import Game.Lemmas.Inequalities
import Game.Generator.API
import Lean.Meta.Tactic.TryThis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Lean Elab Meta Parser PrettyPrinter Tactic

-- def getNextTactic (pos : String.pos) : Syntax :

def mkPrompt (goalBefore currentTactic goalAfter : String) : List String :=
  let p1 := "I am designing natural language hint for Lean 4 code, as a guidance for beginners to write one line of Lean tactic, I will give you state before tactic, state after tactic, and tactic used.
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
  let ref ← getRef
  -- let hint := hint ++ (toString (currentTactic.raw))
  -- logInfo m!"{ref[0]}"
  TryThis.addSuggestion ref[0] (toSuggestion hint)
  -- toSuggestion hint




World "Limit"

Level 1

set_option pp.rawOnError true

open Real Topology

Statement : lim x → 0, sin x = 0 := by
  Hint "Apply the lemma `lim_def_fin_fin` to transform the limit statement into its epsilon-delta definition. You will now need to establish the conditions for each ε to find a suitable δ that satisfies the inequality for |sin x|."
  apply lim_def_fin_fin
  -- apply?
  simp
  intro ε hε
  -- GenerateHint
  use ε
  Hint "Use `constructor` to split the goal!"
  constructor
  · assumption
  · intro x _ hx
    Hint "Apply the inequality here."
    calc
      _ ≤ |x| := abs_sin_le_abs x
      _ < ε := hx







lemma sinsinx_differentiable (x : ℝ) : DifferentiableAt ℝ (fun x => Real.sin ( Real.sin x )) x := by sorry

example (x : ℝ) : deriv (fun x => Real.sin ( Real.sin ( Real.sin x ) ) ) (x : ℝ) =
 Real.cos x * Real.cos ( Real.sin x ) * Real.cos ( Real.sin ( Real.sin x ) ) := by
 Hint "This is an application of 'Composite Function Derivative', firstly you need to let lean figure out what is the composite function which means you need to set sin( sin x) as function g"
 GenerateHint
 set g := fun x => Real.sin ( Real.sin x )
 Hint "Try to rewrite the question"
 have : (fun x => Real.sin ( Real.sin ( Real.sin x ) )) = Real.sin ∘ g := rfl
 Hint "Try rw[] to apply the assumption"
 rw[this]
 Hint "Now we can use the tactic: deriv.comp"
 rw[deriv.comp]
 Hint "Solve the derivetive by the tactic deriv_.."
 rw[Real.deriv_sin]
 GenerateHint
 have h : deriv (fun x => Real.sin ( Real.sin x )) (x : ℝ) = Real.cos x * Real.cos (Real.sin x) := by
  set g := fun x => Real.sin x
  have : (fun x => Real.sin (Real.sin x)) = Real.sin ∘ g := rfl
  rw[this]
  rw[deriv.comp]
  rw[Real.deriv_sin]
  rw[mul_comm]
  Hint "Now we only need to apply Real.differentiableAt_sin"
  exact Real.differentiableAt_sin
  exact Real.differentiableAt_sin
 Hint "apply the rewrite tactic"
 rw[h]
 Hint "Try mul_comm"
 rw[mul_comm]
 Hint "Solve the differentiable question by tactic: Real.differentiableAt_sin"
 exact Real.differentiableAt_sin
 Hint "Suppose that we already have the sinsinx_differentiable"
 exact sinsinx_differentiable x

NewTactic assumption Calc

/-- $|sin(x)| \leq |x|$ -/
TheoremDoc Real.abs_sin_le_abs as "abs_sin_le_abs" in "Inequalities"

NewTheorem Real.abs_sin_le_abs
