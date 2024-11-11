import Lean
import LLMlean.API
import Lean.Meta.Tactic.TryThis
open Lean Elab Meta Parser PrettyPrinter Tactic

-- def getNextTactic (pos : String.pos) : Syntax :

def mkPrompt (goalBefore currentTactic goalAfter : String) : List String :=
  let p1 := "I am designing natural language hint for Lean 4 code, as a guidance for beginners to write one line of Lean tactic, I will give you state before the tactic, state after the tactic, and tactic used. Please offer me a hint for the tactic used. Any latex formula should be wrapped in single dollar sign.
# Example Input 1
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
# Example Output 1
Rewrite `deriv_add` to distribute the derivation. Note that you will need to show the differentiability for each summand to make this lemma work.

# Example Input 2
## State before the tactic
x : ℝ
DenominatorNotZero : x ^ 4 - 2 ≠ 0
⊢ (((fun x => ↑3 * x ^ (3 - 1)) x + (fun x => 1) x) * (x ^ 4 - 2) - (x ^ 3 + x) * deriv (fun x => x ^ 4 - 2) x) / (x ^ 4 - 2) ^ 2 =
  ((3 * x ^ 2 + 1) * (x ^ 4 - 2) - (x ^ 3 + x) * (4 * x ^ 3)) / (x ^ 4 - 2) ^ 2
## Tactic used
rw [deriv_sub]
## State after the tactic
x : ℝ
DenominatorNotZero : x ^ 4 - 2 ≠ 0
⊢ (((fun x => ↑3 * x ^ (3 - 1)) x + (fun x => 1) x) * (x ^ 4 - 2) - (x ^ 3 + x) * (deriv (fun x => x ^ 4) x - deriv (fun x => 2) x)) / (x ^ 4 - 2) ^ 2 =
  ((3 * x ^ 2 + 1) * (x ^ 4 - 2) - (x ^ 3 + x) * (4 * x ^ 3)) / (x ^ 4 - 2) ^ 2
# Example Output 2
Our current goal is $ \\frac\\{(3 x ^ 2 + 1) (x ^ 4 - 2) - (x ^ 3 + x) (x ^ 4 - 2) ^ \\prime}\\{(x ^ 4 - 2) ^ 2}= \\frac\\{((3 x ^ 2 + 1) (x ^ 4 - 2) - (x ^ 3 + x) (4 x ^ 3))}\\{(x ^ 4 - 2) ^ 2}$. Let's start by rewriting with `deriv_sub` to expand the only derivative we have here.

# Example Input 3
## State before the tactic
x : ℝ
⊢ deriv (fun x => Real.exp x ^ Real.exp x) x = Real.exp (x + x * Real.exp x) * (x + 1)
## Tactic used
simp_rw [← Real.exp_mul]
## State after the tactic
x : ℝ
⊢ deriv (fun x => Real.exp (x * Real.exp x)) x = Real.exp (x + x * Real.exp x) * (x + 1)
# Example Output 3
To solve the goal involving the derivative of an exponential function, use `simp_rw [Real.exp_mul]` to rewrite the expression. This will help transform $ \\exp(x) ^ \\exp(x) $ into $ \\exp(x \\cdot \\exp(x)) $, making it easier to differentiate.

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


elab "Hint? " currentTactic:tactic : tactic => withMainContext do
  let goalBefore ← Tactic.getMainGoal
  -- logInfo m!"{← ppGoal goalBefore}"
  Tactic.evalTactic currentTactic
  -- logInfo m!"{currentTactic}"
  let goalAfter ← Tactic.getMainGoal
  -- logInfo m!"{← ppGoal goalAfter}"
  let prompt := mkPrompt
    (toString (← ppGoal goalBefore))
    (toString currentTactic)
    (toString (← ppGoal goalAfter))
  let generationOption : GenerationOptions :=
    {temperature := 0.7, numSamples := 1, «stop» := []}
  let results ← tacticGenerationOpenAI "" prompt (← getAPI) generationOption
  let (hint, _) := results[0]!
  let hint := hint.replace "\\" "\\\\"
  logInfo m!"{hint}"
  let ref ← getRef
  TryThis.addSuggestion ref[0] (toSuggestion hint)
