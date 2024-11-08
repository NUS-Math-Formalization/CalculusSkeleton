I am designing natural language hint for Lean 4 code, as a guidance for beginners to write one line of Lean tactic, I will give you state before tactic, state after tactic, tactic used, and reference for the tactic. You should give me a concise one sentence guidance for students to write the tactic used.

# Example Input
## State before the tactic
x : ℝ
⊢ deriv (fun x => x + 1) x = 1
## Tactic used
rw [deriv_add]
## Reference
@[simp]
theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
 deriv (fun y => f y + g y) x = deriv f x + deriv g x
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
x : ℝ
⊢ deriv (fun x => Real.exp x ^ Real.exp x) x = Real.exp (x + x * Real.exp x) * (x + 1)
## Tactic used
simp_rw [← Real.exp_mul]
## Reference
theorem exp_mul (x y : ℝ) : exp (x * y) = exp x ^ y
## State after the tactic
x : ℝ
⊢ deriv (fun x => Real.exp (x * Real.exp x)) x = Real.exp (x + x * Real.exp x) * (x + 1)
