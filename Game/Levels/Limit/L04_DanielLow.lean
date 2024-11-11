import Game.Metadata
import Mathlib
import Game.Lemmas.Limits.Basic

World "Limit"

Level 4
lemma h0 (x:ℝ): (-8*x + 7- -9) =16-8*x:= by
  ring
lemma hk :|-8|=8:= by
  exact rfl

open Topology
-- use the ε, δ definition to prove that lim_{x → 2} (-8x + 7) = -9
Statement:  lim x → 2, (-8*x + 7) = -9 := by
  Hint "To show that the limit of $-8x + 7$ as $x$ approaches 2 is $-9$, we can use the definition of a limit. Apply the `lim_def_fin_fin` lemma, which requires us to prove the $\\epsilon$-$\\delta$ condition for limits."
  apply lim_def_fin_fin
  Hint "To begin proving the universally quantified statement, introduce $\\varepsilon$ and the condition $\\varepsilon > 0$ into the context using `intro`. This step sets up the framework for finding a suitable $\\delta$ that satisfies the given conditions."
  intro ε hε
  Hint "To tackle the goal of finding a suitable $ \\delta $ for the given $\\varepsilon$ in your limit definition, use the `use` tactic to specify $ \\delta = \\frac\{\\varepsilon}{8} $. This choice of $ \\delta $ helps simplify the subsequent inequality, making it easier to show that the condition holds for all $ x $ within the specified range."
  use ε/8
  Hint "To begin proving the conjunction, use the `constructor` tactic. This tactic will break down the goal into two separate subgoals, allowing you to address each part of the conjunction individually."
  constructor
  linarith
  intro x hx
  have h1 (x:ℝ):|-8 * x + 7 - -9|=|16-8*x|:= by ring_nf
  have h2 (x:ℝ):|16-8*x|=|(-8)*(-2)-8*x|:= by ring_nf
  have h3 (x:ℝ):|(-8)*(-2)-8*x|=|(-8)*(-2+x)|:= by ring_nf
  have h4 (x:ℝ):|(-8)*(-2+x)| = |-8| * |x-2| := by rw[abs_mul,add_comm, ← sub_eq_add_neg]
  have h5 (x:ℝ):|-8| * |x-2|= 8* |x-2| := by simp
  suffices h6 :|-8 * x + 7 - -9| = 8 * |x-2| by
    rw [h6]
    linarith
  rw [h1, h2, h3, h4, h5]


NewTactic ring_nf
