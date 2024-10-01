import Game.Lemmas.Limits.Basic
open Filter Set

lemma my_limit_add_c (f g : ℝ → ℝ) (c L M : ℝ) (hL : my_lim x → c, f x = L)
  (hM : my_lim x → c, g x = M) : my_lim x → c, (f x + g x) = L + M := by exact Tendsto.add hL hM


lemma my_limit_sub_c (f g : ℝ → ℝ) (c L M : ℝ) (hL : my_lim x → c, f x = L)
  (hM : my_lim x → c, g x = M) : my_lim x → c, (f x - g x) = L - M := by exact Tendsto.sub hL hM

-- etc... (product, quotient, composition) let capstone students do them :)

lemma my_limit_replacement_rule (f g : ℝ → ℝ) (c L : ℝ)
  (hL : my_lim x → c, g x = L)
  (hfg : ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → f x = g x) :
  my_lim x → c, f x = L := by
  apply (epsilon_delta_nhds_nhds_deleted f c L).mpr
  intro ε h1
  rcases hfg with ⟨δ1, h2, h3⟩
  rw [epsilon_delta_nhds_nhds_deleted] at hL
  rcases hL ε h1 with ⟨δ2, h4, h5⟩
  use min δ1 δ2
  constructor
  . exact lt_min h2 h4
  . intro _ h6
    rw [h3]
    apply h5
    have := min_le_right δ1 δ2
    constructor; linarith; linarith
    have := min_le_left δ1 δ2
    constructor; linarith; linarith
