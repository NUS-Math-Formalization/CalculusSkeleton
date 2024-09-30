import Game.Lemmas.Limits.Basic

def my_has_deriv (f : ℝ → ℝ) (c y : ℝ) := my_lim x → c, ((f x - f c) / (x - c)) = y

example (c : ℝ) : my_has_deriv (fun x => x) c 1 := by
  rw [my_has_deriv]
  set f := fun (x : ℝ) => (x - c) / (x - c)
  set g := fun (_ : ℝ) => (1 : ℝ)
  apply my_limit_replacement_rule_deleted f g
  . exact tendsto_const_nhds
  . use 1
    constructor
    . norm_num
    . intro x hx
      rcases hx with ⟨hx0, _⟩
      apply div_self
      exact abs_pos.mp hx0

lemma my_deriv_add (c y1 y2: ℝ) (f g : ℝ → ℝ) (hf : my_has_deriv f c y1) (hg : my_has_deriv g c y2)
  : my_has_deriv (f + g) c (y1 + y2) := by
  rw [my_has_deriv] at *
  have : (fun x => (((f + g) x) - ((f + g) c)) / (x - c))
    = fun x => ((f x - f c) / (x - c) + (g x - g c) / (x - c)) := by
    funext; field_simp
    by_cases h : x - c = 0
    . rw [h]; simp only [div_zero]
    . apply (IsUnit.div_left_inj _).mpr
      ring_nf
      simp only [isUnit_iff_ne_zero, ne_eq]
      exact h
  rw [this]
  exact
    my_limit_add_c (fun x => (f x - f c) / (x - c)) (fun x => (g x - g c) / (x - c)) c y1 y2 hf hg

-- etc...
