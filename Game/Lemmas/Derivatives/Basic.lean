import Game.Lemmas.Limits.Basic
import Game.Lemmas.Limits.LimitLaws

-- prove basic properties of derivatives here...

def my_has_deriv (f : ℝ → ℝ) (c y : ℝ) := my_lim x → c, ((f x - f c) / (x - c)) = y

open Classical
noncomputable def my_deriv (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  if h : ∃ y, my_has_deriv f c y then Classical.choose h else 0

noncomputable def my_differentiable (f : ℝ → ℝ) (c : ℝ) :=
  ∃ y , my_has_deriv f c y

lemma my_deriv_unique (f : ℝ → ℝ) (c y1 y2 : ℝ)
  (h1 : my_has_deriv f c y1) (h2 : my_has_deriv f c y2) : y1 = y2 := by
  rw [my_has_deriv] at *
  set g := (fun (x : ℝ) => (f x - f c) / (x - c))
  apply my_limit_nhds_unique g c
  exact h1
  exact h2

lemma my_deriv_eq (f : ℝ → ℝ) (x y : ℝ)
  (h : my_has_deriv f x y) : my_deriv f x = y := by
  apply my_deriv_unique f x
  . sorry
  . exact h

lemma my_has_deriv_add {c y1 y2: ℝ} (f g : ℝ → ℝ) (hf : my_has_deriv f c y1)
  (hg : my_has_deriv g c y2) : my_has_deriv (f + g) c (y1 + y2) := by
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

lemma my_deriv_add (f g : ℝ → ℝ) {c : ℝ} (hf : my_differentiable f c)
  (hg : my_differentiable g c) : my_deriv (f + g) c = my_deriv f c + my_deriv g c := by
  set y1 := my_deriv f c
  set y2 := my_deriv g c
  apply my_deriv_eq
  sorry
