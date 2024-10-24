import Game.Lemmas.Limits.Basic
import Game.Lemmas.Limits.LimitLaws

open Filter Set Classical

-- prove basic properties of derivatives here...

def my_has_deriv (f : ℝ → ℝ) (c y : ℝ) := lim x → c, (f x - f c) / (x - c) = y

noncomputable def my_deriv (f : ℝ → ℝ) (c : ℝ) : ℝ := lim x → c, (f x - f c) / (x - c)

def my_differentiable (f : ℝ → ℝ) (c : ℝ) := HasLimAt (fun x => (f x - f c) / (x - c)) c

variable {c y y1 y2 : ℝ} {f g : ℝ → ℝ}

-- smth smth 'left' and 'right' differentiability

private lemma add_pre : (fun x => (f x - f c) / (x - c) + (g x - g c) / (x - c))
  = (fun x => ((f + g) x - (f + g) c) / (x - c)) := by
  funext
  simp only [Pi.add_apply]
  by_cases h : x - c = 0
  . rw[h]; simp only [div_zero, zero_add]
  . ring_nf

lemma my_differentiable_add (hf : my_differentiable f c) (hg : my_differentiable g c) :
  my_differentiable (f + g) c := by
  rw [my_differentiable] at *
  rw [← add_pre]
  apply HasLimAt_add
  exact hf; exact hg

lemma my_deriv_add (hf : my_differentiable f c) (hg : my_differentiable g c) :
  my_deriv (f + g) c = my_deriv f c + my_deriv g c := by
  have hfg := my_differentiable_add hf hg
  rw [my_differentiable] at *
  rcases hf with ⟨l1, hf1⟩
  rcases hg with ⟨l2, hf2⟩
  rcases hfg with ⟨l12, hfg⟩
  rw [epsilon_delta_nhds_nhds_deleted] at *
  repeat rw [my_deriv]
  rw [← add_pre, lim_add]
  rw [HasLimAt]
  use l1
  rw [epsilon_delta_nhds_nhds_deleted]
  exact hf1
  rw [HasLimAt]
  use l2
  rw [epsilon_delta_nhds_nhds_deleted]
  exact hf2

  -- etc... sub, scalar mult, product rule, quotient rule, chain rule, inverse rule
