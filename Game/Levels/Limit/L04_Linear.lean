import Game.Metadata
import Game.Lemmas.Limits.Basic

open Topology

Introduction "This level is about using the ε, δ definition to prove that lim_{x → 2} (-8x + 7) = -9. This level is done by Daniel Low."

World "Limit"

Level 4

Statement:  lim x → 2, (-8 * x + 7) = -9 := by
  apply lim_def_fin_fin
  intro ε hε
  use ε/8
  constructor
  linarith
  intro x hx
  have h1 (x:ℝ):|-8 * x + 7 - -9|=|16-8*x|:= by ring_nf
  have h2 (x:ℝ):|16-8*x|=|(-8)*(-2)-8*x|:= by ring_nf
  have h3 (x:ℝ):|(-8)*(-2)-8*x|=|(-8)*(-2+x)|:=by ring_nf
  have h4 (x:ℝ):|(-8)*(-2+x)| = |-8| * |x-2| :=by rw[abs_mul,add_comm, ← sub_eq_add_neg]
  have h5 (x:ℝ):|-8| * |x-2|= 8* |x-2| := by simp
  have h6 (x:ℝ):|-8 * x + 7 - -9| = 8* |x-2| := by rw[h1, h2, h3,h4,h5]
  rw[h6]
  linarith

NewTactic ring_nf
