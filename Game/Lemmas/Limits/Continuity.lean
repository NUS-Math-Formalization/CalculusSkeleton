import Game.Lemmas.Limits.Basic
open Filter Set

def my_continuous (f : ℝ → ℝ) (c : ℝ) := lim x → c, f x = f c

-- sum, diff, product, quotient, composition
