import Game.Metadata
-- import Mathlib
import Game.Lemmas.Limits.Basic
import Game.Lemmas.Inequalities
--import Game.Lemmas.Limits.delib

World "Limit"

Level 2


open BigOperators Real Topology


namespace CGame

variable (G :Type*) [Group G]

Statement (e e' : G) (h1:∀ g :G,  e*g = g) (h2: ∀ g :G, g * e=g) (h3:∀ g :G,  e'*g = g) (h4: ∀ g :G, g * e'=g) : e=e'  := by
  Hint "Use `h1` "
  rw [<- h1 e']
  Hint "Use `h4` "
  rw [h4 e]

end CGame
