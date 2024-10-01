import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
-- import Mathlib.Algebra.Order.Group.Abs
-- import Mathlib.Order.Filter.Basic
import Mathlib.Data.ENNReal.Basic
open Filter Set

syntax (name := my_limit_del) "my_lim " term:40 " → " term:10 ", " term:70 " = " term:12 : term
macro_rules (kind := my_limit_del)
  | `(my_lim $x → $c, $r = $L) =>
  `(Tendsto (fun ($x : ℝ) => ($r : ℝ)) (nhdsWithin $c {($c)}ᶜ) (nhds $L))

-- #check lim x → 0, (x + 1) = 1

-- to do limits we need to use deleted neighbourhoods
lemma nhds_basis_abs_sub_lt_deleted (a : ℝ) :
    (nhdsWithin a {a}ᶜ).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { b | 0 < |b - a| ∧ |b - a| < ε }
    := by
  have : (fun ε => { b | 0 < |b - a| ∧ |b - a| < ε }) = (fun ε => {b | |b - a| < ε} ∩ {a}ᶜ) := by
    funext ε
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_compl_iff, mem_singleton_iff, abs_pos, ne_eq]
    rw [and_comm]
    simp only [and_congr_right_iff]
    intro _
    exact sub_ne_zero
  rw [this]
  apply nhdsWithin_hasBasis (nhds_basis_abs_sub_lt (α := ℝ) a) ({a}ᶜ)

-- gotta prove uniqueness of limits in order to allow limit manipulations (lul we simply model our
-- code after mathlib)

def my_has_limit_nhds (f : ℝ → ℝ) (c L : ℝ) := Tendsto f (nhdsWithin c {c}ᶜ) (nhds L)

-- infinite limits here...

open Classical
noncomputable def my_limit_nhds (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  if h : ∃ L, my_has_limit_nhds f c L then Classical.choose h else 0

lemma my_limit_nhds_unique (f : ℝ → ℝ) (c L M : ℝ) (hL: Tendsto f (nhdsWithin c {c}ᶜ) (nhds L))
  (hM : Tendsto f (nhdsWithin c {c}ᶜ) (nhds M)) : L = M := by sorry

lemma my_limit_nhds_eq (f : ℝ → ℝ) (c L : ℝ) (h : my_has_limit_nhds f c L) :
  my_limit_nhds f c = L := by sorry

lemma my_limit_atTop_unique (f : ℝ → ℝ) (c L M : ℝ) (hL: Tendsto f atTop (nhds L))
  (hM : Tendsto f atTop (nhds M)) : L = M := by sorry

-- etc...


-- equivalence between epsilon delta definition and filter definition
lemma epsilon_delta_nhds_nhds_deleted (f : ℝ → ℝ) (c L : ℝ) :
  Tendsto f (nhdsWithin c {c}ᶜ) (nhds L) ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → |f x - L| < ε := by
  have NHBD := nhds_basis_abs_sub_lt_deleted c
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHBD) (NHB L), mem_setOf_eq]


lemma epsilon_delta_atTop_nhds (f : ℝ → ℝ) (L : ℝ) :
  Tendsto f atTop (nhds L) ↔
  ∀ ε > 0, ∃ N, ∀ x, x > N → |f x - L| < ε := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB (NHB L), mem_Ioi, true_and, mem_setOf_eq]


lemma epsilon_delta_nhds_atTop_deleted (f : ℝ → ℝ) (c : ℝ) :
  Filter.Tendsto f (nhdsWithin c {c}ᶜ) atTop ↔
  ∀ N : ℝ, ∃ δ > 0, ∀ x,  0 < |x - c| ∧ |x - c| < δ → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHBD := nhds_basis_abs_sub_lt_deleted c
  simp_rw [HasBasis.tendsto_iff (NHBD) THB, mem_setOf, forall_true_left, mem_Ioi]


lemma epsilon_delta_atTop_atTop (f : ℝ → ℝ) :
  Filter.Tendsto f atTop atTop ↔
  ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB THB, true_and, forall_true_left, mem_Ioi]


-- there's still one-sided limits to handle lol
-- use the following notations, again need punctured neighbourhoods
-- `𝓝[<] x`: the filter `nhdsWithin x (Set.Iio x)` of punctured left-neighborhoods of `x`;
-- `𝓝[>] x`: the filter `nhdsWithin x (Set.Ioi x)` of punctured right-neighborhoods of `x`;
