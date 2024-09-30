import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
-- import Mathlib.Algebra.Order.Group.Abs
-- import Mathlib.Order.Filter.Basic
import Mathlib.Data.ENNReal.Basic
open Filter Set

def my_limit (c : ℝ) (f : ℝ → ℝ) : Option EReal := sorry


syntax (name := my_limit') "lim " term:40 " → " term:10 ", " term:70 " = " term:12 : term
macro_rules (kind := my_limit')
  | `(lim $x → $c, $r = $L) => `(Tendsto (fun ($x : ℝ) => ($r : ℝ)) (nhds $c) (nhds $L))


syntax (name := my_limit_del) "my_lim " term:40 " → " term:10 ", " term:70 " = " term:12 : term
macro_rules (kind := my_limit_del)
  | `(my_lim $x → $c, $r = $L) =>
  `(Tendsto (fun ($x : ℝ) => ($r : ℝ)) (nhdsWithin $c {($c)}ᶜ) (nhds $L))

-- #check lim x → 0, (x + 1) = 1

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

def HasLimit (f : ℝ → ℝ) (c L : ℝ) := Tendsto f (nhdsWithin c {c}ᶜ) (nhds L)

open Classical
noncomputable def my_limit'' (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  if h : ∃ L, HasLimit f c L then Classical.choose h else 0

lemma epsilon_delta_nhds_nhds (f : ℝ → ℝ) (c L : ℝ) :
  Tendsto f (nhds c) (nhds L) ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - L| < ε := by
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHB c) (NHB L), mem_setOf_eq]


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


lemma epsilon_delta_nhds_atTop (f : ℝ → ℝ) (c : ℝ) :
  Filter.Tendsto f (nhds c) atTop ↔
  ∀ N : ℝ, ∃ δ > 0, ∀ x, |x - c| < δ → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHB c) THB, mem_setOf, forall_true_left, mem_Ioi]


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


lemma my_limit_add_c (f g : ℝ → ℝ) (c L M : ℝ) (hL : my_lim x → c, f x = L)
  (hM : my_lim x → c, g x = M) : my_lim x → c, (f x + g x) = L + M := by exact Tendsto.add hL hM


lemma my_limit_sub_c (f g : ℝ → ℝ) (c L M : ℝ) (hL : my_lim x → c, f x = L)
  (hM : my_lim x → c, g x = M) : my_lim x → c, (f x - g x) = L - M := by exact Tendsto.sub hL hM

-- etc... let capstone students do them :)


lemma my_limit_replacement_rule (f g : ℝ → ℝ) (c L : ℝ) (hL : lim x → c, g x = L)
  (hfg : ∃ δ > 0, ∀ x, |x - c| < δ → f x = g x) : (lim x → c, f x = L) := by
  apply (epsilon_delta_nhds_nhds f c L).mpr
  intro ε h1
  rcases hfg with ⟨δ1, h2, h3⟩
  rw [epsilon_delta_nhds_nhds] at hL
  rcases hL ε h1 with ⟨δ2, h4, h5⟩
  use min δ1 δ2
  constructor
  . exact lt_min h2 h4
  . intro _ h6
    rw [h3]
    apply h5
    have := min_le_right δ1 δ2
    linarith
    have := min_le_left δ1 δ2
    linarith


lemma my_limit_replacement_rule_deleted (f g : ℝ → ℝ) (c L : ℝ)
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
