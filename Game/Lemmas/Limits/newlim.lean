import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.ENNReal.Basic

import Lean

open Real Topology Filter


noncomputable section LimDef
open Lean Elab Term Meta Syntax

-- Define the syntax category for extended neighborhoods
declare_syntax_cat enhb

-- Define the syntax for extended neighborhoods
syntax term : enhb
syntax enhb "⁺" : enhb
syntax enhb "⁻" : enhb
syntax "∞" : enhb
syntax "-∞" : enhb

instance : Coe Term (TSyntax `enhb) where
  coe s := ⟨s.raw⟩

-- Define the syntax for the limit notation
syntax:100 (name:=llimbuilder) "lim " ident " → " enhb:101 ", " term:100  (" = " enhb)? : term

open Classical in
irreducible_def flim [TopologicalSpace R] [Inhabited R] (f : α → R) (l₁ : Filter α) : R :=
  if h : ∃ L, Tendsto f l₁ (nhds L) then h.choose else default

def elabenhd : TSyntax `enhb → TermElabM (TSyntax `term) := fun C =>
        match C with
        | `(enhb|$c:term ⁺)  => `(nhdsWithin $c (Set.Ioi $c))
        | `(enhb|$c:term ⁻)  => `(nhdsWithin $c (Set.Iio $c))
        | `(enhb|$c:term)  => `(nhdsWithin $c {($c)}ᶜ)
        | `(enhb|∞) => `(atTop)
        | `(enhb|-∞) => `(atBot)
        | _ => none

def elabenhd_rhs : TSyntax `enhb → TermElabM (TSyntax `term) := fun C =>
        match C with
        | `(enhb|$c:term)  => `(nhds $c)
        | `(enhb|∞) => `(atTop)
        | `(enhb|-∞) => `(atBot)
        | _ => none

@[term_elab llimbuilder]
def elabLimBuilder : TermElab := fun stx et? => do
  let res : TSyntax `term ← do match stx with
    | `(lim $x:ident → $C:enhb, $f:term = $y:enhb) => do
      let nb : TSyntax `term ← do elabenhd C
      let ff : TSyntax `term ← do `(fun $x => $f)
      let y : TSyntax `term ← do elabenhd_rhs  y
      `(Tendsto ($ff) ($nb) ($y))
    | `(lim $x:ident → $C:enhb, $f:term) => do
      let nb : TSyntax `term ← do elabenhd C
      let ff : TSyntax `term ← do `(fun $x => $f)
      `(flim ($ff) ($nb))
    | _ => none
  elabTerm (res) et?

open Lean Lean.PrettyPrinter.Delaborator
--#check flim

def delabenhd : TSyntax `term → DelabM (TSyntax `enhb) := fun C =>
      match C with
        | `(𝓝[≠] $a) => `(enhb|$a)
        | `(𝓝[>] $a) => `(enhb|$a ⁺)
        | `(𝓝[<] $a) => `(enhb|$a ⁻)
        | `(nhdWithin $a (Set.Ioi $b)) => `(enhb|$a ⁺)
        | `(nhdWithin $a (Set.Iio $b)) => `(enhb|$a ⁻)
        | `(nhdWithin $a {$a}ᶜ) => `(enhb|a.raw)
        | `(atTop) => `(enhb|∞)
        | `(atBot) => `(enhb|-∞)
        | a => `(enhb|($a))

def delabenhdrhs : TSyntax `term → DelabM (TSyntax `enhb) := fun C =>
      match C with
        | `(atTop) => `(enhb|∞)
        | `(atBot) => `(enhb|-∞)
        | `(𝓝 $a) => `(enhb|$a)
        | `(nhds $a) => `(enhb|$a)
        | a => `(enhb|a)


@[delab app.flim]
def delabflim : Delab := whenPPOption Lean.getPPNotation <| withOverApp 6 do
  let #[_,_,_,_,ff,nb] := (← SubExpr.getExpr).getAppArgs | failure
  --dbg_trace f!"{ff}, aaaa {nb}"
  let ff ←  Lean.PrettyPrinter.delab ff
  let nb ←  Lean.PrettyPrinter.delab nb
  let nb ← delabenhd nb
  match ff with
  | `(fun $x:ident => $body) => `(lim $(x) → $nb, $body)
  | _ => none

#check Tendsto

#check flim


@[delab app.Filter.Tendsto]
def delabTendsto : Delab := whenPPOption Lean.getPPNotation  <| withOverApp 5 do
  let #[_,_,ff,nb,L] := (← SubExpr.getExpr).getAppArgs | failure
  let ff := (← Lean.PrettyPrinter.delab (ff))
  let nb  ←  delabenhd <| (← Lean.PrettyPrinter.delab (nb))
  let L ←  delabenhdrhs (← Lean.PrettyPrinter.delab (L))
  match ff with
  | `(fun $x:ident => $body) => `(lim $(x) → $nb, $body = $L )
  | _ => none


open Classical

end LimDef

variable (c : ℝ)
variable (f : ℝ → ℝ)
variable (g : ℕ → ℝ)
variable (h : ℕ → ℕ)

#check (lim x→∞, f x)
#check (lim x→-∞, f x)
#check (lim x → ∞, f x) + (lim x → 0⁺,  x) = 0
#check lim x → 0, f x + lim x → ∞, h x + (lim x → ∞, g x) = 0

#check lim x → ∞, f x = ∞
#check lim x → 100⁺, f x = 100
#check lim x → c⁻, f x = -0
#check lim x → ∞, g x = -∞


noncomputable section LimLemmas
open Filter Set Classical Topology

-- to fix: change to functions defined on intervals
def HasLimAt (f : ℝ → ℝ) (c : ℝ) := ∃ (l₂ : ℝ), Tendsto f (nhdsWithin c {c}ᶜ) (nhds l₂)

def HasLeftLimAt (f : ℝ → ℝ) (c : ℝ) := ∃ (l₂ : ℝ), Tendsto f (nhdsWithin c (Set.Iio c)) (nhds l₂)

def HasRightLimAt (f : ℝ → ℝ) (c : ℝ) := ∃ (l₂ : ℝ), Tendsto f (nhdsWithin c (Set.Ioi c)) (nhds l₂)

def HasLimAtTop (f : ℝ → ℝ) := ∃ (l₂ : ℝ), Tendsto f atTop (nhds l₂)



variable {c L : ℝ} {f : ℝ → ℝ}

lemma nhds_basis_abs_sub_lt_deleted (a : ℝ) :
    (nhdsWithin a {a}ᶜ).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { b | 0 < |b - a| ∧ |b - a| < ε }
    := by
  have : (fun ε => { b | 0 < |b - a| ∧ |b - a| < ε }) = (fun ε => {b | |b - a| < ε} ∩ {a}ᶜ) := by
    funext ε; ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_compl_iff, mem_singleton_iff, abs_pos, ne_eq]
    rw [and_comm]
    simp only [and_congr_right_iff]
    intro
    exact sub_ne_zero
  rw [this]
  apply nhdsWithin_hasBasis (nhds_basis_abs_sub_lt (α := ℝ) a) ({a}ᶜ)


lemma epsilon_delta_nhds_nhds_deleted : Tendsto f (nhdsWithin c {c}ᶜ) (nhds L) ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → |f x - L| < ε := by
  have NHBD := nhds_basis_abs_sub_lt_deleted c
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHBD) (NHB L), mem_setOf_eq]

lemma lim_def_fin_fin (h : ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → |f x - L| < ε) :
  (lim x → c, f x) = L := by
  rw [← epsilon_delta_nhds_nhds_deleted] at h
  have hL : ∃ L, Tendsto f (nhdsWithin c {c}ᶜ) (nhds L) := ⟨L, h⟩
  rw [flim, dif_pos hL]
  exact tendsto_nhds_unique hL.choose_spec h



lemma epsilon_delta_nhds_nhds_left : Tendsto f (nhdsWithin c (Set.Iio c)) (nhds L) ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < c - x ∧ c - x < δ → |f x - L| < ε := by
  have : ∃ b, b < c := by use (c - 1); norm_num
  have NHBL := nhdsWithin_Iio_basis' (α := ℝ) this
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff (NHBL) (NHB L), mem_setOf]
  simp only [mem_Ioo, and_imp, gt_iff_lt, sub_pos]
  constructor
  . intro h ε εpos
    have : ∃ ia < c, ∀ x, ia < x → x < c → |f x - L| < ε := by apply h; exact εpos
    rcases this with ⟨ia, iapos, iah⟩
    use (c - ia)
    constructor
    . linarith
    . intro h₁ h₂ h₃
      apply iah; linarith; linarith
  . intro h ε εpos
    have : ∃ δ, 0 < δ ∧ (∀ x, x < c → c - x < δ → |f x - L| < ε) := by apply h; exact εpos
    rcases this with ⟨δ, δpos, δh⟩
    use (c - δ)
    constructor
    . linarith
    . intro u u₁ u₂
      apply δh; linarith; linarith


lemma left_lim_def_fin_fin (h : ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < c - x ∧ c - x < δ → |f x - L| < ε) :
  (lim x → c⁻, f x) = L := by
  rw [← epsilon_delta_nhds_nhds_left] at h
  have hL : ∃ L, Tendsto f (nhdsWithin c (Set.Iio c)) (nhds L) := ⟨L, h⟩
  rw [flim, dif_pos hL]
  exact tendsto_nhds_unique hL.choose_spec h


lemma epsilon_delta_nhds_nhds_right : Tendsto f (nhdsWithin c (Set.Ioi c)) (nhds L) ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < x - c ∧ x - c < δ → |f x - L| < ε := by sorry


lemma right_lim_def_fin_fin (h : ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < x - c ∧ x - c < δ → |f x - L| < ε) :
  lim x → c⁺, f x = L := by sorry


lemma epsilon_delta_atTop_nhds : Tendsto f atTop (nhds L) ↔
  ∀ ε > 0, ∃ N, ∀ x, x > N → |f x - L| < ε := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHB := nhds_basis_abs_sub_lt (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB (NHB L), mem_Ioi, true_and, mem_setOf_eq]


lemma lim_def_inf_fin (h : ∀ ε > 0, ∃ N, ∀ x, x > N → |f x - L| < ε) :
  (lim x → ∞, f x) = L := by
  rw [← epsilon_delta_atTop_nhds] at h
  have hL : ∃ L, Tendsto f atTop (nhds L) := ⟨L, h⟩
  rw [flim, dif_pos hL]
  exact tendsto_nhds_unique hL.choose_spec h


lemma epsilon_delta_nhds_atTop_deleted : Tendsto f (nhdsWithin c {c}ᶜ) atTop ↔
  ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  have NHBD := nhds_basis_abs_sub_lt_deleted c
  simp_rw [HasBasis.tendsto_iff NHBD THB, mem_setOf, forall_true_left, mem_Ioi]


lemma lim_def_fin_inf (h : ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → f x > N ) :
  lim x → c, f x = ∞ := epsilon_delta_nhds_atTop_deleted.mpr h


lemma epsilon_delta_nhds_atTop_left : Tendsto f (nhdsWithin c (Set.Iio c)) atTop ↔
  ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < c - x ∧ c - x < δ → f x > N := by sorry

-- Clarence: I think this should be flipped and iff'ed
lemma left_lim_def_fin_inf (h : ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < c - x ∧ c - x < δ → f x > N) :
  lim x → c⁻, f x = ∞ := by sorry


lemma epsilon_delta_nhds_atTop_right : Tendsto f (nhdsWithin c (Set.Ioi c)) atTop ↔
  ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < x - c ∧ x - c < δ → f x > N := by sorry


lemma right_lim_def_fin_inf (h : ∀ N : ℝ, ∃ δ > 0, ∀ x, 0 < x - c ∧ x - c < δ → f x > N) :
  lim x → c⁺, f x = ∞ := by sorry


lemma epsilon_delta_atTop_atTop : Tendsto f atTop atTop ↔
  ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N := by
  have THB := atTop_basis_Ioi (α := ℝ)
  simp_rw [HasBasis.tendsto_iff THB THB, true_and, forall_true_left, mem_Ioi]


lemma lim_def_inf_inf (h : ∀ N : ℝ, ∃ M, ∀ x, x > M → f x > N) :
  lim x → ∞, f x = ∞ := epsilon_delta_atTop_atTop.mpr h


end LimLemmas
