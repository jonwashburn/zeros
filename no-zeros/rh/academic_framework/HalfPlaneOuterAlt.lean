import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import rh.academic_framework.CompletedXi
import rh.RS.PoissonAI
import rh.RS.Det2Outer
import rh.RS.Cayley

/-!
Half‑plane outers (alternative, lightweight rewrite)

This is an alternative interface module, kept disjoint from the existing
`HalfPlaneOuter` module. It focuses on a minimal, robust API that downstream
files can swap to with import changes, while avoiding heavy analytic proofs.

Key components provided here:
- Right half‑plane domain `Ω_alt` and boundary parametrization `boundary_alt`.
- A Prop‑level outer interface (`OuterWitnessAlt`, `IsOuterAlt`).
- Statement‑level boundary modulus matching predicates.
- A Poisson kernel `poissonKernel_alt`, transport operator `P_alt`, and the
  core positivity transport from boundary a.e. nonnegativity.
- A representation record and its transport corollaries (global and subset).
- Pinch field wrappers mirroring the RS usage points, under Alt names.

This file intentionally leaves existence/constructive parts at the Prop level
to remain decoupled from specific analytic constructions.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Complex

namespace RH
namespace AcademicFramework
namespace HalfPlaneOuterAlt

/-! ## Geometry: domain and boundary -/

/- The right half‑plane Ω := {Re s > 1/2}. -/ 
def Ω_alt : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

local notation "Ω_alt" => Ω_alt

@[simp] lemma mem_Ω_alt_iff {z : ℂ} : z ∈ Ω_alt ↔ (1/2 : ℝ) < z.re := Iff.rfl

/- Boundary parametrization of the line Re s = 1/2. -/
@[simp] def boundary_alt (t : ℝ) : ℂ := (1 / 2 : ℝ) + Complex.I * (t : ℂ)

@[simp] lemma boundary_alt_mk_eq (t : ℝ) : boundary_alt t = Complex.mk (1/2) t := by
  refine Complex.ext ?hre ?him
  · simp [boundary_alt]
  · simp [boundary_alt]

/-! ## Outer interface (Prop‑level) -/

structure OuterWitnessAlt (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω_alt
  nonzero  : ∀ {s}, s ∈ Ω_alt → O s ≠ 0

def IsOuterAlt (O : ℂ → ℂ) : Prop := ∃ _W : OuterWitnessAlt O, True

/- Statement‑level boundary modulus equality along Re s = 1/2. -/
def BoundaryModulusEqAlt (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, Complex.abs (O (boundary_alt t)) = Complex.abs (F (boundary_alt t))

/- Existence of an outer with prescribed boundary modulus (Prop‑level). -/
def ExistsOuterWithBoundaryModulusAlt (F : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, IsOuterAlt O ∧ BoundaryModulusEqAlt O F

/- Specialization: boundary modulus for det2/ξ_ext. -/
open RH.AcademicFramework.CompletedXi in
def ExistsOuterWithModulus_det2_over_xi_ext_Alt (det2 : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, OuterWitnessAlt O ∧
    BoundaryModulusEqAlt O (fun s => det2 s / riemannXi_ext s)

/-! ## BMO boundary data interface (Prop‑level stubs) -/

@[simp] def BMO_on_ℝ_Alt (_u : ℝ → ℝ) : Prop := True

@[simp] def IsBoundaryLogModulusOfAlt (u : ℝ → ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, u t = Real.log (Complex.abs (F (boundary_alt t)))

def PoissonOuterFromBMOAlt (u : ℝ → ℝ) (F : ℂ → ℂ) : Prop :=
  BMO_on_ℝ_Alt u ∧ IsBoundaryLogModulusOfAlt u F →
    ExistsOuterWithBoundaryModulusAlt F

open RH.AcademicFramework.CompletedXi in
def PoissonOuter_det2_over_xi_ext_Alt (det2 : ℂ → ℂ) : Prop :=
  let F := fun s => det2 s / riemannXi_ext s
  ∀ u : ℝ → ℝ, IsBoundaryLogModulusOfAlt u F ∧ BMO_on_ℝ_Alt u →
    ExistsOuterWithModulus_det2_over_xi_ext_Alt det2

/-! ## Poisson kernel and transport -/

/- Poisson kernel for the right half‑plane `Re z > 1/2` (normalized to mass 1). -/
@[simp] def poissonKernel_alt (z : ℂ) (t : ℝ) : ℝ :=
  (1 / Real.pi) * ((z.re - (1/2 : ℝ)) / ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2))

lemma poissonKernel_alt_nonneg {z : ℂ} (hz : (1/2 : ℝ) < z.re) (t : ℝ) :
    0 ≤ poissonKernel_alt z t := by
  unfold poissonKernel_alt
  have hzpos : 0 < z.re - (1/2 : ℝ) := sub_pos.mpr hz
  have hz0 : 0 ≤ z.re - (1/2 : ℝ) := le_of_lt hzpos
  have hden : 0 ≤ (z.re - (1/2 : ℝ))^2 + (t - z.im)^2 := by
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfrac : 0 ≤ (z.re - (1/2 : ℝ)) / ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2) :=
    div_nonneg hz0 hden
  have hπ : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt Real.pi_pos)
  exact mul_nonneg hπ hfrac

/- Boundary→interior transport operator. -/
@[simp] def P_alt (u : ℝ → ℝ) (z : ℂ) : ℝ := ∫ t : ℝ, u t * poissonKernel_alt z t

/- Boundary nonnegativity predicate on `Re = 1/2`. -/
def PPlus_alt (F : ℂ → ℂ) : Prop :=
  (∀ᵐ t : ℝ, 0 ≤ (F (boundary_alt t)).re)

lemma P_alt_nonneg_of_ae_nonneg
    {u : ℝ → ℝ}
  (hInt : ∀ {z : ℂ}, z ∈ Ω_alt → Integrable (fun t : ℝ => u t * poissonKernel_alt z t))
    (hu_nonneg : ∀ᵐ t : ℝ, 0 ≤ u t) :
    ∀ ⦃z : ℂ⦄, z ∈ Ω_alt → 0 ≤ P_alt u z := by
  intro z hz
  have hzRe : (1/2 : ℝ) < z.re := (mem_Ω_alt_iff).1 hz
  have hker_nonneg : 0 ≤ᵐ[volume] fun t : ℝ => poissonKernel_alt z t := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    exact poissonKernel_alt_nonneg hzRe t
  have hprod_nonneg : 0 ≤ᵐ[volume] fun t : ℝ => u t * poissonKernel_alt z t := by
    refine ((hu_nonneg).and hker_nonneg).mono ?_
    intro t ht; exact mul_nonneg ht.1 ht.2
  have _hInt : Integrable (fun t : ℝ => u t * poissonKernel_alt z t) := hInt (by exact hz)
  have hnonneg : 0 ≤ ∫ t, u t * poissonKernel_alt z t :=
    integral_nonneg_of_ae (μ := volume) hprod_nonneg
  simpa [P_alt] using hnonneg

/- Representation record: assumes analyticity, integrability of the boundary kernel
weighted trace, and the Poisson real‑part identity. -/
structure HasHalfPlanePoissonRepresentationAlt (F : ℂ → ℂ) : Prop :=
  (analytic : AnalyticOn ℂ F Ω_alt)
  (integrable : ∀ z ∈ Ω_alt, Integrable (fun t : ℝ => (F (boundary_alt t)).re * poissonKernel_alt z t))
  (re_eq : ∀ z ∈ Ω_alt, (F z).re = P_alt (fun t : ℝ => (F (boundary_alt t)).re) z)

theorem HasHalfPlanePoissonTransportAlt
    {F : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentationAlt F) :
    PPlus_alt F → ∀ ⦃z : ℂ⦄, z ∈ Ω_alt → 0 ≤ (F z).re := by
  intro hBoundary z hz
  have hBoundary' : ∀ᵐ t : ℝ, 0 ≤ (F (boundary_alt t)).re := hBoundary
  have hpos :=
    P_alt_nonneg_of_ae_nonneg
      (u := fun t : ℝ => (F (boundary_alt t)).re)
      (hInt := by intro w hw; exact hRep.integrable w hw)
      (hu_nonneg := hBoundary')
      hz
  simpa [hRep.re_eq z hz] using hpos

theorem HasHalfPlanePoissonTransportAlt_re
    {F : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentationAlt F) :
    PPlus_alt F → ∀ z : ℂ, z.re > (1/2 : ℝ) → 0 ≤ (F z).re := by
  intro hP z hz
  have h := HasHalfPlanePoissonTransportAlt (F := F) hRep hP
  have hz' : z ∈ Ω_alt := (mem_Ω_alt_iff).2 hz
  exact h hz'

/-! ## Boundary Poisson approximate-identity (statement-level) -/

open RH.RS in
def BoundaryPoissonAI_Alt (F : ℂ → ℂ) : Prop :=
  ∀ᵐ x : ℝ,
    Filter.Tendsto (fun b : ℝ => poissonSmooth F b x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (boundaryRe F x))

def boundaryPoissonAI_from_rep_Alt (F : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonRepresentationAlt F → BoundaryPoissonAI_Alt F

/-! ## Pinch wrappers -/

open RH.AcademicFramework.CompletedXi in
@[simp] def F_pinch_alt (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (2 : ℂ) * RH.RS.J_pinch det2 O z

theorem HasHalfPlanePoissonTransportAlt_Jpinch
    {det2 O : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentationAlt (F_pinch_alt det2 O)) :
    PPlus_alt (F_pinch_alt det2 O) →
      ∀ ⦃z : ℂ⦄, z ∈ Ω_alt → 0 ≤ ((F_pinch_alt det2 O) z).re := by
  intro hP z hz
  exact HasHalfPlanePoissonTransportAlt (F := F_pinch_alt det2 O) hRep hP hz

theorem HasHalfPlanePoissonTransportAlt_Jpinch_re
    {det2 O : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentationAlt (F_pinch_alt det2 O)) :
    PPlus_alt (F_pinch_alt det2 O) →
      ∀ z : ℂ, z.re > (1/2 : ℝ) → 0 ≤ ((F_pinch_alt det2 O) z).re := by
  intro hP z hz
  have h := HasHalfPlanePoissonTransportAlt_Jpinch (det2 := det2) (O := O) hRep hP
  have hz' : z ∈ Ω_alt := (mem_Ω_alt_iff).2 hz
  exact h hz'

/-! ## Subset-restricted representation and transport -/

structure HasHalfPlanePoissonRepresentationOnAlt (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  (subset_Ω : S ⊆ Ω_alt)
  (analytic : AnalyticOn ℂ F S)
  (integrable : ∀ z ∈ S, Integrable (fun t : ℝ => (F (boundary_alt t)).re * poissonKernel_alt z t))
  (re_eq : ∀ z ∈ S, (F z).re = P_alt (fun t : ℝ => (F (boundary_alt t)).re) z)

theorem HasHalfPlanePoissonTransportAlt_on
    {F : ℂ → ℂ} {S : Set ℂ}
    (hRep : HasHalfPlanePoissonRepresentationOnAlt F S) :
    PPlus_alt F → ∀ z ∈ S, 0 ≤ (F z).re := by
  intro hBoundary z hzS
  have hBoundary' : ∀ᵐ t : ℝ, 0 ≤ (F (boundary_alt t)).re := hBoundary
  have hzΩ : z ∈ Ω_alt := hRep.subset_Ω hzS
  have hzRe : (1/2 : ℝ) < z.re := (mem_Ω_alt_iff).1 hzΩ
  have hker_nonneg : 0 ≤ᵐ[volume] fun t : ℝ => poissonKernel_alt z t := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    exact poissonKernel_alt_nonneg hzRe t
  have hprod : 0 ≤ᵐ[volume] fun t : ℝ => (F (boundary_alt t)).re * poissonKernel_alt z t := by
    exact ((hBoundary').and hker_nonneg).mono (by intro t ht; exact mul_nonneg ht.1 ht.2)
  have _hI : Integrable (fun t : ℝ => (F (boundary_alt t)).re * poissonKernel_alt z t) :=
    hRep.integrable z hzS
  have hpos : 0 ≤ ∫ t, (F (boundary_alt t)).re * poissonKernel_alt z t :=
    integral_nonneg_of_ae (μ := volume) hprod
  simpa [hRep.re_eq z hzS] using hpos

open RH.AcademicFramework.CompletedXi in
theorem HasHalfPlanePoissonTransportAlt_on_Jpinch
    {det2 O : ℂ → ℂ}
    (hRepOn : HasHalfPlanePoissonRepresentationOnAlt (F_pinch_alt det2 O)
      (Ω_alt \ {z | riemannXi_ext z = 0})) :
    PPlus_alt (F_pinch_alt det2 O) →
      ∀ z ∈ (Ω_alt \ {z | riemannXi_ext z = 0}), 0 ≤ ((F_pinch_alt det2 O) z).re := by
  intro hP
  exact HasHalfPlanePoissonTransportAlt_on (F := F_pinch_alt det2 O) (S := (Ω_alt \ {z | riemannXi_ext z = 0})) hRepOn hP

end HalfPlaneOuterAlt
end AcademicFramework
end RH


