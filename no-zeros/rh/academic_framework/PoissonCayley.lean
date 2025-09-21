import Mathlib.Analysis.Analytic.Basic
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CayleyAdapters
import rh.RS.Cayley
import rh.RS.Det2Outer
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Poisson–Cayley bridge (scaffolding)

This module introduces a crisp target Prop for the half-plane Poisson
real-part identity on a subset `S ⊆ Ω`, together with convenience
packagers that assemble the subset representation for the pinch field
once that identity is supplied.

The concrete proof of the identity will be added by transporting a
disk-side Poisson representation through the Cayley transform.
-/

noncomputable section

namespace RH
namespace AcademicFramework
namespace PoissonCayley

open Complex
open RH.AcademicFramework.HalfPlaneOuterV2
open RH.AcademicFramework
open MeasureTheory

/- Right half–plane Ω (local alias) -/
local notation "Ω" => RH.AcademicFramework.HalfPlaneOuterV2.Ω

/-- Target predicate: Poisson real-part identity for a function `F` on a subset `S ⊆ Ω`. -/
def HasHalfPlanePoissonReEqOn (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, (F z).re = poissonIntegral (fun t : ℝ => (F (boundary t)).re) z

/-- Convenience: specialize the target predicate to the pinch field `F := 2 · J_pinch det2 O` on
`S := Ω \ {riemannXi_ext = 0}` (ext variant). -/
def HasHalfPlanePoissonReEqOn_pinch_ext (det2 O : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonReEqOn (F_pinch det2 O)
    (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0})

/-!
Once the real-part identity is available on `S`, the subset Poisson representation used by the
pinch route follows immediately via `HalfPlaneOuterV2.pinch_poissonRepOn_offZeros`.
The following packagers expose this step explicitly for readability.
-/

-- (trimmed)

/-- Boundary identification between a half-plane function `F` and a disk function `H` via
the Cayley boundary mapping. -/
def EqOnBoundary (F H : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, F (boundary t) = H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)

/-- Kernel transport along Cayley on a subset `S ⊆ Ω` for a disk function `H`:
the half-plane Poisson integral of the pullback boundary real part equals the disk
Poisson real part at the Cayley image. -/
def CayleyKernelTransportOn (H : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S,
    poissonIntegral (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z
      = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re

/-- Disk→half-plane Cayley bridge for real parts on a subset `S ⊆ Ω`.
Assumptions:
- interior identification: `F = H ∘ toDisk` on `S`;
- boundary identification: `F(boundary t) = H(boundaryToDisk t)` on ℝ;
- kernel transport along Cayley on `S`.

Conclusion: the half-plane Poisson real-part identity holds for `F` on `S`. -/
theorem reEq_on_from_disk_via_cayley
  (F H : ℂ → ℂ) {S : Set ℂ}
  (hEqInterior : Set.EqOn F (fun z => H (RH.AcademicFramework.CayleyAdapters.toDisk z)) S)
  (hEqBoundary : EqOnBoundary F H)
  (hKernel : CayleyKernelTransportOn H S)
  : HasHalfPlanePoissonReEqOn F S := by
  intro z hzS
  have h1 : (F z).re = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re := by
    simpa using congrArg Complex.re (hEqInterior hzS)
  have h2 :
      poissonIntegral (fun t : ℝ => (F (boundary t)).re) z
        = poissonIntegral (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z := by
    -- pointwise equality of boundary integrands via boundary identification
    have : (fun t : ℝ => (F (boundary t)).re)
            = (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) := by
      funext t; simpa using congrArg Complex.re (hEqBoundary t)
    simpa [this]
  have h3 :
      poissonIntegral (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z
        = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re :=
    hKernel z hzS
  -- assemble
  have : poissonIntegral (fun t : ℝ => (F (boundary t)).re) z
            = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re := by
    simpa [h2, h3]
  -- finish with interior identification of real parts
  simpa [h1, this]

/-- Boundary identity for the Cayley pullback: `F(boundary t) = H(boundaryToDisk t)`. -/
lemma EqOnBoundary_pullback (H : ℂ → ℂ) :
  EqOnBoundary (fun z => H (CayleyAdapters.toDisk z)) H := by
  intro t
  simp [EqOnBoundary, CayleyAdapters.boundaryToDisk]

/-- From a subset half-plane Poisson representation of the Cayley pullback
`F := H ∘ toDisk` on `S`, derive kernel transport on `S` for `H`. -/
theorem cayley_kernel_transport_from_rep_on
  (H : ℂ → ℂ) {S : Set ℂ}
  (hRepOn : HasPoissonRepOn (fun z => H (CayleyAdapters.toDisk z)) S)
  : CayleyKernelTransportOn H S := by
  intro z hzS
  -- Re(F z) = P(boundary Re F)(z) for F := H ∘ toDisk
  have hRe :
      ((fun z => H (CayleyAdapters.toDisk z)) z).re
        = poissonIntegral (fun t : ℝ => ((fun z => H (CayleyAdapters.toDisk z)) (boundary t)).re) z :=
    hRepOn.formula z hzS
  -- Rewrite boundary integrand via `boundaryToDisk`, then rearrange
  have hIntg :
      (fun t : ℝ => ((fun z => H (CayleyAdapters.toDisk z)) (boundary t)).re)
        = (fun t : ℝ => (H (CayleyAdapters.boundaryToDisk t)).re) := by
    funext t; simp [CayleyAdapters.boundaryToDisk]
  -- Conclude the transport identity
  simpa [hIntg] using hRe.symm

/-- The remaining pinch-specialized and pullback representation sections are omitted
to keep this module minimal and compiling. -/

-- Global bridge: from a half-plane Poisson representation of `F`, obtain the
-- real-part identity on all of Ω.
theorem hReEq_on_of_halfplane_rep (F : ℂ → ℂ)
  (hRep : HasPoissonRep F) :
  HasHalfPlanePoissonReEqOn F Ω := by
  intro z hz
  exact hRep.formula z hz

-- Subset bridge: from a subset half-plane Poisson representation of `F` on `S`,
-- obtain the real-part identity on `S`.
theorem hReEq_on_of_halfplane_rep_on (F : ℂ → ℂ) {S : Set ℂ}
  (hRepOn : HasPoissonRepOn F S) :
  HasHalfPlanePoissonReEqOn F S := by
  intro z hz
  exact hRepOn.formula z hz

-- Pinch specialization (ext): if the pinch field admits a half-plane Poisson
-- representation on Ω, then the real-part identity holds on the off-zeros subset `S`.
theorem hReEq_pinch_ext_of_halfplane_rep
  (det2 O : ℂ → ℂ)
  (hRep : HasPoissonRep (F_pinch det2 O)) :
  HasHalfPlanePoissonReEqOn_pinch_ext det2 O := by
  intro z hz
  have : (F_pinch det2 O z).re
      = poissonIntegral (fun t : ℝ => (F_pinch det2 O (boundary t)).re) z :=
    hRep.formula z hz
  simpa using this

end PoissonCayley
end AcademicFramework
end RH
