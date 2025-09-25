import Mathlib.Analysis.Analytic.Basic
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CayleyAdapters
import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.RS.OuterWitness
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
  -- pointwise equality of boundary real-part functions
  have hIntgEq :
      (fun t : ℝ => (F (boundary t)).re)
        = (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) := by
    funext t
    simpa using congrArg Complex.re (hEqBoundary t)
  -- transport the kernel identity along the equality of boundary integrands
  have hPI :
      poissonIntegral (fun t : ℝ => (F (boundary t)).re) z
        = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re := by
    -- combine integrand equality with kernel transport via a calc chain
    calc
      poissonIntegral (fun t : ℝ => (F (boundary t)).re) z
          = poissonIntegral (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z := by
            exact congrArg (fun u => poissonIntegral u z) hIntgEq
      _ = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re :=
            hKernel z hzS
  -- finish with interior identification of real parts
  simpa [h1] using hPI.symm

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

/-!
## Off-zeros Poisson real-part identity via Cayley (scaffold)

We now provide a clean, assumption-led scaffold that derives the half-plane
real-part Poisson identity on a subset `S ⊆ Ω` for a target function `F`,
by transporting a disk-side Poisson representation of a function `H` along
the Cayley transform.

Inputs (explicit hypotheses):
- `hDisk` — disk Poisson representation for `H` on the unit disk,
- `hEqInterior` — interior identification on `S`: `F = H ∘ toDisk` on `S`,
- `hEqBoundary` — boundary identification on ℝ: `F(boundary t) = H(boundaryToDisk t)`,
- `hMapS` — Cayley maps `S` into the unit disk,
- `hChange` — change-of-variables identity equating the disk and half-plane Poisson
  integrals along Cayley at each `z ∈ S`.

Conclusion: the half-plane Poisson real-part identity holds for `F` on `S`.
-/
theorem hReEq_on_from_disk_scaffold
  {F Hdisk : ℂ → ℂ} {S : Set ℂ}
  (hDisk : RH.AcademicFramework.DiskHardy.HasDiskPoissonRepresentation Hdisk)
  (hEqInterior : Set.EqOn F (fun z => Hdisk (RH.AcademicFramework.CayleyAdapters.toDisk z)) S)
  (hEqBoundary : EqOnBoundary F Hdisk)
  (hMapS : ∀ z ∈ S, RH.AcademicFramework.DiskHardy.unitDisk
            (RH.AcademicFramework.CayleyAdapters.toDisk z))
  (hChange : ∀ z ∈ S,
    (∫ θ : ℝ,
        (Hdisk (RH.AcademicFramework.DiskHardy.boundary θ)).re
          * RH.AcademicFramework.DiskHardy.poissonKernel (RH.AcademicFramework.CayleyAdapters.toDisk z) θ)
      = (∫ t : ℝ,
          (F (boundary t)).re * poissonKernel z t))
  : HasHalfPlanePoissonReEqOn F S := by
  -- Build the kernel transport for `Hdisk` on `S` directly from the disk representation
  -- and the supplied change-of-variables identity, then apply the generic bridge.
  have hKernel : CayleyKernelTransportOn Hdisk S := by
    intro z hzS
    -- Disk-side representation at `w := toDisk z`
    have hw : RH.AcademicFramework.DiskHardy.unitDisk (RH.AcademicFramework.CayleyAdapters.toDisk z) :=
      hMapS z hzS
    have hDiskEq : (Hdisk (RH.AcademicFramework.CayleyAdapters.toDisk z)).re
        = ∫ θ : ℝ,
            (Hdisk (RH.AcademicFramework.DiskHardy.boundary θ)).re
              * RH.AcademicFramework.DiskHardy.poissonKernel (RH.AcademicFramework.CayleyAdapters.toDisk z) θ :=
      hDisk.re_eq (RH.AcademicFramework.CayleyAdapters.toDisk z) hw
    -- Change variables to a half-plane Poisson integral for `F`
    have hCoV := hChange z hzS
    -- Identify the half-plane integrand via the boundary identification
    have hIntgEq :
        (fun t : ℝ => (Hdisk (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re)
          = (fun t : ℝ => (F (boundary t)).re) := by
      funext t
      simpa using congrArg Complex.re (hEqBoundary t)
    -- Conclude the kernel transport identity for `Hdisk`
    -- poissonIntegral (pullback boundary real-part of H) = Re(H (toDisk z))
    -- by chaining disk rep = half-plane integral (hCoV) and rewriting integrands (hIntgEq)
    calc
      poissonIntegral (fun t : ℝ => (Hdisk (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z
          = ∫ t : ℝ,
              (Hdisk (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re * poissonKernel z t := by
            rfl
      _ = ∫ t : ℝ, (F (boundary t)).re * poissonKernel z t := by
            simpa using congrArg (fun u => ∫ t, u t * poissonKernel z t) hIntgEq
      _ = ∫ θ : ℝ,
              (Hdisk (RH.AcademicFramework.DiskHardy.boundary θ)).re
                * RH.AcademicFramework.DiskHardy.poissonKernel (RH.AcademicFramework.CayleyAdapters.toDisk z) θ :=
            hCoV.symm
      _ = (Hdisk (RH.AcademicFramework.CayleyAdapters.toDisk z)).re :=
            hDiskEq.symm
  -- Apply the generic Cayley bridge on `S`
  exact reEq_on_from_disk_via_cayley F Hdisk hEqInterior hEqBoundary hKernel

/-!
Specialized export for the default pinch field on the off-zeros set `S := Ω \ {ξ_ext = 0}`.

This keeps the disk representation and change-of-variables identity as explicit
inputs. Boundary and interior identifications are accepted as hypotheses so this
lemma stays assumption-led; later prompts can instantiate them.
-/
lemma hFormula_default_offZeros_from_disk
  {Hdisk : ℂ → ℂ}
  (_hDet2 : RH.RS.Det2OnOmega)
  (_hXi : AnalyticOn ℂ RH.AcademicFramework.CompletedXi.riemannXi_ext Ω)
  (hDisk : RH.AcademicFramework.DiskHardy.HasDiskPoissonRepresentation Hdisk)
  (hEqInterior : Set.EqOn (F_pinch RH.RS.det2 RH.RS.O_default)
      (fun z => Hdisk (RH.AcademicFramework.CayleyAdapters.toDisk z))
      (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}))
  (hEqBoundary : EqOnBoundary (F_pinch RH.RS.det2 RH.RS.O_default) Hdisk)
  (hChange : ∀ z ∈ (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      (∫ θ : ℝ,
          (Hdisk (RH.AcademicFramework.DiskHardy.boundary θ)).re
            * RH.AcademicFramework.DiskHardy.poissonKernel (RH.AcademicFramework.CayleyAdapters.toDisk z) θ)
        = (∫ t : ℝ,
            (F_pinch RH.RS.det2 RH.RS.O_default (boundary t)).re * poissonKernel z t))
  : ∀ z ∈ (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 RH.RS.O_default z).re
        = poissonIntegral
            (fun t => (F_pinch RH.RS.det2 RH.RS.O_default (boundary t)).re) z := by
  -- Map property of Cayley on Ω ⇒ unit disk; use it on the subset S by projection
  have hMapS : ∀ z ∈ (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      RH.AcademicFramework.DiskHardy.unitDisk (RH.AcademicFramework.CayleyAdapters.toDisk z) := by
    intro z hz
    exact RH.AcademicFramework.CayleyAdapters.map_Ω_to_unitDisk (by exact hz.1)
  -- Apply the scaffold bridge to obtain the formula on S
  have hFormula := hReEq_on_from_disk_scaffold
    (F := F_pinch RH.RS.det2 RH.RS.O_default)
    (Hdisk := Hdisk)
    (S := (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}))
    hDisk hEqInterior hEqBoundary hMapS hChange
  -- Unpack the predicate to the desired pointwise statement
  intro z hz
  exact hFormula z hz

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
    hRep.formula z hz.1
  simpa using this

/-- Scaffold lemma (Cayley route): off-zeros Poisson real-part identity for the
default pinch field `F := 2 · J_pinch det2 O_default` on `S := Ω \\ {ξ_ext = 0}`
assuming a disk-side Poisson representation and a change-of-variables equality.

Inputs (assumptions):
- `Hdisk` and its disk Poisson representation `hDisk`.
- `hMap`: Cayley image `toDisk z` lies in the unit disk for all `z ∈ Ω`.
- `hAnalytic`: analyticity of the half-plane field `F` on `Ω`.
- `hIntegrable`: boundary integrability of `Re F` against the half-plane kernel.
- `hRel`: identification `F = Hdisk ∘ toDisk` on `Ω`.
- `hChange`: change-of-variables identity equating the disk and half-plane
  Poisson integrals along Cayley.

Conclusion: the half-plane Poisson real-part formula holds for `F` on the
off-zeros set `S`.
-/
lemma hFormula_default_offZeros_from_disk
  (Hdisk : ℂ → ℂ)
  (hDisk : DiskHardy.HasDiskPoissonRepresentation Hdisk)
  (hMap : ∀ z ∈ HalfPlaneOuterV2.Ω,
    CayleyAdapters.toDisk z ∈ DiskHardy.unitDisk)
  (hAnalytic : AnalyticOn ℂ
    (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default)
    HalfPlaneOuterV2.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuterV2.Ω,
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default
          (HalfPlaneOuterV2.boundary t)).re
        * HalfPlaneOuterV2.poissonKernel z t))
  (hRel : Set.EqOn
    (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default)
    (fun z => Hdisk (CayleyAdapters.toDisk z))
    HalfPlaneOuterV2.Ω)
  (hChange : ∀ z ∈ HalfPlaneOuterV2.Ω,
    (∫ θ : ℝ,
      (Hdisk (DiskHardy.boundary θ)).re
        * DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ)
      = (∫ t : ℝ,
        (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default
           (HalfPlaneOuterV2.boundary t)).re
          * HalfPlaneOuterV2.poissonKernel z t))
  : ∀ z ∈ (HalfPlaneOuterV2.Ω \ {z | CompletedXi.riemannXi_ext z = 0}),
      (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default z).re
        = HalfPlaneOuterV2.poissonIntegral
            (fun t =>
              (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default
                (HalfPlaneOuterV2.boundary t)).re) z := by
  intro z hz
  -- Build the half-plane Poisson representation for F using the Cayley bridge
  have hRep : HalfPlaneOuterV2.HasPoissonRep
      (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default) :=
    CayleyAdapters.HalfPlanePoisson_real_from_Disk
      (F := HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default)
      (Hdisk := Hdisk)
      hDisk hRel hMap hAnalytic hIntegrable hChange
  -- Restrict the global formula to the off-zeros set; it only uses membership in Ω
  have hzΩ : z ∈ HalfPlaneOuterV2.Ω := hz.1
  simpa using (hRep.formula z hzΩ)

/-- Convenience re-exposure: same as `hFormula_default_offZeros_from_disk`
with the identical inputs and specialization for
`F := 2 · J_pinch RH.RS.det2 RH.RS.O_default`, just re-exposed for callers. -/
lemma hFormula_default_offZeros_from_disk'
  (Hdisk : ℂ → ℂ)
  (hDisk : DiskHardy.HasDiskPoissonRepresentation Hdisk)
  (hMap : ∀ z ∈ HalfPlaneOuterV2.Ω,
    CayleyAdapters.toDisk z ∈ DiskHardy.unitDisk)
  (hAnalytic : AnalyticOn ℂ
    (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default)
    HalfPlaneOuterV2.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuterV2.Ω,
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default
          (HalfPlaneOuterV2.boundary t)).re
        * HalfPlaneOuterV2.poissonKernel z t))
  (hRel : Set.EqOn
    (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default)
    (fun z => Hdisk (CayleyAdapters.toDisk z))
    HalfPlaneOuterV2.Ω)
  (hChange : ∀ z ∈ HalfPlaneOuterV2.Ω,
    (∫ θ : ℝ,
      (Hdisk (DiskHardy.boundary θ)).re
        * DiskHardy.poissonKernel (CayleyAdapters.toDisk z) θ)
      = (∫ t : ℝ,
        (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default
           (HalfPlaneOuterV2.boundary t)).re
          * HalfPlaneOuterV2.poissonKernel z t))
  : ∀ z ∈ (HalfPlaneOuterV2.Ω \ {z | CompletedXi.riemannXi_ext z = 0}),
      (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default z).re
        = HalfPlaneOuterV2.poissonIntegral
            (fun t =>
              (HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default
                (HalfPlaneOuterV2.boundary t)).re) z :=
  hFormula_default_offZeros_from_disk Hdisk hDisk hMap hAnalytic hIntegrable hRel hChange

end PoissonCayley
end AcademicFramework
end RH
