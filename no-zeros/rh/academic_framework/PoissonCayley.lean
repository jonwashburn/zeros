import Mathlib.Analysis.Analytic.Basic
import rh.academic_framework.HalfPlaneOuter
import rh.RS.Cayley
import rh.RS.Det2Outer

/‑!
# Poisson–Cayley bridge (scaffolding)

This module introduces a crisp target Prop for the half‑plane Poisson
real‑part identity on a subset `S ⊆ Ω`, together with convenience
packagers that assemble the subset representation for the pinch field
once that identity is supplied.

The concrete proof of the identity will be added by transporting a
disk‑side Poisson representation through the Cayley transform.
‑/

noncomputable section

namespace RH
namespace AcademicFramework
namespace PoissonCayley

open Complex
open RH.AcademicFramework.HalfPlaneOuter
open RH.AcademicFramework

/- Right half–plane Ω (local alias) -/
local notation "Ω" => RH.AcademicFramework.HalfPlaneOuter.Ω

/-- Target predicate: Poisson real‑part identity for a function `F` on a subset `S ⊆ Ω`. -/
def HasHalfPlanePoissonReEqOn (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, (F z).re = P (fun t : ℝ => (F (boundary t)).re) z

/-- Convenience: specialize the target predicate to the pinch field `F := 2 · J_pinch det2 O` on
`S := Ω \ {riemannXi_ext = 0}` (ext variant). -/
def HasHalfPlanePoissonReEqOn_pinch_ext (det2 O : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonReEqOn (F_pinch det2 O)
    (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0})

/‑!
Once the real‑part identity is available on `S`, the subset Poisson representation used by the
pinch route follows immediately via `HalfPlaneOuter.pinch_representation_on_offXi_M2`.
The following packagers expose this step explicitly for readability.
‑/

/-- From the Poisson real‑part identity on `S := Ω \ {ξ_ext = 0}`, build the subset Poisson
representation record for the pinch field associated to the chosen outer from
`OuterHalfPlane.ofModulus_det2_over_xi_ext`.

Inputs:
- `hDet2` — analyticity/nonvanishing interface for `det2` on `Ω`
- `hOuterExist` — existence of an outer normalizer `O` with boundary modulus `|det2/ξ_ext|`
- `hXi` — analyticity of `ξ_ext` on `Ω`
- `hReEq` — the half‑plane Poisson real‑part identity on `S`
‑/
theorem pinch_representation_on_offXi_M2_from_reEq
  (hDet2 : RH.RS.Det2OnOmega)
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hXi : AnalyticOn ℂ RH.AcademicFramework.CompletedXi.riemannXi_ext Ω)
  (hReEq : HasHalfPlanePoissonReEqOn_pinch_ext RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist))
  : HasHalfPlanePoissonRepresentationOn
      (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist))
      (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) := by
  classical
  -- Unpack the target equality on S and delegate to the M=2 subset builder
  have hReEq' : ∀ z ∈ (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) z).re
        = P (fun t : ℝ =>
            (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) (boundary t)).re) z :=
    hReEq
  -- Invoke the refactored M=2 subset representation builder
  exact RH.AcademicFramework.HalfPlaneOuter.pinch_representation_on_offXi_M2
    (hDet2 := hDet2) (hOuterExist := hOuterExist) (hXi := hXi) (hReEq := hReEq')

/‑!
## Disk→half‑plane Cayley change‑of‑variables: scaffolding

We factor the derivation of the half‑plane Poisson real‑part identity into three
readable assumptions:
- interior identification via Cayley, `EqOn F (H ∘ toDisk) S`;
- boundary identification along the Cayley boundary, `EqOnBoundary`;
- kernel transport along Cayley, `CayleyKernelTransportOn` (Poisson integral
  commutes with the Cayley change of variables on real parts).

From these we derive the target identity `HasHalfPlanePoissonReEqOn F S`.
‑/

/-- Boundary identification between a half‑plane function `F` and a disk function `H` via
the Cayley boundary mapping. -/
def EqOnBoundary (F H : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, F (boundary t) = H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)

/-- Kernel transport along Cayley on a subset `S ⊆ Ω` for a disk function `H`:
the half‑plane Poisson integral of the pullback boundary real part equals the disk
Poisson real part at the Cayley image. -/
def CayleyKernelTransportOn (H : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S,
    P (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z
      = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re

/-- Disk→half‑plane Cayley bridge for real parts on a subset `S ⊆ Ω`.
Assumptions:
- interior identification: `F = H ∘ toDisk` on `S`;
- boundary identification: `F(boundary t) = H(boundaryToDisk t)` on ℝ;
- kernel transport along Cayley on `S`.

Conclusion: the half‑plane Poisson real‑part identity holds for `F` on `S`. -/
theorem reEq_on_from_disk_via_cayley
  (F H : ℂ → ℂ) {S : Set ℂ}
  (hEqInterior : Set.EqOn F (fun z => H (RH.AcademicFramework.CayleyAdapters.toDisk z)) S)
  (hEqBoundary : EqOnBoundary F H)
  (hKernel : CayleyKernelTransportOn H S)
  : HasHalfPlanePoissonReEqOn F S := by
  intro z hzS
  have h1 : (F z).re = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re := by
    have := hEqInterior hzS
    simpa using congrArg Complex.realPart this
  have h2 :
      P (fun t : ℝ => (F (boundary t)).re) z
        = P (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z := by
    -- pointwise equality of boundary integrands via boundary identification
    have : (fun t : ℝ => (F (boundary t)).re)
            = (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) := by
      funext t; simpa [EqOnBoundary] using congrArg Complex.realPart (hEqBoundary t)
    simpa [this]
  have h3 :
      P (fun t : ℝ => (H (RH.AcademicFramework.CayleyAdapters.boundaryToDisk t)).re) z
        = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re :=
    hKernel z hzS
  -- assemble
  have : P (fun t : ℝ => (F (boundary t)).re) z
            = (H (RH.AcademicFramework.CayleyAdapters.toDisk z)).re := by
    simpa [h2, h3]
  -- finish with interior identification of real parts
  simpa [h1, this]

/‑!
## Readiness lemmas for the pinch field on S

We record two small helpers showing that the pinch field `F := 2 · J_pinch det2 O`
is analytic on `S := Ω \ {ξ_ext = 0}` and that its boundary Poisson integrand is
integrable there using the uniform M=2 bound captured earlier.
‑/

/-- Analyticity of the pinch field on the off‑zeros subset `S := Ω \ {ξ_ext = 0}`. -/
lemma analyticOn_pinch_on_S
  (hDet2 : RH.RS.Det2OnOmega)
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hXi : AnalyticOn ℂ RH.AcademicFramework.CompletedXi.riemannXi_ext Ω)
  : AnalyticOn ℂ
      (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist))
      (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) := by
  classical
  have hJ : AnalyticOn ℂ
      (RH.RS.J_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist))
      (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) :=
    RH.RS.J_pinch_analytic_on_offXi_choose (hDet2 := hDet2)
      (hOuterExist := hOuterExist) (hXi := hXi)
  have hConst : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ))
      (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) := by
    simpa using (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ))
      (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}))
  simpa [F_pinch] using hConst.mul hJ

/-- Boundary‑kernel integrability for the pinch field at each interior point of `S`,
using the uniform M=2 boundary bound derived from the boundary modulus equality. -/
lemma integrable_boundary_kernel_pinch_on_S
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  : ∀ z ∈ (Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      Integrable (fun t : ℝ =>
        (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) (boundary t)).re
          * poissonKernel z t) := by
  classical
  intro z hzS
  have hzΩ : z ∈ Ω := hzS.1
  have hzRe : (1/2 : ℝ) < z.re := by simpa [Ω, Set.mem_setOf_eq] using hzΩ
  -- invoke the M=2 integrability helper specialized to the chosen outer
  exact integrable_boundary_kernel_of_bounded' (hOuterExist := hOuterExist) z hzRe

/‑!
### Concrete disk‑side H and Cayley equalities (for the pinch field)

We define the disk‑side function `H_pinch` as the Cayley pullback of the pinch
field through `toHalf`, and show the interior and boundary identifications used
by the Cayley bridge.
‑/

/-- Disk‑side function associated to the pinch field via the inverse Cayley map. -/
def H_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun w => (F_pinch det2 O) (CayleyAdapters.toHalf w)

/-- Algebraic identity: on Ω, `toHalf (toDisk z) = z`. -/
lemma toHalf_toDisk_id_on_Ω {z : ℂ} (hz : z ∈ Ω) :
  CayleyAdapters.toHalf (CayleyAdapters.toDisk z) = z := by
  classical
  -- Expand definitions and use basic field algebra; ensure `z ≠ 0` inside Ω.
  have hz0 : z ≠ 0 := by
    -- If z = 0 then Re z = 0, contradicting Re z > 1/2
    intro h
    have : (0 : ℝ) < (1/2 : ℝ) := by norm_num
    have hzRe : (1/2 : ℝ) < z.re := by simpa [Ω, Set.mem_setOf_eq] using hz
    exact (lt_irrefl _ (lt_trans this hzRe))
  -- Compute explicitly: 1 / (1 − (z−1)/z) = z
  have hden : (1 : ℂ) - ((z - 1) / z) = (1 : ℂ) / z := by
    -- 1 = z/z since z ≠ 0, then combine over common denominator z
    have hzdiv : z / z = (1 : ℂ) := by simpa [hz0] using (div_self hz0)
    calc
      (1 : ℂ) - ((z - 1) / z)
          = (z / z) - ((z - 1) / z) := by simpa [hzdiv]
      _   = (z - (z - 1)) / z := by simpa using (sub_div (z) (z - 1) z).symm
      _   = (1 : ℂ) / z := by ring
  -- conclude
  have : (1 : ℂ) / ((1 : ℂ) / z) = z := by
    -- a/(b/c) = (a*c)/b, with a=b=1
    simpa [one_mul, one_div] using (div_div_eq_mul_div (1 : ℂ) (1 : ℂ) z)
  simpa [CayleyAdapters.toHalf, CayleyAdapters.toDisk, hden, one_div] using this

/-- Interior identification on any `S ⊆ Ω`: `F_pinch = H_pinch ∘ toDisk` on `S`. -/
lemma EqOn_interior_pinch_on
  {S : Set ℂ} (hS : S ⊆ Ω) (det2 O : ℂ → ℂ) :
  Set.EqOn (F_pinch det2 O)
    (fun z => H_pinch det2 O (CayleyAdapters.toDisk z)) S := by
  intro z hzS
  have hzΩ : z ∈ Ω := hS hzS
  -- unfold and use toHalf ∘ toDisk = id on Ω
  simp [H_pinch, CayleyAdapters.toDisk, CayleyAdapters.toHalf, toHalf_toDisk_id_on_Ω hzΩ]

/-- Boundary identification: `F_pinch(boundary t) = H_pinch(boundaryToDisk t)`. -/
lemma EqOnBoundary_pinch (det2 O : ℂ → ℂ) :
  EqOnBoundary (F_pinch det2 O) (H_pinch det2 O) := by
  intro t
  -- boundaryToDisk t = toDisk (boundary t) by definition
  have : CayleyAdapters.toHalf (CayleyAdapters.boundaryToDisk t)
          = boundary t := by
    -- Algebraic identity valid for any nonzero z, applied to z = boundary t
    have hb0 : boundary t ≠ 0 := by
      intro h
      have hre : (boundary t).re = (0 : ℝ) := by simpa [h]
      simp [RH.AcademicFramework.HalfPlaneOuter.boundary] at hre
    simpa [CayleyAdapters.boundaryToDisk]
      using toHalf_toDisk_id_of_ne_zero hb0
  -- Conclude boundary identification
  simp [EqOnBoundary, H_pinch, this]

/-- Cayley bridge specialized to the pinch field on any `S ⊆ Ω`:
if the kernel transport holds for `H_pinch` on `S`, then the real‑part identity
holds for `F_pinch` on `S`. -/
theorem reEq_on_pinch_from_cayley
  {S : Set ℂ} (hS : S ⊆ Ω) (det2 O : ℂ → ℂ)
  (hKernel : CayleyKernelTransportOn (H_pinch det2 O) S)
  : HasHalfPlanePoissonReEqOn (F_pinch det2 O) S := by
  -- Apply the abstract Cayley bridge with the concrete identifications
  refine reEq_on_from_disk_via_cayley
    (F := F_pinch det2 O) (H := H_pinch det2 O)
    (S := S) ?hInt ?hBd hKernel
  · -- interior EqOn on S
    exact EqOn_interior_pinch_on (hS) det2 O
  · -- boundary EqOn
    exact EqOnBoundary_pinch det2 O

/‑!
## Simple bridges from representation to real‑part identity

If we already have a half‑plane Poisson representation (global or subset), we can
read off the real‑part Poisson identity immediately. These bridges are useful to
thread existing representation facts into the refactored M2 builder.
‑/

/-- Global bridge: from a half‑plane Poisson representation of `F`, obtain the
real‑part identity on all of Ω. -/
theorem hReEq_on_of_halfplane_rep (F : ℂ → ℂ)
  (hRep : HasHalfPlanePoissonRepresentation F) :
  HasHalfPlanePoissonReEqOn F Ω := by
  intro z hz
  exact hRep.re_eq z hz

/-- Subset bridge: from a subset half‑plane Poisson representation of `F` on `S`,
obtain the real‑part identity on `S`. -/
theorem hReEq_on_of_halfplane_rep_on (F : ℂ → ℂ) {S : Set ℂ}
  (hRepOn : HasHalfPlanePoissonRepresentationOn F S) :
  HasHalfPlanePoissonReEqOn F S := by
  intro z hz
  exact hRepOn.re_eq z hz

/-- Pinch specialization (ext): if the pinch field admits a half‑plane Poisson
representation on Ω, then the real‑part identity holds on the off‑zeros subset `S`. -/
theorem hReEq_pinch_ext_of_halfplane_rep
  (det2 O : ℂ → ℂ)
  (hRep : HasHalfPlanePoissonRepresentation (F_pinch det2 O)) :
  HasHalfPlanePoissonReEqOn_pinch_ext det2 O := by
  intro z hz
  have : (F_pinch det2 O z).re
      = P (fun t : ℝ => (F_pinch det2 O (boundary t)).re) z :=
    hRep.re_eq z (by exact hz.1)
  simpa using this

end PoissonCayley
end AcademicFramework
end RH
