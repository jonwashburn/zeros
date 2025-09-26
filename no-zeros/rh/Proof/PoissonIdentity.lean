import rh.RS.OuterWitness
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CompletedXi
import rh.academic_framework.PoissonCayley
import rh.academic_framework.CayleyAdapters

/-!
# Poisson real-part identity (statement) and boundary measurability helpers

This lightweight module provides:

- A statement-level `hFormula` shape for the Poisson real-part identity on the
  off-zeros domain `Ω \\ {ξ_ext = 0}` for the default pinch field
  `F_pinch det2 O_default`.
- Boundary measurability wrappers used by `Proof.Transport.hTrans_default`.

No analytic proofs are introduced here; this file only packages assumptions in
the exact forms consumed downstream and exposes convenient lemmas.
-/

noncomputable section

namespace RH
namespace Proof
namespace PoissonIdentity

open Complex Set
open RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2
open RH.AcademicFramework

/-- Target `hFormula` shape used by `Transport.hTrans_default`:
on the off-zeros set, the real part of the default pinch field equals its
Poisson integral from boundary real data. -/
def hFormula_default : Prop :=
  ∀ z ∈ (Ω \\ {z | riemannXi_ext z = 0}),
    (F_pinch RH.RS.det2 RH.RS.O_default z).re
      = poissonIntegral
          (fun t => (F_pinch RH.RS.det2 RH.RS.O_default (boundary t)).re)
          z

/-- Direct half-plane route: the Poisson identity follows immediately from a
subset Poisson representation on `Ω \\ {ξ_ext = 0}`. -/
lemma hFormula_default_of_repOn
  (hRepOn : HasPoissonRepOn (F_pinch RH.RS.det2 RH.RS.O_default)
              (Ω \\ {z | riemannXi_ext z = 0})) :
  hFormula_default := by
  intro z hz
  simpa using hRepOn.formula z hz

/-- Cayley route: derive the Poisson identity for the default pinch field from
disk-side data via the AF Poisson–Cayley bridge. Assumptions are the interior
and boundary identifications with a disk function `H`, and the kernel transport
identity on the working subset. -/
lemma hFormula_default_from_cayley
  (H : ℂ → ℂ)
  (hEqInterior : Set.EqOn (F_pinch RH.RS.det2 RH.RS.O_default)
      (fun z => H (CayleyAdapters.toDisk z))
      (Ω \\ {z | riemannXi_ext z = 0}))
  (hEqBoundary : PoissonCayley.EqOnBoundary (F_pinch RH.RS.det2 RH.RS.O_default) H)
  (hKernel : PoissonCayley.CayleyKernelTransportOn H (Ω \\ {z | riemannXi_ext z = 0}))
  : hFormula_default := by
  intro z hz
  have h : PoissonCayley.HasHalfPlanePoissonReEqOn
      (F_pinch RH.RS.det2 RH.RS.O_default)
      (Ω \\ {z | riemannXi_ext z = 0}) :=
    PoissonCayley.reEq_on_from_disk_via_cayley
      (F := (F_pinch RH.RS.det2 RH.RS.O_default)) (H := H)
      (S := (Ω \\ {z | riemannXi_ext z = 0}))
      hEqInterior hEqBoundary hKernel
  exact h z hz

/-- Boundary measurability helper: `t ↦ det2(boundary t)` is measurable if
`det2` is measurable (it will be supplied or treated abstractly). -/
lemma measurable_boundary_det2
  (h : Measurable RH.RS.det2) :
  Measurable (fun t : ℝ => RH.RS.det2 (boundary t)) :=
  measurable_comp_boundary h

/-- Boundary measurability helper for the chosen default outer. -/
lemma measurable_boundary_O_default
  (h : Measurable RH.RS.O_default) :
  Measurable (fun t : ℝ => RH.RS.O_default (boundary t)) :=
  measurable_comp_boundary h

/-- Boundary measurability helper for `riemannXi_ext`. -/
lemma measurable_boundary_riemannXi_ext
  (h : Measurable riemannXi_ext) :
  Measurable (fun t : ℝ => riemannXi_ext (boundary t)) :=
  measurable_comp_boundary h

end PoissonIdentity
end Proof
end RH
