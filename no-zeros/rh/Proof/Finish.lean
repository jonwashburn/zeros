import rh.Proof.UnconditionalEntry
import rh.Proof.Transport
import rh.Proof.PinnedData
import rh.RS.OuterWitness
import rh.Cert.KxiPPlus
import rh.academic_framework.CompletedXi
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.PoissonCayley

/-!
One-shot unconditional RH glue (parametric): bind transport + (P+) + pinned.

Inputs:
- `Det2OnOmega` (RS interface for analyticity/nonvanishing of `det2` on `Ω`)
- analyticity of `riemannXi_ext` on the half-plane `Ω`
- boundary measurability along the critical line for `det2`, `O_default`, `riemannXi_ext`
- a Poisson real-part identity for the pinch field on `Ω \\ {ξ_ext = 0}`
- the statement-level Carleson ⇒ (P+) bridge for the pinch field

Output: Mathlib's `RiemannHypothesis`.

This composes existing wrappers only; no new analytic content is added.
-/

noncomputable section

namespace RH
namespace Proof
namespace Finish

open Complex Set
open RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2

/-- One-shot unconditional RH: from transport `(P+) ⇒` interior nonnegativity
for the default pinch field, a statement-level `(P+)` provider from a Carleson
budget, and pinned u‑trick data at each `ξ_ext` zero, conclude Mathlib's
`RiemannHypothesis`.

Dependencies are packaged via existing proof-layer helpers:
- transport is provided by `Proof.Transport.hTrans_default` from a Poisson
  representation on `Ω \\ {ξ_ext = 0}` (parametrized by a real‑part identity),
- `(P+)` is provided as the statement shape `Cert.PPlusFromCarleson_exists` for
  the concrete field,
- pinned data is given by `Proof.PinnedData.hPinned_default` from `Det2OnOmega`.
-/
theorem RiemannHypothesis_unconditional
  (hDet2 : RH.RS.Det2OnOmega)
  (hXi   : AnalyticOn ℂ riemannXi_ext Ω)
  (hDet_meas : Measurable (fun t : ℝ => RH.RS.det2 (boundary t)))
  (hO_meas   : Measurable (fun t : ℝ => RH.RS.O_default (boundary t)))
  (hXi_meas  : Measurable (fun t : ℝ => riemannXi_ext (boundary t)))
  (hFormula  : ∀ z ∈ (Ω \\ {z | riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 RH.RS.O_default z).re =
        poissonIntegral (fun t => (F_pinch RH.RS.det2 RH.RS.O_default (boundary t)).re) z)
  (hP : RH.Cert.PPlusFromCarleson_exists
          (fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 RH.RS.O_default z))
  : RiemannHypothesis := by
  -- Transport predicate (P+) ⇒ interior nonnegativity on Ω for the default pinch field
  have hTrans := RH.Proof.Transport.hTrans_default
    (hDet2 := hDet2) (hXi := hXi)
    (hDet_meas := hDet_meas) (hO_meas := hO_meas) (hXi_meas := hXi_meas)
    (hFormula := hFormula)
  -- Pinned u‑trick local data specialized to O_default
  have hPinned := RH.Proof.PinnedData.hPinned_default hDet2
  -- Conclude via the existing unconditional entry wrapper
  exact RH.Proof.Unconditional.RiemannHypothesis_from_transport_and_pinned
    hTrans hP hPinned

/-!
Scaffold wiring: derive the transport predicate `hTrans` for the default pinch
field from a disk-side Poisson representation and a Cayley change-of-variables
identity, then close with a provided `(P+)` provider and the pinned data.

This lemma keeps the disk representation and CoV equality as inputs, so it can
be instantiated once those are supplied. It uses the existing `Finish` glue.
-/
theorem RiemannHypothesis_unconditional_from_disk_scaffold
  (Hdisk : ℂ → ℂ)
  (hDisk : RH.AcademicFramework.DiskHardy.HasDiskPoissonRepresentation Hdisk)
  (hMap : ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω,
    RH.AcademicFramework.CayleyAdapters.toDisk z ∈ RH.AcademicFramework.DiskHardy.unitDisk)
  (hAnalytic : AnalyticOn ℂ
    (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default)
    RH.AcademicFramework.HalfPlaneOuterV2.Ω)
  (hIntegrable : ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω,
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default
          (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re
        * RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel z t))
  (hRel : Set.EqOn
    (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default)
    (fun z => Hdisk (RH.AcademicFramework.CayleyAdapters.toDisk z))
    RH.AcademicFramework.HalfPlaneOuterV2.Ω)
  (hChange : ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω,
    (∫ θ : ℝ,
      (Hdisk (RH.AcademicFramework.DiskHardy.boundary θ)).re
        * RH.AcademicFramework.DiskHardy.poissonKernel (RH.AcademicFramework.CayleyAdapters.toDisk z) θ)
      = (∫ t : ℝ,
        (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 RH.RS.O_default
           (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re
          * RH.AcademicFramework.HalfPlaneOuterV2.poissonKernel z t))
  (hDet2 : RH.RS.Det2OnOmega)
  (hXi   : AnalyticOn ℂ RH.AcademicFramework.CompletedXi.riemannXi_ext RH.AcademicFramework.HalfPlaneOuterV2.Ω)
  (hDet_meas : Measurable (fun t : ℝ => RH.RS.det2 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))
  (hO_meas   : Measurable (fun t : ℝ => RH.RS.O_default (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))
  (hXi_meas  : Measurable (fun t : ℝ => RH.AcademicFramework.CompletedXi.riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))
  (hP : RH.Cert.PPlusFromCarleson_exists
          (fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 RH.RS.O_default z))
  : RiemannHypothesis := by
  -- Off-zeros Poisson formula via the scaffold lemma
  have hFormula := RH.AcademicFramework.PoissonCayley.hFormula_default_offZeros_from_disk
    (Hdisk := Hdisk) (hDisk := hDisk) (hMap := hMap)
    (hAnalytic := hAnalytic) (hIntegrable := hIntegrable)
    (hRel := hRel) (hChange := hChange)
  -- Transport predicate from boundary (P+) to interior nonnegativity
  have hTrans := RH.Proof.Transport.hTrans_default
    (hDet2 := hDet2) (hXi := hXi)
    (hDet_meas := hDet_meas) (hO_meas := hO_meas) (hXi_meas := hXi_meas)
    (hFormula := hFormula)
  -- Pinned local data at ξ_ext-zeros
  have hPinned := RH.Proof.PinnedData.hPinned_default hDet2
  -- Final close
  exact RH.Proof.Unconditional.RiemannHypothesis_from_transport_and_pinned
    hTrans hP hPinned

end Finish
end Proof
end RH

import rh.RS.XiExtBridge
import rh.academic_framework.CompletedXi
import rh.Proof.Main

/-!
CR-outer backup route: transport removable existence from `ξ_ext`-zeros to `ζ`-zeros
and conclude Mathlib's `RiemannHypothesis`.

Given, for each `ξ_ext`-zero `ρ ∈ Ω`, an isolating open set `U ⊆ Ω` and a
removable analytic extension `g` of `Θ := Θ_of CRGreenOuterData` across `ρ`
with `g ρ = 1` and a nontriviality witness, we transport this assignment to the
`ζ`-zeros using `CompletedXi.xi_ext_zeros_eq_zeta_zeros_on_Ω` and then invoke
the existing CR-outer removable wrapper.
-/

noncomputable section

namespace RH
namespace Proof
namespace Finish

open RH.AcademicFramework.CompletedXi

/-- CR-outer backup route (removable-existence form).

From a removable-extension assignment at each `ξ_ext` zero on `Ω` for
`Θ := Θ_of CRGreenOuterData`, transport the assignment to `ζ`-zeros via
`xi_ext_zeros_eq_zeta_zeros_on_Ω` and conclude Mathlib's `RiemannHypothesis`
using the existing CR-outer removable wrapper. -/
theorem RiemannHypothesis_cr_outer
  (hRemXi : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
        AnalyticOn ℂ (RH.RS.Θ_of RH.RS.CRGreenOuterData) (U \ {ρ}) ∧
        Set.EqOn (RH.RS.Θ_of RH.RS.CRGreenOuterData) g (U \ {ρ}) ∧
        g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : RiemannHypothesis := by
  -- Transport the assignment from `ξ_ext`-zeros to `ζ`-zeros on Ω
  have hRemZeta :
    ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (RH.RS.Θ_of RH.RS.CRGreenOuterData) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Θ_of RH.RS.CRGreenOuterData) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 :=
    RH.RS.assign_fromXiExtRemovable
      (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (assignXi := hRemXi)
  -- Apply the CR-outer removable route on the transported ζ-assignment
  exact RH.Proof.Final.RiemannHypothesis_mathlib_from_CR_outer_ext_removable hRemZeta

end Finish
end Proof
end RH
