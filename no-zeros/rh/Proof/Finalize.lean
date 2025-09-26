import rh.RS.OuterWitness
import rh.academic_framework.HalfPlaneOuterV2
import rh.Cert.KxiPPlus
import rh.RS.Cayley
import rh.RS.PinnedRemovable
import rh.RS.PinchIngredients
import rh.Proof.Main

/-!
Proof-layer wrappers for Poisson representation and interior nonnegativity of
the pinch field on the off-zeros set. This file adds no new assumptions to the
RS/AF layers and does not modify existing modules.
-/

noncomputable section

open Complex Set

namespace RH
namespace Proof
namespace Finalize

/-- Exported existence witness: outer on Ω with boundary modulus |det₂/ξ_ext|. -/
@[simp] def hOuter : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext :=
  RH.RS.outer_exists_det2_over_xi_ext

/-- Poisson representation on the off-zeros set for `F := F_pinch det2 O`, where
`O` is chosen from the outer existence witness. This is parameterized by:
  * `hDet2`: analyticity and nonvanishing of `det2` on `Ω` (RS interface),
  * `hXi`: analyticity of `riemannXi_ext` on `Ω`,
  * boundary measurability of `det2`, `O`, and `riemannXi_ext` along the line,
  * an explicit Poisson formula `hFormula` for `Re F` on the set.

No edits to RS/AF layers are required; this composes the existing API.
-/
 theorem hasPoissonRepOn_Fpinch_choose
  (hDet2 : RH.RS.Det2OnOmega)
  (hXi : AnalyticOn ℂ RH.AcademicFramework.CompletedXi.riemannXi_ext RH.AcademicFramework.HalfPlaneOuterV2.Ω)
  (hDet_meas : Measurable (fun t : ℝ => RH.RS.det2 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))
  (hO_meas : Measurable (fun t : ℝ => (RH.RS.OuterHalfPlane.choose_outer hOuter) (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))
  (hXi_meas : Measurable (fun t : ℝ => RH.AcademicFramework.CompletedXi.riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))
  (hFormula : ∀ z ∈ (RH.AcademicFramework.HalfPlaneOuterV2.Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter) z).re)
        = RH.AcademicFramework.HalfPlaneOuterV2.poissonIntegral
            (fun t => (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)
              (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re)
            z)
  : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter))
      (RH.AcademicFramework.HalfPlaneOuterV2.Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) := by
  classical
  let O : ℂ → ℂ := RH.RS.OuterHalfPlane.choose_outer hOuter
  have hOuterSpec := RH.RS.OuterHalfPlane.choose_outer_spec hOuter
  have hO_RS : RH.RS.OuterHalfPlane O := hOuterSpec.1
  have hBME_RS : RH.RS.BoundaryModulusEq O
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) := hOuterSpec.2
  -- Convert RS boundary-modulus equality to the AF predicate
  have hBME_AF :
      RH.AcademicFramework.HalfPlaneOuterV2.BoundaryModulusEq O
        (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) := by
    intro t
    have := hBME_RS t
    simpa [RH.RS.boundary, RH.AcademicFramework.HalfPlaneOuterV2.boundary] using this
  -- Build the Poisson representation using the AF helper
  refine RH.AcademicFramework.HalfPlaneOuterV2.pinch_poissonRepOn_offZeros
    (hDet2 := hDet2) (hO := hO_RS) (hBME := hBME_AF) (hXi := hXi)
    (hDet_meas := hDet_meas) (hO_meas := hO_meas) (hXi_meas := hXi_meas) ?_
  -- Provide the Poisson formula for Re(F)
  intro z hz
  exact hFormula z hz

/-- Interior nonnegativity on the off-zeros set from (P+) + Poisson representation. -/
 theorem hRe_offXi_from_Plus_and_Poisson
  (hDet2 : RH.RS.Det2OnOmega)
  (hXi : AnalyticOn ℂ RH.AcademicFramework.CompletedXi.riemannXi_ext RH.AcademicFramework.HalfPlaneOuterV2.Ω)
  (hDet_meas : Measurable (fun t : ℝ => RH.RS.det2 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))
  (hO_meas : Measurable (fun t : ℝ => (RH.RS.OuterHalfPlane.choose_outer hOuter) (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))
  (hXi_meas : Measurable (fun t : ℝ => RH.AcademicFramework.CompletedXi.riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)))
  (hFormula : ∀ z ∈ (RH.AcademicFramework.HalfPlaneOuterV2.Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter) z).re)
        = RH.AcademicFramework.HalfPlaneOuterV2.poissonIntegral
            (fun t => (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)
              (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re)
            z)
  (hBoundary :
    RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive
      (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)))
  : ∀ z ∈ (RH.AcademicFramework.HalfPlaneOuterV2.Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter) z).re) := by
  classical
  -- Build the Poisson representation on `Ω \ {ξ_ext = 0}`
  have hRep :=
    hasPoissonRepOn_Fpinch_choose hDet2 hXi hDet_meas hO_meas hXi_meas hFormula
  -- Transport boundary positivity into the interior on the subset
  intro z hz
  exact RH.AcademicFramework.HalfPlaneOuterV2.poissonTransportOn hRep hBoundary z hz

/-!
Additional proof-layer wrappers (Prompt 2/3): removable assignment from pinned
data, assembly of the pinch certificate, and final RH.
-/

/-- Removable assignment at `ξ_ext`-zeros from per-zero pinned data.

This is a thin proof-layer wrapper that packages the u-trick data into the
removable-extension assignment expected by the pinch certificate. It reuses the
existing RS helper `removable_assign_for_Theta_pinch_ext`.
-/
theorem hRemXi
  (hPinnedData :
    ∀ ρ ∈ RH.RS.Ω, RH.AcademicFramework.CompletedXi.riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter))
                   (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)) z ≠ 1)
  : ∀ ρ ∈ RH.RS.Ω, RH.AcademicFramework.CompletedXi.riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 :=
by
  -- Delegate to the RS builder
  exact RH.RS.removable_assign_for_Theta_pinch_ext (hOuter := hOuter) (hPinnedData := hPinnedData)

/-- Build a pinch certificate from the two proof-layer ingredients: interior
nonnegativity off zeros and removable assignment at `ξ_ext`-zeros. -/
def C
  (hRe_offXi : ∀ z ∈ (RH.AcademicFramework.HalfPlaneOuterV2.Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter) z).re))
  (hRemXi' : ∀ ρ ∈ RH.RS.Ω, RH.AcademicFramework.CompletedXi.riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : RH.RS.PinchCertificateExt :=
  RH.RS.certificate_from_pinch_ingredients hOuter
    (by
      intro z hz
      -- `F_pinch = 2·J_pinch`, so reuse `hRe_offXi` directly
      simpa [RH.AcademicFramework.HalfPlaneOuterV2.F_pinch] using hRe_offXi z hz)
    hRemXi'

/-- Final one-shot wrapper: from the two ingredients, conclude Mathlib's
`RiemannZeta.RiemannHypothesis`. -/
theorem RiemannHypothesis_complete
  (hRe_offXi : ∀ z ∈ (RH.AcademicFramework.HalfPlaneOuterV2.Ω \ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}),
      0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter) z).re))
  (hRemXi' : ∀ ρ ∈ RH.RS.Ω, RH.AcademicFramework.CompletedXi.riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | RH.AcademicFramework.CompletedXi.riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuter)) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : RiemannHypothesis := by
  exact RH.Proof.Export.RiemannHypothesis_final (C hRe_offXi hRemXi')

end Finalize
end Proof
end RH
