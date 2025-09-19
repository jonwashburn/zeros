import rh.Proof.Main

/-!
Final wiring exports: clean, stable entry points that expose Mathlib's
`RiemannZeta.RiemannHypothesis` through the assembled RS/AF routes.

These theorems do not introduce any new assumptions beyond those
appearing in `rh/Proof/Main.lean`. They are placed in a thin wrapper
module so downstream users can import only this file for the final API.
-/

open RH.AcademicFramework.CompletedXi

namespace RH.Proof.Export

-- Unconditional pipeline readiness via the certificate layer
abbrev PipelineReady := RH.Proof.PipelineReady

theorem pipeline_ready_unconditional : PipelineReady := RH.Proof.pipeline_ready_unconditional

-- Final certificate-driven alias to Mathlib's RiemannHypothesis
theorem RiemannHypothesis_final (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RH.Proof.RiemannHypothesis_final C

theorem RH (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RH.Proof.RH C

-- Certificate route variants re-exported for convenience
theorem RiemannHypothesis_from_certificate_route
  (α c : ℝ)
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hTrans : RH.RS.HasHalfPlanePoissonTransport
    (fun z => (2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) z)))
  (hKxi : RH.Cert.KxiWhitney.KxiBound α c)
  (hPinned : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ (Θ_analytic_off_rho : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (U \ {ρ}))
          (u : ℂ → ℂ)
          (hEq : Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}))
          (hu0 : Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)))
          (z_nontrivial : ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) z ≠ 1),
          True)
  : RiemannHypothesis :=
  RH.Proof.RiemannHypothesis_from_certificate_route α c hOuterExist hTrans hKxi hPinned

-- Subset-representation route
theorem RiemannHypothesis_from_certificate_rep_on_via_cov
  (α c : ℝ)
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hDet2 : RH.RS.Det2OnOmega)
  (hXiAnalytic : AnalyticOn ℂ riemannXi_ext RH.RS.Ω)
  (hKxi : RH.Cert.KxiWhitney.KxiBound α c)
  (hPinned : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ (Θ_analytic_off_rho : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (U \ {ρ}))
          (u : ℂ → ℂ)
          (hEq : Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}))
          (hu0 : Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)))
          (z_nontrivial : ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) z ≠ 1),
          True)
  : RiemannHypothesis :=
  RH.Proof.RiemannHypothesis_from_certificate_rep_on_via_cov α c hOuterExist hDet2 hXiAnalytic hKxi hPinned

-- Minimal API export to Mathlib wrapper from CR-outer route
theorem RiemannHypothesis_mathlib_from_CR_outer_ext
  (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
  (hGnz : ∀ ρ ∈ RH.RS.Ω, G_ext ρ ≠ 0)
  : RiemannHypothesis :=
  RH.Proof.Final.RiemannHypothesis_mathlib_from_CR_outer_ext choose hGnz

end RH.Proof.Export


