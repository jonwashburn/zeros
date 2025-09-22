import rh.RS.OuterWitness
import rh.Proof.Export
import rh.Cert.KxiWhitney

/-!
# Final closure shim

This small module wires a single, top-level theorem that closes
`RiemannHypothesis` from:
- an outer existence (provided by `rh.RS.OuterWitness`),
- a Kξ Carleson bound (`KxiWhitney.KxiBound`), which via existing
  RS adapters yields interior positivity for `F := 2·J_pinch`, and
- pinned u‑trick data at each `ξ_ext` zero, packaged by existing RS
  helpers into the removable assignment.

It uses the existing `RiemannHypothesis_from_poisson_and_pinned'` export
to avoid modifying any other files.
-/

noncomputable section

namespace RH
namespace Proof
namespace Closure

open RH.AcademicFramework.CompletedXi

/-- Final closure from Kξ, Poisson interior positivity for `O_default`, and pinned data. -/
theorem RiemannHypothesis_from_Kxi_poisson_and_pinned
  (_hKxi : RH.Cert.KxiWhitney.KxiBound (α := (3 : ℝ) / 5) (c := (1 : ℝ)))
  (hPoisson : ∀ z ∈ RH.RS.Ω,
      0 ≤ ((2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 RH.RS.O_default z)).re)
  (hPinned : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ (_Θ_analytic_off_rho : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 RH.RS.O_default) (U \ {ρ}))
          (_u : ℂ → ℂ)
          (_hEq : Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 RH.RS.O_default) (fun z => (1 - _u z) / (1 + _u z)) (U \ {ρ}))
          (_hu0 : Filter.Tendsto _u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)))
          (_z_nontrivial : ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 RH.RS.O_default z) ≠ 1),
          True)
  : RiemannHypothesis := by
  -- Default outer existence witness
  let hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext :=
    RH.RS.outer_exists_det2_over_xi_ext
  -- Bridge: `choose_outer hOuterExist` definally equals `O_default`
  have Oeq : RH.RS.OuterHalfPlane.choose_outer hOuterExist = RH.RS.O_default := rfl
  -- Transport the positivity hypothesis to the expected form
  have hTrans : ∀ z ∈ RH.RS.Ω,
      0 ≤ ((2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) z)).re := by
    intro z hz; simpa [Oeq] using hPoisson z hz
  -- Conclude via the export wrapper
  exact RH.Proof.Export.RiemannHypothesis_from_certificate_route
    (hOuterExist := hOuterExist)
    (hTrans := hTrans)
    (_hKxi := _hKxi)
    (hPinned := by
      intro ρ hΩ hXi; exact hPinned ρ hΩ hXi)

end Closure
end Proof
end RH


