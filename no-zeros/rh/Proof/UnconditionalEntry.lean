import rh.Proof.Main
import rh.Proof.Export
import rh.RS.OuterWitness
import rh.Cert.KxiPPlus
import rh.academic_framework.CompletedXi
import rh.RS.PinchCertificate
import rh.RS.PinnedRemovable

/-!
# Unconditional entry (no chooser): transport + pinned u-trick

This small entry exposes a convenience theorem that derives the interior
positivity ingredient from a Poisson transport predicate together with a
Carleson budget, and combines it with pinned u‑trick data at each ξ_ext zero
to conclude Mathlib's `RiemannZeta.RiemannHypothesis`.

Inputs required:
- a Poisson transport predicate for the concrete pinch field `F := 2·J_pinch`;
- a statement-level bridge from Carleson to boundary `(P+)` for `F`;
- pinned u‑trick data at each ξ_ext zero, yielding a removable assignment for
  `Θ := Θ_pinch_of det2 (choose O)`.

The outer existence on Ω for `|det₂/ξ_ext|` is provided from `rh.RS.OuterWitness`.

This entry removes any explicit local-data chooser; it consumes only
statement-level ingredients.
-/

noncomputable section

namespace RH
namespace Proof
namespace Unconditional

open Complex RH.RS RH.AcademicFramework.CompletedXi RH.Proof

local notation "Ω" => RH.RS.Ω

/-- Unconditional entry: from a Poisson transport predicate for the pinch field,
    a Carleson→(P+) bridge, and pinned u‑trick data at each `ξ_ext` zero,
    conclude Mathlib's `RiemannHypothesis`.

`hTrans` is the transport predicate `(P+) ⇒ interior nonnegativity on Ω` for
the concrete field `F := 2 · J_pinch det2 (choose O)`; `hP` is the statement
that a Carleson budget produces `(P+)` for the same field; `hPinned` supplies
the pinned data at each `ξ_ext` zero. No chooser is required.
-/
theorem RiemannHypothesis_from_transport_and_pinned
  (hTrans : RH.Cert.PPlus
              (fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 (RH.RS.O_default) z)
            → ∀ z : ℂ, z.re > (1/2 : ℝ) →
                0 ≤ ((2 : ℂ) * RH.RS.J_pinch RH.RS.det2 (RH.RS.O_default) z).re)
  (hP : RH.Cert.PPlusFromCarleson_exists
          (fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 (RH.RS.O_default) z))
  (hPinned : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 RH.RS.O_default) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 RH.RS.O_default)
                   (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 RH.RS.O_default) z ≠ 1)
  : RiemannHypothesis := by
  -- Outer existence witness and chosen outer `O_default`
  have hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext :=
    RH.RS.outer_exists_det2_over_xi_ext
  have hO : RH.RS.OuterHalfPlane RH.RS.O_default ∧
            RH.RS.BoundaryModulusEq RH.RS.O_default
              (fun s => RH.RS.det2 s / riemannXi_ext s) :=
    RH.RS.O_default_spec
  -- Carleson existence (concrete budget); add explicit nonnegativity for the adapter
  rcases RH.Cert.exists_Carleson_from_FGammaPrime
      (σ0 := (3 : ℝ) / 5)
      (RH.AcademicFramework.GammaBounds.boundedFGammaPrimeOnStrip_of (by norm_num) (by norm_num))
    with ⟨Kξ, hConc⟩
  have hKxi : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ := ⟨Kξ, hConc.1, hConc⟩
  -- Interior positivity on Ω via the certificate-side adapter
  have hPoisson : ∀ z ∈ Ω,
      0 ≤ ((2 : ℂ) * RH.RS.J_pinch RH.RS.det2 RH.RS.O_default z).re := by
    exact RH.Cert.hPoisson_nonneg_on_Ω_from_Carleson
      (O := RH.RS.O_default)
      (hTrans := hTrans)
      (hP := hP)
      (hKxi := hKxi)
  -- Package pinch ingredients and conclude via the certificate route
  let hOuter : ∃ O : ℂ → ℂ, RH.RS.OuterHalfPlane O ∧
      RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) :=
    ⟨RH.RS.O_default, hO.1, hO.2⟩
  let hRe_offXi : ∀ z ∈ Ω \ {z | riemannXi_ext z = 0},
      0 ≤ ((2 : ℂ) * RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter) z).re :=
    fun z hz => hPoisson z hz.1
  let hRemXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (Classical.choose hOuter)) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
    intro ρ hΩ hXi0
    rcases hPinned ρ hΩ hXi0 with
      ⟨U, hUopen, hUconn, hUsub, hρU, hIso,
       hΘU, u, hEq, hu0, ⟨z0, hz0U, hz0ne, hΘz0⟩⟩
    let Θ : ℂ → ℂ := RH.RS.Θ_pinch_of RH.RS.det2 (Classical.choose hOuter)
    have hEq_ev : (fun w => Θ w) =ᶠ[nhdsWithin ρ (U \ {ρ})]
        (fun w => (1 - u w) / (1 + u w)) :=
      Set.EqOn.eventuallyEq_nhdsWithin (s := U \ {ρ}) hEq
    have _hΘ_lim1 : Filter.Tendsto Θ (nhdsWithin ρ (U \ {ρ})) (nhds (1 : ℂ)) :=
      RH.RS.Theta_pinned_limit_from_N2 (U := U \ {ρ}) (ρ := ρ) (Θ := Θ) (u := u) hEq_ev hu0
    let g : ℂ → ℂ := Function.update Θ ρ (1 : ℂ)
    have hEqOn : Set.EqOn Θ g (U \ {ρ}) := by
      intro w hw; simpa only [g, Function.update_noteq hw.2] using rfl
    have hval : g ρ = 1 := by
      classical
      simp [g]
    have hgU : AnalyticOn ℂ g U := by
      exact RH.RS.analyticOn_update_from_pinned (U := U) (ρ := ρ) (Θ := Θ) (u := u)
        hUopen hρU hΘU hEq hu0
    have nz : g z0 ≠ 1 := by
      have : g z0 = Θ z0 := by
        change Function.update Θ ρ (1 : ℂ) z0 = Θ z0
        simp [g, hz0ne]
      exact by simpa [this] using hΘz0
    exact ⟨U, hUopen, hUconn, hUsub, hρU, hIso,
      ⟨g, hgU, hΘU, hEqOn, hval, z0, hz0U, nz⟩⟩
  exact RH.Proof.Export.RiemannHypothesis_final
    (RH.RS.certificate_from_pinch_ingredients hOuter hRe_offXi hRemXi)

end Unconditional
end Proof
end RH
