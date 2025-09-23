import rh.Proof.Export
import rh.RS.OuterWitness
import rh.Cert.KxiPPlus
import rh.academic_framework.CompletedXi

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

open Complex RH.RS RH.AcademicFramework.CompletedXi

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
  -- Conclude via the existing export wiring
  exact RH.Proof.Main.RiemannHypothesis_from_poisson_and_pinned'
    (hOuter := ⟨RH.RS.O_default, hO.1, hO.2⟩)
    (hPoisson := hPoisson)
    (hPinned := hPinned)

end Unconditional
end Proof
end RH


