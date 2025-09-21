import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import rh.academic_framework.CompletedXi
import rh.RS.Det2Outer
import rh.RS.Cayley
import rh.RS.PinnedRemovable

/-!
# Pinch certificate builder for the ext ξ route

This module packages the two load-bearing ingredients required to construct
an RS-side pinch certificate for `riemannXi_ext`:

- interior positivity: `0 ≤ Re(2 · J_pinch)` on `Ω \ Z(ξ_ext)`; and
- removable-extension existence for the Cayley transform `Θ := Θ_pinch_of det2 O`
  across each zero of `ξ_ext`.

Given these two inputs, together with the statement-level outer existence
`OuterHalfPlane.ofModulus_det2_over_xi`, we produce a concrete
`PinchCertificateExt` suitable for the final pinch wrapper.

All heavy analysis remains outside: this file only rewraps the two
assumptions into the certificate structure via `PinchCertificateExt.of_pinch`.
-/

noncomputable section

namespace RH
namespace RS

open Complex RH.AcademicFramework.CompletedXi

/-- Shorthand for the right half–plane domain. -/
local notation "Ω" => RH.RS.Ω

/-- Build a `PinchCertificateExt` from:

1) a statement-level outer existence `O` for the boundary modulus `|det2/ξ_ext|`;
2) an interior-positivity witness for `2·J_pinch` off `Z(ξ_ext)`; and
3) a removable-extension witness for the associated `Θ := Θ_pinch_of det2 O`
   at each zero of `ξ_ext`.

This is a thin constructor that uses `PinchCertificateExt.of_pinch` under the hood.
-/
def buildPinchCertificate
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (hRe_offXi : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re)
  (hRemXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter)) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : PinchCertificateExt := by
  classical
  -- Choose an outer `O` from the existence witness
  let O : ℂ → ℂ := Classical.choose hOuter
  -- Package the two ingredients using the paper's `J_pinch` choice
  exact PinchCertificateExt.of_pinch det2 O
    (by
      intro z hz
      simpa using (hRe_offXi z hz))
    (by
      intro ρ hΩ hXi
      simpa [Θ_pinch_of] using (hRemXi ρ hΩ hXi))

/-- Build a `PinchCertificateExt` from outer existence, interior positivity on
the off-zeros set, and pinned u-trick data giving removable extensions for the
pinch `Θ`. -/
def buildPinchCertificate_from_pinned
  (hDet2 : Det2OnOmega)
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (hRe_offXi : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re)
  (hPinnedData : ∀ ρ ∈ Ω, riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter))
                   (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (Θ_pinch_of det2 (Classical.choose hOuter)) z ≠ 1)
  : PinchCertificateExt := by
  classical
  -- Use the generic builder once we have the removable assignment
  -- Convert pinned data into the removable assignment expected by `of_interfaces`
  refine PinchCertificateExt.of_interfaces (hDet2 := hDet2)
    (hOuter := hOuter) (hRe := hRe_offXi) (hRem := ?hRem)
  · -- Removable assignment from pinned data using the builder in PinnedRemovable
    intro ρ hΩ hXi
    -- hPinnedData already includes isolation equality; thread through the RS builder
    -- by directly constructing g via update using the pinned data.
    rcases hPinnedData ρ hΩ hXi with
      ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi, hΘU, u, hEq, hu0,
        z0, hz0U, hz0ne, hΘz0ne⟩
    -- Align Θ with the expected `OuterHalfPlane.choose_outer` choice
    let Θ := Θ_pinch_of det2 (OuterHalfPlane.choose_outer hOuter)
    have hΘU' : AnalyticOn ℂ Θ (U \ {ρ}) := by
      simpa [Θ, OuterHalfPlane.choose_outer] using hΘU
    have hEq' : Set.EqOn Θ (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) := by
      simpa [Θ, OuterHalfPlane.choose_outer] using hEq
    -- Build the removable extension directly via the u‑trick helper
    have pin := RH.RS.removable_pinned_from_u_trick Θ u U ρ hUopen hρU hΘU' hEq' hu0 z0 hz0U hz0ne hΘz0ne
    rcases pin with ⟨_Uopen, _ρmem, g, hgU, hEqOff, hgρ, ⟨w, hwU, hwne, hgwne⟩⟩
    refine ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi, ?_⟩
    -- Pack the conjunctions with explicit nesting to match the target type
    refine ⟨g, ?_, ?_, ?_⟩
    · exact hgU
    · exact by simpa [Θ] using hΘU'
    · refine ⟨(by simpa [Θ] using hEqOff), ?_⟩
      refine ⟨hgρ, ?_⟩
      exact ⟨w, ⟨hwU, hgwne⟩⟩

end RS
end RH
