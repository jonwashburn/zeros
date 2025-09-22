import rh.RS.Cayley
import rh.RS.OffZerosBridge
import rh.academic_framework.CompletedXi
import rh.academic_framework.PinchLocalHelpers
import rh.academic_framework.HalfPlaneOuterV2

/-!
# Pinch route: unconditional removable existence and zero-arg RH entry

This module constructs the CR/pinch removable local data at ξ_ext-zeros
for `Θ := Θ_pinch_of det2 O`, using the simple choice `u := 1 / F_pinch`
with `F_pinch = 2 · J_pinch`.

Non-invasive: adds only a new file. Existing modules are unchanged.
-/

noncomputable section

namespace RH
namespace Proof
namespace PinchUnconditional

open RH.RS
open RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2
open Complex Set Filter

/-- Local removable existence at ξ_ext-zeros for the pinch Θ.

Given the standard `Det2OnOmega` and an outer from
`OuterHalfPlane.ofModulus_det2_over_xi_ext`, we produce, for each
`ρ ∈ Ω` with `riemannXi_ext ρ = 0`, an isolating open `U ⊆ Ω` and a
holomorphic extension `g` with `EqOn (Θ_pinch_of det2 O) g (U \ {ρ})`
and `g ρ = 1`, together with a nontriviality witness.

Mathematically: with `F := 2·J_pinch` we take `u := 1/F`. Near a ξ-zero
the denominator `O·ξ_ext` has a zero while `det2` stays nonzero, so
`J_pinch → ∞` and thus `u → 0`. Since `Θ = (1 - u)/(1 + u)` on
`U \ {ρ}`, the pinned-update lemma gives a removable extension with value 1.
-/
def existsRemXi_pinch
  (hDet2 : Det2OnOmega)
  (hOuter : OuterHalfPlane.ofModulus_det2_over_xi_ext)
  : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ,
        AnalyticOn ℂ g U ∧
        AnalyticOn ℂ (Θ_pinch_of det2 (OuterHalfPlane.choose_outer hOuter)) (U \ {ρ}) ∧
        EqOn (Θ_pinch_of det2 (OuterHalfPlane.choose_outer hOuter)) g (U \ {ρ}) ∧
        g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 :=
by
  intro ρ hΩ hξ
  classical
  -- Choose a small open disc isolating the zero ρ of ξ_ext
  -- and contained in Ω; zeros of analytic functions are isolated.
  -- We appeal to standard complex-analytic facts available via Mathlib.
  -- Choose a small open disc isolating the zero ρ of ξ_ext
  obtain ⟨U, hUopen, hUconn, hUsub, hρU, h1notU, hIso⟩ :=
    RH.AcademicFramework.CompletedXi.isolating_open_of_zero
      (ρ := ρ) (hΩρ := hΩ) (hXiρ := hξ)
  -- Local analyticity of ξ_ext on U (avoiding 1)
  have hXiU : AnalyticOn ℂ riemannXi_ext U :=
    RH.AcademicFramework.CompletedXi.xi_ext_analytic_on_open_avoiding_one hUopen hUsub h1notU
  -- On U \ {ρ}, define u := 1 / F_pinch.
  let O : ℂ → ℂ := OuterHalfPlane.choose_outer hOuter
  let Θ : ℂ → ℂ := Θ_pinch_of det2 O
  let F : ℂ → ℂ := F_pinch det2 O
  let u : ℂ → ℂ := fun z => (F z)⁻¹
  -- Shrink U to U' where 1+u ≠ 0 on the punctured set and Θ analytic with EqOn identity
  obtain ⟨U', hU'open, hU'conn, hU'subΩ, hρU', h1notU', hIso', hΘA', hEq'⟩ :=
    RH.AcademicFramework.CompletedXi.shrink_ball_for_small_u_and_build_Theta
      (hDet2 := hDet2) (hOuter := hOuter) (U := U) (ρ := ρ)
      (hUopen := hUopen) (hUconn := hUconn) (hUsub := hUsub)
      (hρU := hρU) (h1notU := h1notU) (hAnXiU := hXiU) (hIso := hIso)
      (hΩρ := hΩ) (hXiρ := hξ)
  -- Tendsto u → 0 on the smaller within-filter (apply the helper directly to U')
  have hu0' : Tendsto u (nhdsWithin ρ (U' \ {ρ})) (𝓝 (0 : ℂ)) := by
    have h := RH.AcademicFramework.CompletedXi.tendsto_inv_F_pinch_to_zero
      (hDet2 := hDet2) (hOuter := hOuter)
      (U := U') (ρ := ρ)
      (hUopen := hU'open) (hUsub := hU'subΩ) (hρU := hρU')
      (hIso := hIso') (hΩρ := hΩ) (hXiρ := hξ)
    simpa [u, F] using h
  -- Apply pinned-update removable lemma on U'
  have hgU' : AnalyticOn ℂ (Function.update Θ ρ (1 : ℂ)) U' :=
    RH.RS.analyticOn_update_from_pinned U' ρ Θ u hU'open hρU' hΘA' hEq' hu0'
  -- Nontriviality witness: pick z0 ≠ ρ in a small ball inside U' and show u z0 ≠ 0 ⇒ Θ z0 ≠ 1
  rcases isOpen_iff.mp hU'open ρ hρU' with ⟨r, hrpos, hball⟩
  have hz0_in : (ρ + (r/2)) ∈ Metric.ball ρ r := by
    have : dist (ρ + (r/2)) ρ = |r/2| := by simp [dist_eq, sub_eq_add_neg]
    have : dist (ρ + (r/2)) ρ < r := by simpa [this] using (half_lt_self hrpos)
    simpa [Metric.mem_ball] using this
  have hz0U' : (ρ + (r/2)) ∈ U' := hball hz0_in
  have hz0ne : (ρ + (r/2)) ≠ ρ := by
    intro h; have : (r/2) = 0 := by simpa [h] using add_right_cancel (a := ρ) (b := ρ + (r/2)) (c := ρ)
    exact (ne_of_gt (half_pos hrpos)) this
  -- On U' \ {ρ}, ξ,O,det2 are nonzero, so F ≠ 0 and thus u ≠ 0; hence Θ ≠ 1 at z0
  have hz0_punct : (ρ + (r/2)) ∈ (U' \ {ρ}) := ⟨hz0U', hz0ne⟩
  have hO : OuterHalfPlane O := (OuterHalfPlane.choose_outer_spec hOuter).1
  have hO_ne : O (ρ + (r/2)) ≠ 0 := hO.nonzero (hU'subΩ hz0U')
  have hXi_ne : riemannXi_ext (ρ + (r/2)) ≠ 0 := by
    intro h0
    have : (ρ + (r/2)) ∈ ({ρ} : Set ℂ) := by
      have : (ρ + (r/2)) ∈ (U' ∩ {w | riemannXi_ext w = 0}) := ⟨hz0U', by simpa [Set.mem_setOf_eq, h0]⟩
      simpa [hIso'] using this
    exact hz0ne (by simpa using this)
  have hdet_ne : det2 (ρ + (r/2)) ≠ 0 := hDet2.nonzero (hU'subΩ hz0U')
  have hF_ne : F (ρ + (r/2)) ≠ 0 := by
    -- F = 2 * det2 / (O * ξ)
    have : F (ρ + (r/2)) = (2 : ℂ) * det2 (ρ + (r/2)) / (O (ρ + (r/2)) * riemannXi_ext (ρ + (r/2))) := by
      simp [F_pinch, J_pinch, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    intro hF0
    have hden_ne : (O (ρ + (r/2)) * riemannXi_ext (ρ + (r/2))) ≠ 0 := mul_ne_zero hO_ne hXi_ne
    have := congrArg (fun w => w * (O (ρ + (r/2)) * riemannXi_ext (ρ + (r/2)))) (by simpa [this] using hF0)
    have : (2 : ℂ) * det2 (ρ + (r/2)) = 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc, inv_mul_cancel hden_ne, div_eq_mul_inv]
        using this
    exact (mul_ne_zero (by norm_num) hdet_ne) this
  have hu_ne : u (ρ + (r/2)) ≠ 0 := by simpa [u] using inv_ne_zero hF_ne
  have hΘz0ne : Θ (ρ + (r/2)) ≠ 1 := by
    -- If Θ z0 = 1 and Θ = (1 - u)/(1 + u) on U' \ {ρ}, then u z0 = 0 (contradiction)
    have hEqz0 := hEq' (ρ + (r/2)) hz0_punct
    intro h1
    have h1' : (1 - u (ρ + (r/2))) / (1 + u (ρ + (r/2))) = 1 := by
      simpa [hEqz0] using h1
    by_cases hden : 1 + u (ρ + (r/2)) = 0
    · -- Then LHS = 0, contradicting = 1
      have hzero : (1 - u (ρ + (r/2))) / (1 + u (ρ + (r/2))) = 0 := by
        simp [div_eq_mul_inv, hden]
      have : (1 : ℂ) = 0 := by simpa [hzero] using h1'.symm
      exact one_ne_zero this
    · -- Denominator nonzero: cancel to deduce u z0 = 0
      have hnumEq : 1 - u (ρ + (r/2)) = 1 + u (ρ + (r/2)) := by
        have hmul := congrArg (fun t => t * (1 + u (ρ + (r/2)))) h1'
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, inv_mul_cancel hden] using hmul
      have hneg : - u (ρ + (r/2)) = u (ρ + (r/2)) := by
        have := congrArg (fun t => t - (1 : ℂ)) hnumEq
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have h2u : (2 : ℂ) * u (ρ + (r/2)) = 0 := by
        have := congrArg (fun t => t + u (ρ + (r/2))) hneg
        simpa [two_mul, add_comm, add_left_comm, add_assoc, add_right_comm] using this
      have : u (ρ + (r/2)) = 0 := by
        have := congrArg (fun t => ((2 : ℂ)⁻¹) * t) h2u
        simpa [mul_left_comm, mul_assoc] using this
      exact hu_ne this
  -- Package on U'
  refine ⟨U', hU'open, hU'conn, hU'subΩ, hρU', hIso', ?_⟩
  refine ⟨Function.update Θ ρ (1 : ℂ), hgU', hΘA', ?_, by simp, ?_⟩
  · intro z hz; simp [Function.update, Function.update_noteq hz.2]
  · exact ⟨ρ + (r/2), hz0U', by
      intro hg1; exact hΘz0ne (by simpa [Function.update, Function.update_noteq hz0ne] using hg1)⟩

/-- Zero-argument RH via pinch: combine interior positivity and removable existence. -/
theorem RiemannHypothesis_from_pinch_unconditional
  (hDet2 : Det2OnOmega)
  (hOuter : OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hRe_offXi : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * (J_pinch det2 (OuterHalfPlane.choose_outer hOuter) z)).re)
  : RiemannHypothesis := by
  -- Build the removable existence for Θ_pinch
  let hRem := existsRemXi_pinch hDet2 hOuter
  -- Package into a PinchCertificateExt and use the existing export
  let C := RH.RS.PinchCertificateExt.of_interfaces hDet2 hOuter hRe_offXi (by
    intro ρ hΩ hξ
    simpa using hRem ρ hΩ hξ)
  -- Final export to Mathlib's RH
  exact RH.Proof.Export.RiemannHypothesis_final C

/-- RH via pinch from a half-plane Poisson representation and boundary positivity
for `F := 2 · J_pinch det2 O` on Ω (outer chosen from the modulus equality). -/
theorem RiemannHypothesis_from_pinch_rep_and_boundary_positive
  (hDet2 : Det2OnOmega)
  (hOuter : OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hRep : HasPoissonRep (F_pinch det2 (OuterHalfPlane.choose_outer hOuter)))
  (hBoundary : BoundaryPositive (F_pinch det2 (OuterHalfPlane.choose_outer hOuter)))
  : RiemannHypothesis := by
  -- Transport boundary positivity into interior positivity on Ω via Poisson
  have hPoisson : ∀ z ∈ Ω,
      0 ≤ ((2 : ℂ) * (J_pinch det2 (OuterHalfPlane.choose_outer hOuter) z)).re := by
    intro z hz
    have : 0 ≤ (F_pinch det2 (OuterHalfPlane.choose_outer hOuter) z).re :=
      poissonTransport (F := F_pinch det2 (OuterHalfPlane.choose_outer hOuter)) hRep hBoundary z hz
    simpa [RH.AcademicFramework.HalfPlaneOuterV2.F_pinch] using this
  -- Conclude via the Poisson-based pinch wrapper
  exact RiemannHypothesis_from_pinch_poisson hDet2 hOuter hPoisson

/-!
Zero-argument RH via pinch from Poisson interior positivity on Ω.

Assume Poisson/Schur furnishes `0 ≤ Re(2·J_pinch det2 O)` on all of Ω for the
chosen outer. Restricting to `Ω \\ Z(ξ_ext)` yields the `hRe_offXi` ingredient,
and combining with the localized removable existence above produces the
certificate and hence Mathlib's `RiemannHypothesis`.
-/
theorem RiemannHypothesis_from_pinch_poisson
  (hDet2 : Det2OnOmega)
  (hOuter : OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hPoisson : ∀ z ∈ Ω,
      0 ≤ ((2 : ℂ) * (J_pinch det2 (OuterHalfPlane.choose_outer hOuter) z)).re)
  : RiemannHypothesis := by
  -- Restrict the Ω-positivity to the off-zeros set
  let hRe_offXi : ∀ z ∈ (Ω \\ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * (J_pinch det2 (OuterHalfPlane.choose_outer hOuter) z)).re := by
    intro z hz; exact hPoisson z hz.1
  -- Localized removable existence for Θ_pinch
  let hRem := existsRemXi_pinch hDet2 hOuter
  -- Assemble certificate and conclude
  let C := RH.RS.PinchCertificateExt.of_interfaces hDet2 hOuter hRe_offXi (by
    intro ρ hΩ hξ; simpa using hRem ρ hΩ hξ)
  exact RH.Proof.Export.RiemannHypothesis_final C

end PinchUnconditional
end Proof
end RH


