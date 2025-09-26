import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.RS.OuterWitness
import rh.academic_framework.CompletedXi
import rh.academic_framework.PinchLocalHelpers

/-!
# Pinned u-trick data at ξ_ext-zeros for `O_default` (no chooser)

This module provides the pinned-removability local data required by the
unconditional entry, specialized to the concrete choice `O_default` exported
by `rh.RS.OuterWitness`.

For each zero `ρ` of `riemannXi_ext` in `Ω`, we construct an isolating open
neighborhood `U ⊆ Ω` and define a function `u` on `U \ {ρ}` such that

- `Θ := Θ_pinch_of det2 O_default` is analytic on `U \ {ρ}`;
- on `U \ {ρ}`, we have the identity `Θ = (1 - u) / (1 + u)`;
- `u → 0` along the within-filter `𝓝[U \ {ρ}] ρ`;
- there is a point `z ∈ U`, `z ≠ ρ`, with `Θ z ≠ 1`.

The construction follows the pattern in `rh/Proof/PinchUnconditional.lean` and
uses the local helpers in `rh/academic_framework/PinchLocalHelpers.lean`.
-/

noncomputable section

namespace RH
namespace Proof

open Complex Set Filter RH.RS RH.AcademicFramework.CompletedXi

/-- Pinned u‑trick data at `ξ_ext` zeros for the default outer `O_default`.

Inputs: a `Det2OnOmega` interface witnessing analyticity and nonvanishing of
`det2` on `Ω`.

Output: for every `ρ ∈ Ω` with `riemannXi_ext ρ = 0`, an isolating open
neighborhood `U ⊆ Ω` on which `Θ := Θ_pinch_of det2 O_default` is analytic off
`ρ`, agrees with the Möbius transform `(1 - u)/(1 + u)` for a function `u`
that tends to `0` along `𝓝[U \ {ρ}] ρ`, and admits a point in `U` where
`Θ ≠ 1`.
-/
theorem hPinned_default
  (hDet2 : Det2OnOmega)
  : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      AnalyticOn ℂ (Θ_pinch_of det2 O_default) (U \ {ρ}) ∧
      ∃ u : ℂ → ℂ,
        Set.EqOn (Θ_pinch_of det2 O_default)
                 (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
        Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
        ∃ z, z ∈ U ∧ z ≠ ρ ∧ (Θ_pinch_of det2 O_default) z ≠ 1 := by
  intro ρ hΩ hξ
  classical
  -- Isolating open disc `U ⊆ Ω` avoiding `1`, with `U ∩ {ξ_ext = 0} = {ρ}`
  obtain ⟨U, hUopen, hUconn, hUsub, hρU, h1notU, hIso⟩ :=
    isolating_open_of_zero (ρ := ρ) (hΩρ := hΩ) (hXiρ := hξ)
  -- Local analyticity of `riemannXi_ext` on `U`
  have hXiU : AnalyticOn ℂ riemannXi_ext U :=
    xi_ext_analytic_on_open_avoiding_one hUopen hUsub h1notU
  -- Outer existence witness and identification with `O_default`
  let hOuter := outer_exists_det2_over_xi_ext
  -- Shrink and build Θ-analyticity and the EqOn identity on `U' \ {ρ}`
  obtain ⟨U', hU'open, hU'conn, hU'subΩ, hρU', h1notU', hIso', hΘA', hEq'⟩ :=
    shrink_ball_for_small_u_and_build_Θ
      (hDet2 := hDet2) (hOuter := hOuter) (U := U) (ρ := ρ)
      (hUopen := hUopen) (hUconn := hUconn) (hUsub := hUsub)
      (hρU := hρU) (h1notU := h1notU) (hAnXiU := hXiU) (hIso := hIso)
      (hΩρ := hΩ) (hXiρ := hξ)
  -- Identify the chosen outer with `O_default` and specialize the conclusions
  have hOdef : OuterHalfPlane.choose_outer hOuter = O_default := rfl
  have hΘA : AnalyticOn ℂ (Θ_pinch_of det2 O_default) (U' \ {ρ}) := by
    simpa [Θ_pinch_of, hOdef] using hΘA'
  let u : ℂ → ℂ := fun z => (F_pinch det2 O_default z)⁻¹
  have hEq : Set.EqOn (Θ_pinch_of det2 O_default)
      (fun z => (1 - u z) / (1 + u z)) (U' \ {ρ}) := by
    simpa [Θ_pinch_of, F_pinch, hOdef, u] using hEq'
  -- Limit `u → 0` along the within-filter on `U' \ {ρ}`
  have hu0 : Filter.Tendsto u (nhdsWithin ρ (U' \ {ρ})) (nhds (0 : ℂ)) := by
    have := tendsto_inv_F_pinch_to_zero
      (hDet2 := hDet2) (hOuter := hOuter) (U := U') (ρ := ρ)
      (hUopen := hU'open) (hUsub := hU'subΩ) (hρU := hρU') (hIso := hIso')
      (hΩρ := hΩ) (hXiρ := hξ)
    simpa [F_pinch, hOdef, u] using this
  -- Pick an explicit point `z0 ∈ U'`, `z0 ≠ ρ`
  have hU'n : U' ∈ 𝓝 ρ := hU'open.mem_nhds hρU'
  rcases Metric.mem_nhds_iff.1 hU'n with ⟨r, hrpos, hball_sub⟩
  let z0 : ℂ := ρ + (r / 2 : ℂ)
  have hz0_ball : z0 ∈ Metric.ball ρ r := by
    -- dist z0 ρ = |r/2| = r/2 < r
    have hdist_lt : Complex.abs ((r / 2 : ℝ) : ℂ) < r := by
      have : (r / 2 : ℝ) < r := by
        have hrpos' : (0 : ℝ) < r := hrpos
        have : (0 : ℝ) < r / 2 := by exact half_pos hrpos'
        nlinarith
      simpa [Complex.abs_ofReal, abs_of_nonneg (by exact (half_pos hrpos).le)] using this
    simpa [Metric.mem_ball, z0, Complex.dist_eq, sub_eq_add_neg,
           add_comm, add_left_comm, add_assoc]
      using hdist_lt
  have hz0U' : z0 ∈ U' := hball_sub hz0_ball
  have hz0ne : z0 ≠ ρ := by
    -- Since dist z0 ρ = r/2 > 0, we have z0 ≠ ρ
    have hdist_pos : 0 < dist z0 ρ := by
      have : (0 : ℝ) < r / 2 := half_pos hrpos
      have : Complex.abs ((r / 2 : ℝ) : ℂ) = r / 2 := by
        simpa [Complex.abs_ofReal, abs_of_nonneg (by exact (half_pos hrpos).le)]
      have : dist z0 ρ = r / 2 := by
        calc
          dist z0 ρ = Complex.abs (z0 - ρ) := by simp [Complex.dist_eq]
          _ = Complex.abs ((r / 2 : ℂ)) := by
                simp [z0, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          _ = r / 2 := by simpa [Complex.abs_ofReal,
                                  abs_of_nonneg (by exact (half_pos hrpos).le)]
      simpa [this] using (half_pos hrpos)
    have : dist z0 ρ ≠ 0 := ne_of_gt hdist_pos
    simpa [dist_eq_zero] using this
  -- Nonvanishing of all factors at `z0 ∈ U' \ {ρ}`
  have hz0_punct : z0 ∈ (U' \ {ρ}) := ⟨hz0U', hz0ne⟩
  have hO : OuterHalfPlane O_default := (O_default_spec).1
  have hO_ne : O_default z0 ≠ 0 := hO.nonzero (hU'subΩ hz0U')
  have hXi_ne : riemannXi_ext z0 ≠ 0 := by
    intro h0
    have : z0 ∈ ({ρ} : Set ℂ) := by
      have : z0 ∈ (U' ∩ {w | riemannXi_ext w = 0}) :=
        ⟨hz0U', by simpa [Set.mem_setOf_eq] using h0⟩
      simpa [hIso'] using this
    exact hz0ne (by simpa using this)
  have hdet_ne : det2 z0 ≠ 0 := hDet2.nonzero (hU'subΩ hz0U')
  -- Hence `F ≠ 0` and so `u z0 ≠ 0`
  have hF_ne : F_pinch det2 O_default z0 ≠ 0 := by
    -- If F z0 = 0, then (2·det2 z0) = 0 by multiplying by the nonzero denominator
    have hF_id : F_pinch det2 O_default z0
        = (2 : ℂ) * det2 z0 / (O_default z0 * riemannXi_ext z0) := by
      simp [F_pinch, J_pinch, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    intro hF0
    have hden_ne : (O_default z0 * riemannXi_ext z0) ≠ 0 := mul_ne_zero hO_ne hXi_ne
    have := congrArg (fun w => w * (O_default z0 * riemannXi_ext z0)) (by simpa [hF_id] using hF0)
    have : (2 : ℂ) * det2 z0 = 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc, inv_mul_cancel hden_ne,
             div_eq_mul_inv] using this
    exact (mul_ne_zero (by norm_num) hdet_ne) this
  have hu_ne : u z0 ≠ 0 := by simpa [u] using inv_ne_zero hF_ne
  -- Conclude nontriviality: Θ z0 ≠ 1 via the Möbius identity on `U' \ {ρ}`
  have hΘ_ne1 : (Θ_pinch_of det2 O_default) z0 ≠ 1 := by
    -- Use the EqOn identity at z0 and split on the denominator
    have hEqz0 := hEq z0 hz0_punct
    intro h1
    have h1' : (1 - u z0) / (1 + u z0) = 1 := by simpa [hEqz0] using h1
    by_cases hden : 1 + u z0 = 0
    · have hzero : (1 - u z0) / (1 + u z0) = 0 := by simp [div_eq_mul_inv, hden]
      have : (1 : ℂ) = 0 := by simpa [hzero] using h1'.symm
      exact one_ne_zero this
    · have hnumEq : 1 - u z0 = 1 + u z0 := by
        have hmul := congrArg (fun t => t * (1 + u z0)) h1'
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, inv_mul_cancel hden] using hmul
      have hneg : -u z0 = u z0 := by
        have := congrArg (fun t => t - (1 : ℂ)) hnumEq
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have h2u : (2 : ℂ) * u z0 = 0 := by
        have := congrArg (fun t => t + u z0) hneg
        simpa [two_mul, add_comm, add_left_comm, add_assoc, add_right_comm] using this
      have : u z0 = 0 := by
        have := congrArg (fun t => ((2 : ℂ)⁻¹) * t) h2u
        simpa [mul_left_comm, mul_assoc] using this
      exact hu_ne this
  -- Package the result on `U'`
  refine ⟨U', hU'open, hU'conn, hU'subΩ, hρU', hIso', ?_ , ?_⟩
  · simpa [Θ_pinch_of, hOdef] using hΘA'
  · refine ⟨u, hEq, hu0, ?_⟩
    exact ⟨z0, hz0U', hz0ne, hΘ_ne1⟩

end Proof
end RH
