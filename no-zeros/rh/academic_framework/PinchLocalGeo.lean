import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import rh.academic_framework.CompletedXi
import rh.academic_framework.ZetaFunctionalEquation
import rh.RS.Domain

/-!
# Local geometry and analyticity helpers for ξ_ext on small balls

This file provides two basic lemmas used by the pinch-local pipeline:

- `xi_ext_analytic_on_ball_avoiding_one`: ξ_ext is analytic on any ball contained
  in Ω and avoiding 1.
- `exists_ball_in_Ω_avoiding_one`: around a ξ_ext-zero ρ ∈ Ω, there is a small
  ball contained in Ω that avoids 1.
-/

noncomputable section

namespace RH
namespace AcademicFramework
namespace CompletedXi

open Complex Set RH.RS

/-– Local analyticity of ξ_ext on opens avoiding 1. -/
lemma xi_ext_analytic_on_open_avoiding_one
  {U : Set ℂ} (hUopen : IsOpen U) (hUsub : U ⊆ Ω) (h1 : (1 : ℂ) ∉ U) :
  AnalyticOn ℂ riemannXi_ext U := by
  classical
  -- AnalyticOn ↔ DifferentiableOn on open sets
  refine (analyticOn_iff_differentiableOn (f := riemannXi_ext) (s := U) hUopen).2 ?h
  intro z hzU
  have hzΩ : z ∈ Ω := hUsub hzU
  have hz_ne0 : z ≠ 0 := by
    have hzRe : (1 / 2 : ℝ) < z.re := by simpa [Ω, mem_setOf_eq] using hzΩ
    intro hz; simpa [hz, Complex.zero_re] using (lt_trans (by norm_num : (0 : ℝ) < 1/2) hzRe)
  have hz_ne1 : z ≠ 1 := by intro hz1; exact h1 (by simpa [hz1] using hzU)
  have hdiff : DifferentiableAt ℂ completedRiemannZeta z :=
    differentiableAt_completedZeta (s := z) hz_ne0 hz_ne1
  simpa [riemannXi_ext] using hdiff.differentiableWithinAt

lemma xi_ext_analytic_on_ball_avoiding_one
  {ρ : ℂ} {r : ℝ}
  (hsub : Metric.ball ρ r ⊆ Ω) (h1 : (1 : ℂ) ∉ Metric.ball ρ r) :
  AnalyticOn ℂ riemannXi_ext (Metric.ball ρ r) := by
  classical
  have hopen : IsOpen (Metric.ball ρ r) := Metric.isOpen_ball
  -- Use existing open-set lemma from PinchLocalHelpers to avoid duplication
  exact RH.AcademicFramework.CompletedXi.xi_ext_analytic_on_open_avoiding_one
    (U := Metric.ball ρ r) hopen hsub h1

lemma exists_ball_in_Ω_avoiding_one {ρ : ℂ}
  (hΩρ : ρ ∈ Ω) (hXiρ : riemannXi_ext ρ = 0) :
  ∃ r > 0, Metric.ball ρ r ⊆ Ω ∧ (1 : ℂ) ∉ Metric.ball ρ r := by
  classical
  -- helper: ξ_ext(1) ≠ 0 ⇒ ρ ≠ 1
  have ρ_ne1 : ρ ≠ 1 := by
    intro h
    -- Reprove ξ_ext(1) ≠ 0 (duplicated locally to avoid private lemma dependency)
    have xi_ext_nonzero_at_one : riemannXi_ext 1 ≠ 0 := by
      intro hΛ
      change completedRiemannZeta 1 = 0 at hΛ
      have hζdef : riemannZeta 1 = completedRiemannZeta 1 / Complex.Gammaℝ 1 :=
        riemannZeta_def_of_ne_zero (s := (1 : ℂ)) one_ne_zero
      have hζ0 : riemannZeta 1 = 0 := by
        rw [hζdef, hΛ]; simp
      exact riemannZeta_one_ne_zero hζ0
    exact xi_ext_nonzero_at_one (by simpa [h] using hXiρ)
  -- Work inside T = Ω ∩ {z ≠ 1}
  let T : Set ℂ := Ω ∩ {z : ℂ | z ≠ 1}
  have hTopen : IsOpen T := by
    have hΩopen : IsOpen Ω := by
      simpa [Ω, mem_setOf_eq] using isOpen_lt continuous_const Complex.continuous_re
    exact hΩopen.inter isOpen_ne
  have hρT : ρ ∈ T := ⟨hΩρ, by simpa [Set.mem_setOf_eq] using ρ_ne1⟩
  rcases Metric.mem_nhds_iff.1 (hTopen.mem_nhds hρT) with ⟨r, hrpos, hball_sub_T⟩
  refine ⟨r, hrpos, ?_, ?_⟩
  · intro z hz; exact (hball_sub_T hz).1
  · intro h1; exact (hball_sub_T h1).2 rfl

end CompletedXi
end AcademicFramework
end RH
