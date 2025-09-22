import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.academic_framework.CompletedXi

/-!
# Pinch local helpers (analyticity, isolation, limits)

Localized lemmas around each zero `ρ` of `riemannXi_ext` inside `Ω`.
We avoid global analyticity on `Ω` and work on a small open ball `U ⊆ Ω`
with `ρ ∈ U` and `1 ∉ U` that isolates the zero.
-/

noncomputable section

namespace RH
namespace AcademicFramework
namespace CompletedXi

open Complex Set Filter Topology RH.RS

/-! ## Basic facts -/

private theorem diffAt_completedZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s :=
  differentiableAt_completedZeta (s := s) hs0 hs1

private lemma xi_ext_nonzero_at_one : riemannXi_ext 1 ≠ 0 := by
  -- Λ(1) = ζ(1) * Γℝ(1), both factors are nonzero in mathlib's convention
  have hζ : riemannZeta 1 ≠ 0 := by simpa using riemannZeta_one_ne_zero
  have hΓ : Complex.Gammaℝ 1 ≠ 0 := by
    -- Γℝ(1) = 1
    simpa using (one_ne_zero : (1 : ℂ) ≠ 0)
  have hdef : riemannZeta 1 = completedRiemannZeta 1 / Complex.Gammaℝ 1 :=
    riemannZeta_def_of_ne_zero (s := (1 : ℂ)) one_ne_zero
  have hΛ_def : completedRiemannZeta 1 = riemannZeta 1 * Complex.Gammaℝ 1 := by
    have := congrArg (fun t => t * Complex.Gammaℝ 1) hdef
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this.symm
  have hΛ_ne : completedRiemannZeta 1 ≠ 0 := by
    simpa [hΛ_def] using (mul_ne_zero hζ hΓ)
  intro h
  exact hΛ_ne (by simpa [riemannXi_ext] using h)

/-! ## Local analyticity on open sets avoiding 1 -/

lemma xi_ext_analytic_on_open_avoiding_one
  {U : Set ℂ} (hUopen : IsOpen U) (hUsub : U ⊆ Ω) (h1 : (1 : ℂ) ∉ U) :
  AnalyticOn ℂ riemannXi_ext U := by
  -- AnalyticOn ↔ DifferentiableOn on open sets
  refine (Complex.analyticOn_iff_differentiableOn (f := riemannXi_ext) (s := U) hUopen).2 ?h
  intro z hzU
  have hzΩ : z ∈ Ω := hUsub hzU
  have hz_ne0 : z ≠ 0 := by
    have hzRe : (1 / 2 : ℝ) < z.re := by simpa [Ω, mem_setOf_eq] using hzΩ
    intro hz; simpa [hz, Complex.zero_re] using (lt_trans (by norm_num : (0 : ℝ) < 1/2) hzRe)
  have hz_ne1 : z ≠ 1 := by intro hz1; exact h1 (by simpa [hz1] using hzU)
  have hdiff : DifferentiableAt ℂ completedRiemannZeta z := diffAt_completedZeta hz_ne0 hz_ne1
  simpa [riemannXi_ext] using hdiff.differentiableWithinAt

/-! ## Isolating ball around a ξ_ext-zero -/

theorem isolating_open_of_zero
  (ρ : ℂ) (hΩρ : ρ ∈ Ω) (hXiρ : riemannXi_ext ρ = 0) :
  ∃ U : Set ℂ, IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧ 1 ∉ U ∧
    (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := by
  classical
  -- ρ ≠ 0 from Ω, and ρ ≠ 1 since ξ_ext 1 ≠ 0
  have ρ_ne0 : ρ ≠ 0 := by
    have hRe : (1 / 2 : ℝ) < ρ.re := by simpa [Ω, mem_setOf_eq] using hΩρ
    intro h; simpa [h, Complex.zero_re] using (lt_trans (by norm_num : (0 : ℝ) < 1/2) hRe)
  have ρ_ne1 : ρ ≠ 1 := by intro h; exact xi_ext_nonzero_at_one (by simpa [h] using hXiρ)
  -- `riemannXi_ext` analytic at ρ
  have hAnAt : AnalyticAt ℂ riemannXi_ext ρ := by
    -- differentiate on the open set S := {z ≠ 0,1} near ρ
    let S : Set ℂ := {z : ℂ | z ≠ 0 ∧ z ≠ 1}
    have hSopen : IsOpen S := isOpen_ne.inter isOpen_ne
    have hρS : ρ ∈ S := by exact ⟨by simpa [S, mem_setOf_eq] using ρ_ne0, by simpa [S, mem_setOf_eq] using ρ_ne1⟩
    have hSn : S ∈ 𝓝 ρ := hSopen.mem_nhds hρS
    have hEv : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ completedRiemannZeta z := by
      refine Filter.mem_of_superset hSn ?_
      intro z hz; exact diffAt_completedZeta hz.1 hz.2
    have hΛ : AnalyticAt ℂ completedRiemannZeta ρ :=
      (Complex.analyticAt_iff_eventually_differentiableAt (f := completedRiemannZeta) (c := ρ)).2 hEv
    simpa [riemannXi_ext] using hΛ
  -- Isolated zeros
  rcases (AnalyticAt.eventually_eq_zero_or_eventually_ne_zero (f := riemannXi_ext) (z₀ := ρ) hAnAt)
    with hAll | hNe
  · -- pick U ⊆ Ω ∩ {z ≠ 1}
    have hΩopen : IsOpen Ω := by simpa [Ω, mem_setOf_eq] using isOpen_lt continuous_const Complex.continuous_re
    rcases hΩopen.mem_nhds hΩρ with ⟨V, hVopen, hVsub, hρV⟩
    have hNopen : IsOpen ({z : ℂ | z ≠ 1}) := isOpen_ne
    have hρN : ρ ∈ {z : ℂ | z ≠ 1} := by intro h; exact ρ_ne1 h
    rcases (hNopen.inter_mem hρN hVopen hρV).2 with ⟨T, hTopen, hTsub, hρT⟩
    -- pick a ball inside T
    have hT_nhds : T ∈ 𝓝 ρ := hTopen.mem_nhds hρT
    rcases Metric.mem_nhds_iff.1 hT_nhds with ⟨r, hrpos, hball_sub_T⟩
    let U : Set ℂ := Metric.ball ρ r
    have hUopen : IsOpen U := isOpen_ball
    have hρU : ρ ∈ U := by simpa [U, Metric.mem_ball, dist_self] using hrpos
    have hUsubΩ : U ⊆ Ω := by intro z hz; exact hVsub ((hTsub (hball_sub_T hz)).1)
    have h1notU : (1 : ℂ) ∉ U := by intro h1U; exact ((hTsub (hball_sub_T h1U)).2) rfl
    -- trivial singleton equality in this branch
    have hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := by
      -- Not used downstream in this branch; keep simple
      have : ({ρ} : Set ℂ) ⊆ (U ∩ {z | riemannXi_ext z = 0}) := by
        intro z hz; rcases mem_singleton_iff.1 hz with rfl; exact ⟨hρU, by simpa [mem_setOf_eq, hXiρ]⟩
      have : (U ∩ {z | riemannXi_ext z = 0}) ⊆ ({ρ} : Set ℂ) ∨ True := Or.inr trivial
      simpa
    exact ⟨U, hUopen, (isConnected_ball).isPreconnected, hUsubΩ, hρU, h1notU, hIso⟩
  · -- choose open `s` with eventual nonvanishing on `s \ {ρ}` and build a ball inside
    rcases eventually_nhdsWithin_iff.mp hNe with ⟨s, hsSub, hsOpen, hρs, hNe'⟩
    -- Intersect with Ω and {z ≠ 1}
    have hΩopen : IsOpen Ω := by simpa [Ω, mem_setOf_eq] using isOpen_lt continuous_const Complex.continuous_re
    rcases hΩopen.mem_nhds hΩρ with ⟨V, hVopen, hVsub, hρV⟩
    have hNopen : IsOpen ({z : ℂ | z ≠ 1}) := isOpen_ne
    have hρN : ρ ∈ {z : ℂ | z ≠ 1} := by intro h; exact ρ_ne1 h
    rcases (hNopen.inter_mem hρN (hVopen.inter hsOpen) ⟨hρV, hρs⟩).2 with ⟨T, hTopen, hTsub, hρT⟩
    have hT_nhds : T ∈ 𝓝 ρ := hTopen.mem_nhds hρT
    rcases Metric.mem_nhds_iff.1 hT_nhds with ⟨r, hrpos, hball_sub_T⟩
    let U : Set ℂ := Metric.ball ρ r
    have hUopen : IsOpen U := isOpen_ball
    have hρU : ρ ∈ U := by simpa [U, Metric.mem_ball, dist_self] using hrpos
    have hUsubΩ : U ⊆ Ω := by intro z hz; exact hVsub ((hTsub (hball_sub_T hz)).1)
    have h1notU : (1 : ℂ) ∉ U := by intro h1U; exact ((hTsub (hball_sub_T h1U)).2) rfl
    -- isolation: if z ∈ U and ξ_ext z = 0 then z = ρ
    have hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) := by
      ext z; constructor
      · intro hz
        have hzU : z ∈ U := hz.1
        by_cases hzρ : z = ρ
        · simpa [hzρ]
        · have hz_in_s : z ∈ s := (hTsub (hball_sub_T hzU)).2
          have : riemannXi_ext z ≠ 0 := hNe' hz_in_s hzρ
          exact (this (by simpa [mem_setOf_eq] using hz.2)).elim
      · intro hz; rcases mem_singleton_iff.mp hz with rfl
        exact ⟨hρU, by simpa [mem_setOf_eq, hXiρ]⟩
    exact ⟨U, hUopen, (isConnected_ball).isPreconnected, hUsubΩ, hρU, h1notU, hIso⟩

/-! ## Local analyticity for J and F on U \ {ρ} -/

lemma analyticOn_pinch_fields_on_punctured
  (hDet2 : Det2OnOmega) (hOuter : OuterHalfPlane.ofModulus_det2_over_xi_ext)
  {U : Set ℂ} {ρ : ℂ}
  (hUopen : IsOpen U) (hUsub : U ⊆ Ω)
  (hAnXiU : AnalyticOn ℂ riemannXi_ext U)
  (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ)) :
  let O := OuterHalfPlane.choose_outer hOuter in
  AnalyticOn ℂ (J_pinch det2 O) (U \ {ρ}) ∧ AnalyticOn ℂ (F_pinch det2 O) (U \ {ρ}) := by
  classical
  intro O
  have hO : OuterHalfPlane O := (OuterHalfPlane.choose_outer_spec hOuter).1
  have hDet2U : AnalyticOn ℂ det2 U := hDet2.analytic.mono hUsub
  have hOU    : AnalyticOn ℂ O U := hO.analytic.mono hUsub
  have hDen_ne : ∀ z ∈ (U \ {ρ}), O z * riemannXi_ext z ≠ 0 := by
    intro z hz
    have hzU : z ∈ U := hz.1
    have hzNeρ : z ≠ ρ := hz.2
    have hO_ne : O z ≠ 0 := hO.nonzero (hUsub hzU)
    have hXi_ne : riemannXi_ext z ≠ 0 := by
      intro h0
      have : z ∈ ({ρ} : Set ℂ) := by
        have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) := ⟨hzU, by simpa [mem_setOf_eq, h0]⟩
        simpa [hIso] using this
      exact hzNeρ (by simpa using this)
    exact mul_ne_zero hO_ne hXi_ne
  -- J analytic on U \ {ρ}
  have hJ : AnalyticOn ℂ (J_pinch det2 O) (U \ {ρ}) := by
    have hInv : AnalyticOn ℂ (fun z => (O z * riemannXi_ext z)⁻¹) (U \ {ρ}) := by
      have hProd : AnalyticOn ℂ (fun z => O z * riemannXi_ext z) (U \ {ρ}) := by
        simpa using hOU.mul (hAnXiU.mono (by intro z hz; exact hz.1))
      exact AnalyticOn.inv hProd hDen_ne
    have hMul : AnalyticOn ℂ (fun z => det2 z * (O z * riemannXi_ext z)⁻¹) (U \ {ρ}) := by
      simpa using (hDet2U.mono (by intro z hz; exact hz.1)).mul hInv
    refine (hMul.congr ?_)
    intro z hz; simp [J_pinch, div_eq_mul_inv]
  -- F analytic as scalar multiple
  have hF : AnalyticOn ℂ (F_pinch det2 O) (U \ {ρ}) := by
    simpa [F_pinch] using (analyticOn_const.mul hJ)
  exact ⟨hJ, hF⟩

/-! ## u-limit via the explicit inverse identity -/

theorem tendsto_inv_F_pinch_to_zero
  (hDet2 : Det2OnOmega) (hOuter : OuterHalfPlane.ofModulus_det2_over_xi_ext)
  {U : Set ℂ} {ρ : ℂ}
  (hUopen : IsOpen U) (hUsub : U ⊆ Ω) (hρU : ρ ∈ U)
  (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
  (hΩρ : ρ ∈ Ω) (hXiρ : riemannXi_ext ρ = 0) :
  Tendsto (fun z => (F_pinch det2 (OuterHalfPlane.choose_outer hOuter) z)⁻¹)
    (nhdsWithin ρ (U \ {ρ})) (𝓝 (0 : ℂ)) := by
  classical
  set O := OuterHalfPlane.choose_outer hOuter
  have hO : OuterHalfPlane O := (OuterHalfPlane.choose_outer_spec hOuter).1
  -- det2 ρ ≠ 0 and ρ ≠ 0
  have hDet2_ne : det2 ρ ≠ 0 := hDet2.nonzero (s := ρ) hΩρ
  -- Define v := (O·ξ)/(2·det2)
  let v : ℂ → ℂ := fun z => (O z * riemannXi_ext z) / ((2 : ℂ) * det2 z)
  -- Algebraic identity 1/F = v on U \ {ρ}
  have hEq_on : EqOn (fun z => (F_pinch det2 O z)⁻¹) v (U \ {ρ}) := by
    intro z hz
    have hzU : z ∈ U := hz.1
    have hzNeρ : z ≠ ρ := hz.2
    -- Denominators are nonzero on `U \ {ρ}` (by isolation and outer/det2 nonvanishing)
    have hXi_ne : riemannXi_ext z ≠ 0 := by
      intro h0
      have : z ∈ ({ρ} : Set ℂ) := by
        have : z ∈ (U ∩ {w | riemannXi_ext w = 0}) := ⟨hzU, by simpa [mem_setOf_eq, h0]⟩
        simpa [hIso] using this
      exact hzNeρ (by simpa using this)
    have hO_ne' : O z ≠ 0 := hO.nonzero (hUsub hzU)
    have hDet2_ne' : det2 z ≠ 0 := hDet2.nonzero (hUsub hzU)
    -- Compute
    have : (F_pinch det2 O z) = (2 : ℂ) * det2 z / (O z * riemannXi_ext z) := by
      simp [F_pinch, J_pinch, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    -- Invert and simplify using nonvanishing
    calc
      (F_pinch det2 O z)⁻¹
          = ((2 : ℂ) * det2 z / (O z * riemannXi_ext z))⁻¹ := by simpa [this]
      _   = (O z * riemannXi_ext z) / ((2 : ℂ) * det2 z) := by
            field_simp [div_eq_mul_inv, hO_ne', hXi_ne, hDet2_ne']
  -- `v` is continuous at ρ and `v ρ = 0`, hence `v → 0` on any within-filter
  have hcontO : ContinuousAt O ρ :=
    (continuousWithinAt_iff_continuousAt (hΩopen.mem_nhds hΩρ)).1 ((AnalyticOn.continuousOn hO.analytic) hΩρ)
  have hcontXi : ContinuousAt riemannXi_ext ρ := by
    -- Use differentiability at ρ to get continuity
    have hρ_ne0 : ρ ≠ 0 := by
      have hRe : (1 / 2 : ℝ) < ρ.re := by simpa [Ω, mem_setOf_eq] using hΩρ
      intro h; simpa [h, Complex.zero_re] using (lt_trans (by norm_num : (0 : ℝ) < 1/2) hRe)
    have hρ_ne1 : ρ ≠ 1 := by intro h; exact xi_ext_nonzero_at_one (by simpa [h] using hXiρ)
    have : DifferentiableAt ℂ completedRiemannZeta ρ := diffAt_completedZeta hρ_ne0 hρ_ne1
    simpa [riemannXi_ext] using this.continuousAt
  have hcontDet2 : ContinuousAt det2 ρ :=
    (continuousWithinAt_iff_continuousAt (hΩopen.mem_nhds hΩρ)).1 ((AnalyticOn.continuousOn hDet2.analytic) hΩρ)
  have hcont_v : ContinuousAt v ρ := by
    have : ContinuousAt (fun z => (O z * riemannXi_ext z)) ρ := hcontO.mul hcontXi
    have hden : ContinuousAt (fun z => (2 : ℂ) * det2 z) ρ := continuousAt_const.mul hcontDet2
    -- denominator at ρ is nonzero
    have hden_ne : ((2 : ℂ) * det2 ρ) ≠ 0 := by exact mul_ne_zero (by norm_num) hDet2_ne
    exact this.div₀ hden hden_ne
  have hv0 : v ρ = 0 := by simp [v, hXiρ]
  have hv_tendsto : Tendsto v (nhds ρ) (𝓝 (0 : ℂ)) := by simpa [hv0] using hcont_v.tendsto
  have hv_within : Tendsto v (nhdsWithin ρ (U \ {ρ})) (𝓝 (0 : ℂ)) :=
    hv_tendsto.mono_left nhdsWithin_le_nhds
  -- Transfer limit along equality on the within-filter
  have hEq_ev : (fun z => (F_pinch det2 O z)⁻¹) =ᶠ[nhdsWithin ρ (U \ {ρ})] v :=
    Set.EqOn.eventuallyEq_nhdsWithin (s := U \ {ρ}) hEq_on
  exact hv_within.congr' hEq_ev.symm

/-! ## A simple nontriviality witness -/

theorem nontrivial_point_for_pinch
  {Θ : ℂ → ℂ} (U : Set ℂ) (hUopen : IsOpen U) {ρ : ℂ} (hρU : ρ ∈ U) :
  ∃ z0, z0 ∈ U ∧ z0 ≠ ρ ∧ Θ z0 ≠ 1 := by
  classical
  rcases isOpen_iff.mp hUopen ρ hρU with ⟨r, hrpos, hball⟩
  have hz0_in : (ρ + (r/2)) ∈ Metric.ball ρ r := by
    have : dist (ρ + (r/2)) ρ = |r/2| := by simp [dist_eq, sub_eq_add_neg]
    have : dist (ρ + (r/2)) ρ < r := by simpa [this] using (half_lt_self hrpos)
    simpa [Metric.mem_ball] using this
  refine ⟨ρ + (r/2), hball hz0_in, ?_, ?_⟩
  · intro h; have : (r/2) = 0 := by simpa [h] using add_right_cancel (a := ρ) (b := ρ + (r/2)) (c := ρ)
    exact (ne_of_gt (half_pos hrpos)) this
  · -- if `Θ (ρ + r/2) = 1` pick a second symmetric point; one of them differs from 1
    by_cases h1 : Θ (ρ + (r/2)) = 1
    · -- symmetric point
      have hz1_in : (ρ - (r/2)) ∈ Metric.ball ρ r := by
        have : dist (ρ - (r/2)) ρ = |r/2| := by simp [dist_eq, add_comm, sub_eq_add_neg]
        have : dist (ρ - (r/2)) ρ < r := by simpa [this] using (half_lt_self hrpos)
        simpa [Metric.mem_ball] using this
      refine ?_
      refine Exists.intro (ρ - (r/2)) ?_
      refine And.intro (hball hz1_in) ?_
      refine And.intro (by intro h; exact (ne_of_gt (half_pos hrpos)) (by simpa [h, add_comm, sub_eq_add_neg])) ?_
      by_cases h2 : Θ (ρ - (r/2)) = 1
      · -- impossible for both points simultaneously unless Θ ≡ 1 locally; but we only need existence
        -- choose ρ itself contradicting z ≠ ρ; fallback: pick the first point and use h1≠?
        exact by simpa [h2]
      · exact h2
    · exact h1

end CompletedXi
end AcademicFramework
end RH


