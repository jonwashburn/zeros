import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
  # Half-plane Poisson kernel and transport

  Self-contained Mathlib-ready development of the Poisson kernel on the right
  half-plane `Ω = {s : ℂ | Re s > 1/2}`: nonnegativity, comparison to a Cauchy
  tail, integrability, Poisson integral operator, representation predicate, and
  transport of boundary positivity to the interior. Includes basic measurability
  helpers.

  This file is intentionally minimal and avoids any external project-specific
  dependencies so it can be upstreamed to Mathlib. The statements mirror the
  classical theory specialized to the right half-plane with boundary line
  `Re s = 1/2` parameterized by `t ↦ 1/2 + i t`.
-/

namespace RH
namespace HalfPlanePoisson

noncomputable section

open Complex MeasureTheory Filter
open scoped Topology Real MeasureTheory

/-! ## Domain and boundary parameterization -/

/-- The right half-plane domain `Ω = {s : ℂ | Re s > 1/2}`. -/
def Ω : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

/-- Boundary parameterization of the line `Re s = 1/2` by the imaginary part. -/
@[simp] def boundary (t : ℝ) : ℂ := (1/2 : ℝ) + I * (t : ℂ)

/-- Real part of a boundary point. -/
lemma boundary_re (t : ℝ) : (boundary t).re = 1/2 := by
  simp [boundary]

/-- Imaginary part of a boundary point. -/
lemma boundary_im (t : ℝ) : (boundary t).im = t := by
  simp [boundary]

/-- Structured equality for the boundary point. -/
@[simp] lemma boundary_mk_eq (t : ℝ) :
    boundary t = { re := (1/2 : ℝ), im := t } := by
  apply Complex.ext <;> simp [boundary]

/-- The boundary map is measurable. -/
lemma measurable_boundary_affine : Measurable (boundary : ℝ → ℂ) := by
  -- Continuity implies measurability
  have hcont : Continuous (fun t : ℝ => (1/2 : ℝ) + I * (t : ℂ)) := by
    exact continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  exact hcont.measurable

/-- If `f` is measurable on `ℂ`, then its pullback along `boundary` is measurable. -/
lemma measurable_comp_boundary {α} [MeasurableSpace α]
    {f : ℂ → α} (hf : Measurable f) :
    Measurable (fun t : ℝ => f (boundary t)) :=
  hf.comp measurable_boundary_affine

/-! ## Poisson kernel and basic properties -/

/-- The (normalized) Poisson kernel for the right half-plane.

Given `z = a + i b` with `a = Re z - 1/2 > 0`,
`poissonKernel z t = (1/π) · a / (a^2 + (t - b)^2)` is nonnegative and integrable.
-/
@[simp] noncomputable def poissonKernel (z : ℂ) (t : ℝ) : ℝ :=
  let a := z.re - 1/2
  let b := z.im
  (1 / Real.pi) * (a / (a^2 + (t - b)^2))

/-- Nonnegativity of the Poisson kernel for `z ∈ Ω`. -/
lemma poissonKernel_nonneg {z : ℂ} (hz : z ∈ Ω) (t : ℝ) :
    0 ≤ poissonKernel z t := by
  unfold poissonKernel Ω at *
  simp only [Set.mem_setOf_eq] at hz
  have ha : 0 < z.re - 1/2 := sub_pos.mpr hz
  have hdenom : 0 < (z.re - 1/2)^2 + (t - z.im)^2 := by
    refine add_pos_of_pos_of_nonneg ?_ (sq_nonneg _)
    exact sq_pos_of_ne_zero (ne_of_gt ha)
  exact mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le)
    (div_nonneg ha.le hdenom.le)

/-- Helper bound: the Poisson kernel is dominated by a Cauchy tail `C/(1+(t-b)^2)`. -/
private lemma poissonKernel_bound (z : ℂ) (hz : z ∈ Ω) :
    ∃ C > 0, ∀ t : ℝ, poissonKernel z t ≤ C / (1 + (t - z.im)^2) := by
  unfold Ω at hz
  simp only [Set.mem_setOf_eq] at hz
  set a := z.re - 1/2 with ha_def
  have ha : 0 < a := sub_pos.mpr hz
  -- Choose `C = (1/π) * max a (1/a)`
  refine ⟨(1 / Real.pi) * max a (1 / a), ?_, ?_⟩
  · exact mul_pos (one_div_pos.mpr Real.pi_pos) (lt_max_of_lt_left ha)
  · intro t
    have hden1 : 0 < (1 + (t - z.im) ^ 2) := by
      have : 0 ≤ (t - z.im) ^ 2 := sq_nonneg _
      have : 0 < (1 : ℝ) + (t - z.im) ^ 2 := add_pos_of_pos_of_nonneg (by norm_num) this
      simpa using this
    have hden2 : 0 < a ^ 2 + (t - z.im) ^ 2 := by
      have : 0 < a ^ 2 := by
        have : a ≠ 0 := ne_of_gt ha
        simpa [pow_two] using mul_self_pos.mpr this
      exact add_pos_of_pos_of_nonneg this (sq_nonneg _)
    -- Establish the target fractional bound by cases on `a ≤ 1` or `1 ≤ a`.
    have hfrac : a / (a ^ 2 + (t - z.im) ^ 2)
        ≤ (max a (1 / a)) / (1 + (t - z.im) ^ 2) := by
      have hposL : 0 < (a ^ 2 + (t - z.im) ^ 2) := hden2
      have hposR : 0 < (1 + (t - z.im) ^ 2) := hden1
      have hposR_le : 0 ≤ (1 + (t - z.im) ^ 2) := le_of_lt hposR
      have hcases := le_total a (1 : ℝ)
      cases hcases with
      | inl hA_le_one =>
        -- Use `a² ≤ 1` to show `a/(a²+X) ≤ (1/a)/(1+X)`
        have ha2_le_one : a ^ 2 ≤ (1 : ℝ) := by
          have := sq_le_sq.mpr hA_le_one
          simpa [pow_two, one_pow] using this
        have hstep : a * (1 + (t - z.im) ^ 2)
            ≤ (1 / a) * (a ^ 2 + (t - z.im) ^ 2) := by
          have hx : a ^ 2 * (t - z.im) ^ 2 ≤ (t - z.im) ^ 2 := by
            exact mul_le_mul_of_nonneg_right ha2_le_one (sq_nonneg _)
          have hx' : a ^ 2 * (1 + (t - z.im) ^ 2) ≤ a ^ 2 + (t - z.im) ^ 2 := by
            simpa [mul_add] using add_le_add_left hx (a ^ 2)
          have ha_pos : 0 < a := ha
          have : (1 / a) * (a ^ 2 * (1 + (t - z.im) ^ 2))
              ≤ (1 / a) * (a ^ 2 + (t - z.im) ^ 2) :=
            mul_le_mul_of_nonneg_left hx' (one_div_nonneg.mpr (le_of_lt ha_pos))
          have ha_ne : a ≠ 0 := ne_of_gt ha_pos
          simpa [one_div, pow_two, mul_comm, mul_left_comm, mul_assoc, ha_ne] using this
        -- Convert to the desired fractional inequality via `le_div_iff` and `div_le_iff`
        have h1 : a ≤ ((1 / a) * (a ^ 2 + (t - z.im) ^ 2)) / (1 + (t - z.im) ^ 2) :=
          (le_div_iff hposR).mpr hstep
        have h2 : a / (a ^ 2 + (t - z.im) ^ 2)
            ≤ (1 / a) / (1 + (t - z.im) ^ 2) := by
          -- `div_le_iff` with positive left denominator
          have := (div_le_iff hposL).mpr h1
          -- rearrange to the target shape
          simpa [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using this
        -- Lift numerator by monotonicity of division by a positive number
        have hnum_le : (1 / a) ≤ max a (1 / a) := le_max_right _ _
        have hmono := div_le_div_of_nonneg_right hnum_le hposR_le
        exact h2.trans hmono
      | inr h_one_le_A =>
        -- `1 ≤ a` gives `1 ≤ a²` hence `a/(a²+X) ≤ a/(1+X)`
        have one_le_a2 : (1 : ℝ) ≤ a ^ 2 := by
          have := pow_le_pow_left (by norm_num : (0 : ℝ) ≤ 1) h_one_le_A (2 : ℕ)
          simpa [one_pow] using this
        have hx : (1 + (t - z.im) ^ 2) ≤ (a ^ 2 + (t - z.im) ^ 2) :=
          add_le_add_right one_le_a2 _
        have h2 : a / (a ^ 2 + (t - z.im) ^ 2)
            ≤ a / (1 + (t - z.im) ^ 2) := by
          -- Use `div_le_div_of_nonneg_left` as `a ≥ 0` and denominators order
          have ha_nonneg : 0 ≤ a := le_of_lt ha
          exact div_le_div_of_nonneg_left ha_nonneg (by exact hx) (lt_of_le_of_lt (by norm_num) hposR) (lt_of_le_of_lt (sq_nonneg _) ?_)
          -- The above is tricky; instead, use `le_of_mul_le_mul_left` on positive denominators:
        -- Alternative approach: multiply both sides by positive denominators
        have h2' : a * (1 + (t - z.im) ^ 2)
            ≤ a * (a ^ 2 + (t - z.im) ^ 2) :=
          mul_le_mul_of_nonneg_left hx (le_of_lt ha)
        have hA : a / (a ^ 2 + (t - z.im) ^ 2)
            ≤ a / (1 + (t - z.im) ^ 2) := by
          have := (le_div_iff₀ (by exact hposR.ne')).mpr h2'
          have := (div_le_iff₀ (by exact hposL.ne')).mpr this
          simpa [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using this
        -- Lift to `max a (1/a)`
        have hnum_le : a ≤ max a (1 / a) := le_max_left _ _
        have hmono := div_le_div_of_nonneg_right hnum_le hposR_le
        exact hA.trans hmono
    have hπnonneg : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt Real.pi_pos)
    have : (1 / Real.pi) * (a / (a ^ 2 + (t - z.im) ^ 2))
        ≤ (1 / Real.pi) * ((max a (1 / a)) / (1 + (t - z.im) ^ 2)) :=
      mul_le_mul_of_nonneg_left hfrac hπnonneg
    simpa [poissonKernel, ha_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

/-- Integrability of the Poisson kernel on `ℝ` for `z ∈ Ω`. -/
lemma poissonKernel_integrable {z : ℂ} (hz : z ∈ Ω) :
    Integrable (fun t : ℝ => poissonKernel z t) := by
  obtain ⟨C, hC_pos, hbound⟩ := poissonKernel_bound z hz
  -- The dominating Cauchy tail is integrable by translation of `1/(1+t^2)`.
  have h_dom : Integrable (fun t => C / (1 + (t - z.im)^2)) := by
    have h' : Integrable (fun t : ℝ => (1 + (t - z.im) ^ 2)⁻¹) := by
      simpa [sub_eq_add_neg] using
        (Integrable.comp_sub_right (μ := volume) integrable_inv_one_add_sq z.im)
    have : Integrable (fun t : ℝ => 1 / (1 + (t - z.im) ^ 2)) := by
      simpa [one_div] using h'
    simpa [div_eq_mul_inv] using this.const_mul C
  refine h_dom.mono ?_ ?_
  · -- measurability of the kernel
    have hb : Measurable (fun t : ℝ => t - z.im) := by
      simpa [sub_eq_add_neg] using (measurable_id.sub measurable_const)
    have hden : Measurable (fun t : ℝ => (z.re - 1/2) ^ 2 + (t - z.im) ^ 2) :=
      measurable_const.add (hb.pow measurable_const)
    have hfrac : Measurable
        (fun t : ℝ => (z.re - 1/2) / ((z.re - 1/2) ^ 2 + (t - z.im) ^ 2)) := by
      have : Measurable (fun t : ℝ => ((z.re - 1/2) ^ 2 + (t - z.im) ^ 2)⁻¹) :=
        hden.inv
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this.const_mul (z.re - 1/2)
    have hmeas : Measurable
        (fun t : ℝ => (1 / Real.pi) *
          ((z.re - 1/2) / ((z.re - 1/2) ^ 2 + (t - z.im) ^ 2))) :=
      hfrac.const_mul (1 / Real.pi)
    simpa [poissonKernel] using hmeas.aestronglyMeasurable
  · -- pointwise bound by the dominating tail
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hk_nonneg : 0 ≤ poissonKernel z t := poissonKernel_nonneg hz t
    have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
    have hden_pos : 0 < 1 + (t - z.im) ^ 2 :=
      add_pos_of_pos_of_nonneg (by norm_num) (sq_nonneg _)
    have hquot_nonneg : 0 ≤ C / (1 + (t - z.im) ^ 2) :=
      div_nonneg hC_nonneg (le_of_lt hden_pos)
    -- Convert scalar inequality to a norm inequality
    have h_base : poissonKernel z t ≤ C / (1 + (t - z.im) ^ 2) := hbound t
    have h_left : ‖poissonKernel z t‖ = poissonKernel z t := by
      simp [Real.norm_eq_abs, _root_.abs_of_nonneg hk_nonneg]
    -- use that norm is monotone on nonnegative reals: since RHS ≥ 0, we can bound norms
    have hRHS_nonneg : 0 ≤ C / (1 + (t - z.im) ^ 2) := hquot_nonneg
    have h_right : ‖C / (1 + (t - z.im) ^ 2)‖ = C / (1 + (t - z.im) ^ 2) := by
      simp [Real.norm_eq_abs, _root_.abs_of_nonneg hRHS_nonneg]
    have : ‖poissonKernel z t‖ ≤ ‖C / (1 + (t - z.im) ^ 2)‖ := by
      simpa [h_left, h_right] using
        (le_trans h_base (le_of_eq h_right.symm))
    exact this

/-! ## Poisson integral and representation/transport -/

/-- Poisson integral of a real boundary function `u : ℝ → ℝ` at `z ∈ Ω`. -/
@[simp] noncomputable def poissonIntegral (u : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, u t * poissonKernel z t

/-- Boundary positivity predicate: `(P+)` on the line `Re s = 1/2`. -/
def BoundaryPositive (F : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re

/-- Poisson representation predicate for `F` on all of `Ω` (real-part form). -/
structure HasPoissonRep (F : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ F Ω
  integrable : ∀ z ∈ Ω, Integrable (fun t => (F (boundary t)).re * poissonKernel z t)
  formula : ∀ z ∈ Ω, (F z).re = poissonIntegral (fun t => (F (boundary t)).re) z

/-- Subset version of the Poisson representation predicate. -/
structure HasPoissonRepOn (F : ℂ → ℂ) (S : Set ℂ) : Prop where
  subset : S ⊆ Ω
  analytic : AnalyticOn ℂ F S
  integrable : ∀ z ∈ S, Integrable (fun t => (F (boundary t)).re * poissonKernel z t)
  formula : ∀ z ∈ S, (F z).re = poissonIntegral (fun t => (F (boundary t)).re) z

/-- Transport of boundary positivity to the interior using a Poisson representation. -/
theorem poissonTransport {F : ℂ → ℂ} (hRep : HasPoissonRep F) :
    BoundaryPositive F → ∀ z ∈ Ω, 0 ≤ (F z).re := by
  intro hBoundary z hz
  -- Use the Poisson representation for `Re F` and the nonnegativity of the kernel.
  have hformula := hRep.formula z hz
  -- Rewrite with the formula
  have : (F z).re = poissonIntegral (fun t => (F (boundary t)).re) z := hformula
  -- Conclude
  have : 0 ≤ ∫ t : ℝ, (F (boundary t)).re * poissonKernel z t := by
    apply integral_nonneg_of_ae
    filter_upwards [hBoundary] with t ht
    exact mul_nonneg ht (poissonKernel_nonneg hz t)
  simpa [poissonIntegral, hformula] using this

/-- Transport of boundary positivity on a subset admitting a Poisson representation. -/
theorem poissonTransportOn {F : ℂ → ℂ} {S : Set ℂ} (hRep : HasPoissonRepOn F S) :
    BoundaryPositive F → ∀ z ∈ S, 0 ≤ (F z).re := by
  intro hBoundary z hz
  have hzΩ : z ∈ Ω := hRep.subset hz
  have hformula := hRep.formula z hz
  have : 0 ≤ ∫ t : ℝ, (F (boundary t)).re * poissonKernel z t := by
    apply integral_nonneg_of_ae
    filter_upwards [hBoundary] with t ht
    exact mul_nonneg ht (poissonKernel_nonneg hzΩ t)
  simpa [poissonIntegral, hformula]

/-! ## Integrability under bounded boundary data -/

/-- If the boundary data is essentially bounded by `M`, the Poisson integrand is integrable. -/
lemma integrable_boundedBoundary
    (F : ℂ → ℂ) (z : ℂ) (M : ℝ)
    (hz : z ∈ Ω)
    (hBound : ∀ t : ℝ, |(F (boundary t)).re| ≤ M)
    (hMeas : Measurable (fun t => (F (boundary t)).re)) :
    Integrable (fun t => (F (boundary t)).re * poissonKernel z t) := by
  -- Kernel is integrable
  have hker := poissonKernel_integrable hz
  -- `M ≥ 0` since `|F.re| ≥ 0`
  have hM_nonneg : 0 ≤ M := by
    have : 0 ≤ |(F (boundary 0)).re| := abs_nonneg _
    exact this.trans (hBound 0)
  -- Dominating function
  have h_dom : Integrable (fun t => M * poissonKernel z t) := hker.const_mul M
  refine h_dom.mono ?_ ?_
  · -- measurability
    have hb : Measurable (fun t : ℝ => t - z.im) := by
      simpa [sub_eq_add_neg] using (measurable_id.sub measurable_const)
    have hden : Measurable (fun t : ℝ => (z.re - 1/2) ^ 2 + (t - z.im) ^ 2) :=
      measurable_const.add (hb.pow measurable_const)
    have hfrac : Measurable
        (fun t : ℝ => (z.re - 1/2) / ((z.re - 1/2) ^ 2 + (t - z.im) ^ 2)) := by
      have : Measurable (fun t : ℝ => ((z.re - 1/2) ^ 2 + (t - z.im) ^ 2)⁻¹) :=
        hden.inv
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this.const_mul (z.re - 1/2)
    have hpk_meas : Measurable (fun t : ℝ => poissonKernel z t) :=
      (hfrac.const_mul (1 / Real.pi))
    exact (hMeas.mul hpk_meas).aestronglyMeasurable
  · -- pointwise bound by `M`
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hk_nonneg : 0 ≤ poissonKernel z t := poissonKernel_nonneg hz t
    have : ‖(F (boundary t)).re * poissonKernel z t‖
        ≤ M * poissonKernel z t := by
      have := mul_le_mul_of_nonneg_right (hBound t) hk_nonneg
      simpa [norm_mul, Real.norm_eq_abs, _root_.abs_of_nonneg hk_nonneg,
        _root_.abs_of_nonneg hM_nonneg] using this
    simpa [norm_mul] using this

end HalfPlanePoisson
end RH
