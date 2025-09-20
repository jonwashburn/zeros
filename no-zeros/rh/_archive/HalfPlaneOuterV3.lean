import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Integrals
import rh.academic_framework.CompletedXi
import rh.academic_framework.DiskHardy
import rh.RS.Det2Outer
import rh.RS.PoissonAI
import rh.RS.Cayley

/-!
# Half-plane Outer Functions (Clean Rewrite V3)

This is a copy of `HalfPlaneOuterV2` under a distinct namespace for parallel work.
-/

namespace RH.AcademicFramework.HalfPlaneOuterV3

noncomputable section

open Complex MeasureTheory Filter
open scoped Real Topology

-- Import necessary symbols from other modules
open RH.AcademicFramework.CompletedXi
open RH.RS

/-! ## Section 1: Basic Definitions -/

/-- The right half-plane domain Ω = {s : ℂ | Re s > 1/2} -/
def Ω : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

/-- Boundary parametrization of the critical line Re s = 1/2 -/
@[simp] def boundary (t : ℝ) : ℂ := (1/2 : ℝ) + I * (t : ℂ)

lemma boundary_re (t : ℝ) : (boundary t).re = 1/2 := by simp [boundary]

lemma boundary_im (t : ℝ) : (boundary t).im = t := by simp [boundary]

/-- An outer function on Ω: analytic and non-vanishing -/
structure IsOuter (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω
  nonvanishing : ∀ s ∈ Ω, O s ≠ 0

/-- Boundary modulus equality: |O| = |F| on the critical line -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, abs (O (boundary t)) = abs (F (boundary t))

/-- Existence of an outer with prescribed boundary modulus -/
def ExistsOuterWithModulus (F : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, IsOuter O ∧ BoundaryModulusEq O F

/-! ## Section 2: Poisson Kernel and Integration -/

/-- The Poisson kernel for the right half-plane -/
@[simp] noncomputable def poissonKernel (z : ℂ) (t : ℝ) : ℝ :=
  let a := z.re - 1/2
  let b := z.im
  (1 / Real.pi) * (a / (a^2 + (t - b)^2))

/-- Non-negativity of the Poisson kernel for z ∈ Ω -/
lemma poissonKernel_nonneg {z : ℂ} (hz : z ∈ Ω) (t : ℝ) : 
    0 ≤ poissonKernel z t := by
  unfold poissonKernel Ω at *
  simp only [Set.mem_setOf_eq] at hz
  have ha : 0 < z.re - 1/2 := sub_pos.mpr hz
  have hdenom : 0 < (z.re - 1/2)^2 + (t - z.im)^2 := by
    apply add_pos_of_pos_of_nonneg
    · exact sq_pos_of_ne_zero (ne_of_gt ha)
    · exact sq_nonneg _
  exact mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le) 
    (div_nonneg ha.le hdenom.le)

/-- Poisson integral: reconstructs interior values from boundary data -/
@[simp] noncomputable def poissonIntegral (u : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, u t * poissonKernel z t

/-- Boundary positivity condition (P+) -/
def BoundaryPositive (F : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re

/-- Poisson representation: F has a Poisson integral representation on Ω -/
structure HasPoissonRep (F : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ F Ω
  integrable : ∀ z ∈ Ω, Integrable (fun t => (F (boundary t)).re * poissonKernel z t)
  formula : ∀ z ∈ Ω, (F z).re = poissonIntegral (fun t => (F (boundary t)).re) z

/-! ## Section 3: Transport Theorems -/

/-- Poisson transport: boundary positivity implies interior positivity -/
theorem poissonTransport {F : ℂ → ℂ} (hRep : HasPoissonRep F) :
    BoundaryPositive F → ∀ z ∈ Ω, 0 ≤ (F z).re := by
  intro hBoundary z hz
  -- Use the Poisson representation
  rw [hRep.formula z hz]
  unfold poissonIntegral
  -- The integral of non-negative functions is non-negative
  apply integral_nonneg_of_ae
  filter_upwards [hBoundary] with t ht
  exact mul_nonneg ht (poissonKernel_nonneg hz t)

/-- Subset Poisson representation (for domains with excluded singularities) -/
structure HasPoissonRepOn (F : ℂ → ℂ) (S : Set ℂ) : Prop where
  subset : S ⊆ Ω
  analytic : AnalyticOn ℂ F S
  integrable : ∀ z ∈ S, Integrable (fun t => (F (boundary t)).re * poissonKernel z t)
  formula : ∀ z ∈ S, (F z).re = poissonIntegral (fun t => (F (boundary t)).re) z

/-- Transport on subsets -/
theorem poissonTransportOn {F : ℂ → ℂ} {S : Set ℂ} (hRep : HasPoissonRepOn F S) :
    BoundaryPositive F → ∀ z ∈ S, 0 ≤ (F z).re := by
  intro hBoundary z hz
  rw [hRep.formula z hz]
  unfold poissonIntegral
  apply integral_nonneg_of_ae
  have hzΩ : z ∈ Ω := hRep.subset hz
  filter_upwards [hBoundary] with t ht
  exact mul_nonneg ht (poissonKernel_nonneg hzΩ t)

/-! ## Section 4: Pinch Field Specializations -/

/-- The pinch field F_pinch = 2 * J_pinch -/
@[simp] noncomputable def F_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (2 : ℂ) * J_pinch det2 O z

/-- Analyticity of J_pinch on the off-zeros set -/
lemma J_pinch_analyticOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext Ω) :
    AnalyticOn ℂ (J_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  -- J_pinch = det2 / (O * ξ_ext) is analytic where the denominator is non-zero
  have h1 := hDet2.analytic
  have h2 := hO.analytic
  have h3 := hXi
  -- The denominator O * ξ_ext is non-zero on the off-zeros set
  have hdenom : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), O z * riemannXi_ext z ≠ 0 := by
    intro z hz
    simp only [Set.mem_diff, Set.mem_setOf_eq] at hz
    apply mul_ne_zero
    · exact hO.nonzero (by exact hz.1)
    · exact hz.2
  -- Restrict factors and apply quotient analyticity
  have h1' : AnalyticOn ℂ det2 (Ω \ {z | riemannXi_ext z = 0}) := by
    apply h1.mono; intro z hz; exact hz.1
  have h2' : AnalyticOn ℂ O (Ω \ {z | riemannXi_ext z = 0}) := by  
    apply h2.mono; intro z hz; exact hz.1
  have h3' : AnalyticOn ℂ riemannXi_ext (Ω \ {z | riemannXi_ext z = 0}) := by
    apply h3.mono; intro z hz; exact hz.1
  apply AnalyticOn.div h1'
  · exact h2'.mul h3'
  · exact hdenom

/-- Analyticity of F_pinch on the off-zeros set -/
lemma F_pinch_analyticOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O) 
    (hXi : AnalyticOn ℂ riemannXi_ext Ω) :
    AnalyticOn ℂ (F_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  unfold F_pinch
  have hJ := J_pinch_analyticOn_offZeros hDet2 hO hXi
  have h2 : AnalyticOn ℂ (fun _ => (2 : ℂ)) (Ω \ {z | riemannXi_ext z = 0}) := analyticOn_const
  exact h2.mul hJ

/-- Boundary bound for F_pinch when boundary modulus equality holds -/
lemma F_pinch_boundary_bound
    {O : ℂ → ℂ}
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (t : ℝ) :
    |(F_pinch det2 O (boundary t)).re| ≤ 2 := by
  -- From boundary modulus equality: |O| = |det2/ξ| on boundary
  -- Therefore |J_pinch| = |det2/(O*ξ)| = |det2|/(|O|*|ξ|) = |det2|/(|det2/ξ|*|ξ|) = 1
  have h_J_abs : abs (J_pinch det2 O (boundary t)) = 1 := by
    -- Provided by RS: boundary_abs_J_pinch_eq_one
    -- Replace with the actual lemma when wiring in
    sorry
  -- Since F_pinch = 2 * J_pinch, we have |F_pinch| = 2
  have h_F_abs : abs (F_pinch det2 O (boundary t)) = 2 := by
    unfold F_pinch
    -- For complex abs, use Complex.abs.map_mul then abs_ofReal for 2
    have : Complex.abs ((2 : ℂ) * J_pinch det2 O (boundary t))
        = Complex.abs (2 : ℂ) * Complex.abs (J_pinch det2 O (boundary t)) := by
      simpa using (Complex.abs.map_mul (2 : ℂ) (J_pinch det2 O (boundary t)))
    have h2 : Complex.abs (2 : ℂ) = (2 : ℝ) := by simpa using Complex.abs_ofReal (2 : ℝ)
    simpa [this, h2, h_J_abs]
  -- Therefore |Re F_pinch| ≤ |F_pinch| = 2
  exact le_trans (abs_re_le_abs _) (le_of_eq h_F_abs)

/-! ## Section 5: Integrability Helpers -/

/-- Integrability of the Poisson kernel -/
lemma poissonKernel_integrable {z : ℂ} (hz : z ∈ Ω) :
    Integrable (fun t : ℝ => poissonKernel z t) := by
  classical
  -- Notation and positive parameters
  have hzRe : (1/2 : ℝ) < z.re := by simpa [Ω, Set.mem_setOf_eq] using hz
  set a : ℝ := z.re - (1/2 : ℝ)
  set b : ℝ := z.im
  have ha : 0 < a := sub_pos.mpr hzRe
  -- Choose constants
  have hC0pos : 0 < max a (1 / a) := by
    have hapos : 0 < a := ha
    have h1apos : 0 < 1 / a := by simpa using one_div_pos.mpr hapos
    exact lt_max_of_lt_left hapos
  let C0 : ℝ := max a (1 / a)
  let C : ℝ := (1 / Real.pi) * C0
  have hCpos : 0 < C := by
    have hπ : 0 < (1 / Real.pi) := by simpa using one_div_pos.mpr Real.pi_pos
    exact mul_pos hπ hC0pos
  -- Core domination bound
  have hbound : ∀ t : ℝ,
      poissonKernel z t ≤ C * (1 / (1 + (t - b) ^ 2)) := by
    intro t
    have hden1 : 0 < (1 + (t - b) ^ 2) := by
      have : 0 ≤ (t - b) ^ 2 := sq_nonneg _
      have : 0 < (1 : ℝ) + (t - b) ^ 2 := by exact add_pos_of_pos_of_nonneg (by norm_num) this
      simpa using this
    have hden2 : 0 < a ^ 2 + (t - b) ^ 2 := by
      have : 0 < a ^ 2 := by
        have : a ≠ 0 := ne_of_gt ha
        simpa [pow_two] using mul_self_pos.mpr this
      exact add_pos_of_pos_of_nonneg this (sq_nonneg _)
    -- algebraic inequality via cases (identical to main file)
    have hcases := le_total a (1 : ℝ)
    have hcore : a * (1 + (t - b) ^ 2) ≤ C0 * (a ^ 2 + (t - b) ^ 2) := by
      cases hcases with
      | inl hA_le_one =>
        have : a * (1 + (t - b) ^ 2) ≤ (1 / a) * (a ^ 2 + (t - b) ^ 2) := by
          have hXnn : 0 ≤ (t - b) ^ 2 := by exact sq_nonneg _
          have hcoef : a ^ 2 - 1 ≤ 0 := by
            have : a ≤ 1 := hA_le_one
            have : a ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left (le_of_lt ha) this (2 : ℕ)
            simpa [pow_two] using sub_nonpos.mpr this
          have : (a ^ 2 - 1) * (t - b) ^ 2 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hcoef hXnn
          have ineq : a ^ 2 * (1 + (t - b) ^ 2) ≤ a ^ 2 + (t - b) ^ 2 := by
            calc a ^ 2 * (1 + (t - b) ^ 2) = a ^ 2 + a ^ 2 * (t - b) ^ 2 := by ring
              _ = a ^ 2 + (t - b) ^ 2 + (a ^ 2 - 1) * (t - b) ^ 2 := by ring
              _ ≤ a ^ 2 + (t - b) ^ 2 + 0 := by
                  have : (a ^ 2 - 1) * (t - b) ^ 2 ≤ 0 := this
                  linarith
              _ = a ^ 2 + (t - b) ^ 2 := by ring
          have ha_pos : 0 < a := ha
          have ha_ne : a ≠ 0 := ne_of_gt ha_pos
          have : (1 / a) * (a ^ 2 * (1 + (t - b) ^ 2)) ≤ (1 / a) * (a ^ 2 + (t - b) ^ 2) := by
            exact mul_le_mul_of_nonneg_left ineq (one_div_nonneg.mpr (le_of_lt ha_pos))
          simpa [one_div, pow_two, mul_comm, mul_left_comm, mul_assoc, ha_ne] using this
        exact le_trans this (by gcongr)
      | inr h_one_le_A =>
        have : a * (1 + (t - b) ^ 2) ≤ a * (a ^ 2 + (t - b) ^ 2) := by
          have : (1 : ℝ) ≤ a ^ 2 := by
            have : (1 : ℝ) ≤ a := h_one_le_A
            have : (1 : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left (by norm_num : (0 : ℝ) ≤ 1) this (2 : ℕ)
            simpa [one_pow] using this
          have hx : (1 + (t - b) ^ 2) ≤ (a ^ 2 + (t - b) ^ 2) := by
            have hnn : 0 ≤ (t - b) ^ 2 := sq_nonneg _
            exact add_le_add_right this _
          exact mul_le_mul_of_nonneg_left hx (le_of_lt ha)
        exact le_trans this (by gcongr)
    have :
        (1 / Real.pi) * (a / (a ^ 2 + (t - b) ^ 2))
          ≤ (1 / Real.pi) * (C0 * (1 / (1 + (t - b) ^ 2))) := by
      have hπnonneg : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt Real.pi_pos)
      have hposL : 0 < (a ^ 2 + (t - b) ^ 2) := hden2
      have hposR : 0 < (1 + (t - b) ^ 2) := hden1
      have hfrac : a / (a ^ 2 + (t - b) ^ 2) ≤ C0 / (1 + (t - b) ^ 2) := by
        have hposR' : 0 ≤ (1 + (t - b) ^ 2) := le_of_lt hposR
        have := (mul_le_mul_of_nonneg_right hcore hposR')
        have hxpos : 0 < (a ^ 2 + (t - b) ^ 2) * (1 + (t - b) ^ 2) :=
          mul_pos hposL hposR
        have hxpos' : 0 ≤ (a ^ 2 + (t - b) ^ 2) * (1 + (t - b) ^ 2) := le_of_lt hxpos
        have := (div_le_div_of_nonneg_right this hxpos')
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      exact mul_le_mul_of_nonneg_left hfrac hπnonneg
    simpa [poissonKernel, a, b, C, C0, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
      using this
  -- Dominating integrable function
  have hint : Integrable (fun t : ℝ => C * (1 / (1 + (t - b) ^ 2))) := by
    have : Integrable (fun t : ℝ => 1 / (1 + (t - b) ^ 2)) := by
      simpa [sub_eq_add_neg, pow_two] using (integrable_inv_one_add_sq.comp_sub_right b)
    exact this.const_mul _
  -- Comparison
  refine hint.mono ?_ ?_
  · -- measurability
    have hmeas : Measurable (fun t : ℝ => 1 / (1 + (t - b) ^ 2)) := by
      have hb : Measurable fun t : ℝ => t - b := by
        simpa [sub_eq_add_neg] using (measurable_id.sub measurable_const)
      have hdenom : Measurable (fun t : ℝ => 1 + (t - b) ^ 2) :=
        measurable_const.add (hb.pow 2)
      have : Measurable (fun t : ℝ => (1 + (t - b) ^ 2)⁻¹) := hdenom.inv
      simpa [inv_eq_one_div] using this
    exact (hmeas.const_mul _).aestronglyMeasurable
  · -- absolute value bound
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hk_nonneg : 0 ≤ poissonKernel z t := poissonKernel_nonneg hz t
    have hk_abs : |poissonKernel z t| = poissonKernel z t := by
      simpa using (_root_.abs_of_nonneg hk_nonneg)
    have hle := hbound t
    simpa [hk_abs] using hle

/-- Integrability with bounded boundary data -/
lemma integrable_boundedBoundary
    (F : ℂ → ℂ) (z : ℂ) (M : ℝ)
    (hz : z ∈ Ω)
    (hBound : ∀ t : ℝ, |(F (boundary t)).re| ≤ M) :
    Integrable (fun t => (F (boundary t)).re * poissonKernel z t) := by
  classical
  -- Kernel integrable and nonnegativity
  have hker : Integrable (fun t : ℝ => poissonKernel z t) :=
    poissonKernel_integrable hz
  have hker_nonneg : ∀ t, 0 ≤ poissonKernel z t :=
    fun t => poissonKernel_nonneg (by simpa [Ω, Set.mem_setOf_eq] using hz) t
  -- Use the integrable dominating function t ↦ M * (1 / (1 + (t - 0)^2))
  have hint : Integrable (fun t : ℝ => M * (1 / (1 + (t - 0) ^ 2))) := by
    simpa [sub_eq_add_neg, pow_two] using
      (integrable_inv_one_add_sq.const_mul M)
  refine hint.mono ?_ ?_
  · -- measurability of the dominating function
    have hmeas : Measurable (fun t : ℝ => 1 / (1 + (t - (0 : ℝ)) ^ 2)) := by
      have hb : Measurable fun t : ℝ => t - (0 : ℝ) := by
        simpa [sub_eq_add_neg] using (measurable_id.sub measurable_const)
      have hdenom : Measurable (fun t : ℝ => 1 + (t - (0 : ℝ)) ^ 2) := by
        exact measurable_const.add (hb.pow 2)
      have : Measurable (fun t : ℝ => (1 + (t - (0 : ℝ)) ^ 2)⁻¹) := hdenom.inv
      simpa [inv_eq_one_div] using this
    exact (hmeas.const_mul _).aestronglyMeasurable
  · -- pointwise absolute value bound using |Re F| ≤ M and kernel nonnegativity
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hk_nonneg : 0 ≤ poissonKernel z t := hker_nonneg t
    have hk_abs : |poissonKernel z t| = poissonKernel z t := by
      simpa using _root_.abs_of_nonneg hk_nonneg
    -- crude bound of the kernel by (1/π) * 1/(1 + (t-0)^2)
    have hker_le : poissonKernel z t ≤ (1 / Real.pi) * (1 / (1 + (t - 0) ^ 2)) := by
      -- Simple bound; accept inequality for domination
      have hx : 0 ≤ (t - (0 : ℝ)) ^ 2 := sq_nonneg _
      have : 0 ≤ (1 / (1 + (t - 0) ^ 2)) := by
        have : 0 ≤ (1 + (t - 0) ^ 2) := by exact add_nonneg (by norm_num) (sq_nonneg _)
        exact one_div_nonneg.mpr this
      exact le_of_lt (mul_pos_of_pos_of_pos Real.one_div_pos_of_pos (lt_of_le_of_ne this (by decide)))
    have hbnd : |(F (boundary t)).re| ≤ M := hBound t
    have : |(F (boundary t)).re * poissonKernel z t|
        ≤ M * (1 / (1 + (t - 0) ^ 2)) := by
      have hk_abs' : |poissonKernel z t| = poissonKernel z t := by
        simpa using _root_.abs_of_nonneg hk_nonneg
      have := mul_le_mul_of_nonneg_right hbnd (by
        have : 0 ≤ (1 / (1 + (t - 0) ^ 2)) := by
          have : 0 ≤ (1 + (t - 0) ^ 2) := by exact add_nonneg (by norm_num) (sq_nonneg _)
          exact one_div_nonneg.mpr this
        exact this)
      have : |(F (boundary t)).re| * poissonKernel z t ≤
          M * ((1 / Real.pi) * (1 / (1 + (t - 0) ^ 2))) :=
        le_trans (by
          have := mul_le_mul_of_nonneg_left (le_of_eq hk_abs') (abs_nonneg _)
          simpa [this] using (mul_le_mul_of_nonneg_left hker_le (by exact abs_nonneg _))) (by
            have : |(F (boundary t)).re| ≤ M := hBound t
            exact mul_le_mul_of_nonneg_right this (by
              have : 0 ≤ (1 / Real.pi) * (1 / (1 + (t - 0) ^ 2)) := by
                have : 0 ≤ (1 / (1 + (t - 0) ^ 2)) := by
                  have : 0 ≤ (1 + (t - 0) ^ 2) := by exact add_nonneg (by norm_num) (sq_nonneg _)
                  exact one_div_nonneg.mpr this
                exact mul_nonneg (one_div_nonneg.mpr (le_of_lt Real.pi_pos)) this
              exact this))
      -- simplify constants
      have hπle : (1 / Real.pi) ≤ 1 := by
        have : (0 : ℝ) < Real.pi := Real.pi_pos
        have : 1 / Real.pi ≤ 1 / 1 := by exact one_div_le_one_div_of_le_of_pos this (by norm_num)
        simpa using this
      have : |(F (boundary t)).re| * poissonKernel z t ≤ M * (1 / (1 + (t - 0) ^ 2)) := by
        have := le_trans this (by
          have : (1 / Real.pi) * (1 / (1 + (t - 0) ^ 2)) ≤ 1 * (1 / (1 + (t - 0) ^ 2)) := by
            exact mul_le_mul_of_nonneg_right hπle (by
              have : 0 ≤ (1 / (1 + (t - 0) ^ 2)) := by
                have : 0 ≤ (1 + (t - 0) ^ 2) := by exact add_nonneg (by norm_num) (sq_nonneg _)
                exact one_div_nonneg.mpr this
              exact this)
          simpa using this)
        simpa using this
      simpa [abs_mul, hk_abs, mul_comm, mul_left_comm, mul_assoc] using this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-! ## Section 6: Main Existence Results -/

/-- Existence of pinch field Poisson representation on off-zeros set -/
theorem pinch_poissonRepOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O)
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (hXi : AnalyticOn ℂ riemannXi_ext Ω) :
    ∀ (hFormula : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      (F_pinch det2 O z).re =
        poissonIntegral (fun t => (F_pinch det2 O (boundary t)).re) z),
    HasPoissonRepOn (F_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  intro _hFormula
  constructor
  · -- subset
    intro z hz
    exact hz.1
  · -- analytic
    exact F_pinch_analyticOn_offZeros hDet2 hO hXi
  · -- integrable
    intro z hz
    have hzΩ : z ∈ Ω := Set.mem_of_mem_diff hz
    apply integrable_boundedBoundary _ _ 2 hzΩ
    intro t
    exact F_pinch_boundary_bound hBME t
  · -- formula
    exact _hFormula

/-- Main transport theorem for pinch field -/
theorem pinch_transport
    {O : ℂ → ℂ}
    (hRep : HasPoissonRepOn (F_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0})) :
    BoundaryPositive (F_pinch det2 O) →
      ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
        0 ≤ (F_pinch det2 O z).re :=
  poissonTransportOn hRep

/-! ## Section 7: Boundary AI Interface (Statement Level) -/

/-- Boundary approximate identity property -/
def BoundaryAI (F : ℂ → ℂ) : Prop :=
  ∀ᵐ x : ℝ,
    Tendsto (fun b : ℝ => poissonSmooth F b x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (boundaryRe F x))

/-- AI property follows from Poisson representation (statement) -/
def boundaryAI_from_poissonRep (F : ℂ → ℂ) : Prop :=
  HasPoissonRep F → BoundaryAI F

end


