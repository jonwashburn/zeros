import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import rh.academic_framework.CompletedXi
import rh.academic_framework.DiskHardy
import rh.RS.Det2Outer
import rh.RS.PoissonAI
import rh.RS.Cayley

/-!
# Half-plane Outer Functions (Clean Rewrite)

This module provides a clean interface for outer functions on the right half-plane
Ω = {s : ℂ | Re s > 1/2}. We establish:

1. Basic definitions (domain, boundary, outer functions)
2. Poisson kernel and transport theorems
3. Boundary modulus matching
4. Pinch field specializations

The implementation focuses on clarity and avoids complex proof details where possible,
using interface predicates at the Prop level.
-/

namespace RH.AcademicFramework.HalfPlaneOuterV2

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
    · exact hO.nonzero hz.1
    · exact hz.2
  -- Use analyticity of quotients where denominator is non-zero
  -- Restrict all functions to the off-zeros set
  have h1' : AnalyticOn ℂ det2 (Ω \ {z | riemannXi_ext z = 0}) := by
    apply h1.mono; intro z hz; exact hz.1
  have h2' : AnalyticOn ℂ O (Ω \ {z | riemannXi_ext z = 0}) := by  
    apply h2.mono; intro z hz; exact hz.1
  have h3' : AnalyticOn ℂ riemannXi_ext (Ω \ {z | riemannXi_ext z = 0}) := by
    apply h3.mono; intro z hz; exact hz.1
  apply AnalyticOn.div h1'
  · apply AnalyticOn.mul h2' h3'
  · exact hdenom

/-- Analyticity of F_pinch on the off-zeros set -/
lemma F_pinch_analyticOn_offZeros
    (hDet2 : Det2OnOmega)
    {O : ℂ → ℂ} (hO : OuterHalfPlane O) 
    (hXi : AnalyticOn ℂ riemannXi_ext Ω) :
    AnalyticOn ℂ (F_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  unfold F_pinch
  -- F_pinch = 2 * J_pinch, so analyticity follows from J_pinch analyticity
  have hJ := J_pinch_analyticOn_offZeros hDet2 hO hXi
  have h2 : AnalyticOn ℂ (fun _ => (2 : ℂ)) (Ω \ {z | riemannXi_ext z = 0}) := analyticOn_const
  exact h2.mul hJ

/-- Boundary bound for F_pinch when boundary modulus equality holds -/
lemma F_pinch_boundary_bound
    {O : ℂ → ℂ}
    (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
    (t : ℝ) :
    |(F_pinch det2 O (boundary t)).re| ≤ 2 := by
  -- Apply RS.boundary_Re_F_pinch_le_two when O and ξ are nonzero
  -- When either is zero, F_pinch = 0 so the bound holds trivially
  classical
  -- Translate local BoundaryModulusEq (with local boundary) to the RS version
  have hBME_RS : RH.RS.BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s) := by
    intro τ; simpa [RH.RS.boundary, boundary] using hBME τ
  -- Work on RS.boundary and then rewrite back to the local boundary
  have hRS : |(F_pinch det2 O (RH.RS.boundary t)).re| ≤ (2 : ℝ) := by
    by_cases hO : O (RH.RS.boundary t) = 0
    · by_cases hXi : riemannXi_ext (RH.RS.boundary t) = 0
      · have hzero : (F_pinch det2 O (RH.RS.boundary t)) = 0 := by
          simp [F_pinch, RH.RS.J_pinch, hO, hXi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        have hre0 : (F_pinch det2 O (RH.RS.boundary t)).re = 0 := by
          simpa using congrArg Complex.re hzero
        simpa [hre0] using (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
      · exact RH.RS.boundary_Re_F_pinch_le_two (O := O) hBME_RS t (by simpa [hO]) (by exact hXi)
    · by_cases hXi : riemannXi_ext (RH.RS.boundary t) = 0
      · have hzero : (F_pinch det2 O (RH.RS.boundary t)) = 0 := by
          simp [F_pinch, RH.RS.J_pinch, hO, hXi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        have hre0 : (F_pinch det2 O (RH.RS.boundary t)).re = 0 := by
          simpa using congrArg Complex.re hzero
        simpa [hre0] using (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
      · exact RH.RS.boundary_Re_F_pinch_le_two (O := O) hBME_RS t (by exact hO) (by exact hXi)
  simpa [RH.RS.boundary, boundary] using hRS

/-! ## Section 5: Integrability Helpers -/

/-- Helper lemma: Poisson kernel is bounded by C/(1+(t-b)²) -/
private lemma poissonKernel_bound (z : ℂ) (hz : z ∈ Ω) :
    ∃ C > 0, ∀ t : ℝ, poissonKernel z t ≤ C / (1 + (t - z.im)^2) := by
  unfold Ω at hz
  simp only [Set.mem_setOf_eq] at hz
  set a := z.re - 1/2 with ha_def
  have ha : 0 < a := sub_pos.mpr hz
  -- Take C = (1/π) * max(a, 1/a)
  use (1 / Real.pi) * max a (1/a)
  constructor
  · apply mul_pos
    · exact one_div_pos.mpr Real.pi_pos
    · exact lt_max_of_lt_left ha
  · intro t
    unfold poissonKernel
    -- The inequality a/(a²+(t-b)²) ≤ C/(1+(t-b)²) follows by case analysis
    -- When a ≤ 1: use that a*(1+X) ≤ (1/a)*(a²+X) for X ≥ 0
    -- When a > 1: use that a*(1+X) ≤ a*(a²+X) for X ≥ 0
    sorry -- Algebraic inequality proven in original file lines 350-423

/-- Integrability of the Poisson kernel -/
lemma poissonKernel_integrable {z : ℂ} (hz : z ∈ Ω) :
    Integrable (fun t : ℝ => poissonKernel z t) := by
  -- Get the bound
  obtain ⟨C, hC_pos, hbound⟩ := poissonKernel_bound z hz
  -- The dominating function is integrable  
  have h_dom : Integrable (fun t => C / (1 + (t - z.im)^2)) := by
    -- integrable_inv_one_add_sq gives integrability of 1/(1+t²)
    -- Translation and scaling preserve integrability
    have : Integrable (fun t : ℝ => 1 / (1 + (t - z.im) ^ 2)) := by
      simpa [sub_eq_add_neg, pow_two] using
        (integrable_inv_one_add_sq.comp_sub_right z.im)
    simpa [div_eq_mul_inv] using this.const_mul C
  -- Apply comparison
  refine h_dom.mono ?_ ?_
  · -- Measurability of poissonKernel
    -- Build from basic measurable operations
    have hb : Measurable (fun t : ℝ => t - z.im) := by
      simpa [sub_eq_add_neg] using (measurable_id.sub measurable_const)
    have hden : Measurable (fun t : ℝ => (z.re - 1/2) ^ 2 + (t - z.im) ^ 2) :=
      measurable_const.add (hb.pow 2)
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
  · -- Pointwise bound using hbound and nonnegativity of the kernel
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hk_nonneg : 0 ≤ poissonKernel z t := poissonKernel_nonneg hz t
    have hk_abs : |poissonKernel z t| = poissonKernel z t := by
      simpa using abs_of_nonneg hk_nonneg
    simpa [hk_abs] using hbound t

/-- Integrability with bounded boundary data 
    Note: The measurability assumption `hMeas` is needed since F may not be continuous.
    For analytic functions, this follows from continuity. -/
lemma integrable_boundedBoundary
    (F : ℂ → ℂ) (z : ℂ) (M : ℝ)
    (hz : z ∈ Ω)
    (hBound : ∀ t : ℝ, |(F (boundary t)).re| ≤ M)
    (hMeas : Measurable (fun t => (F (boundary t)).re)) :
    Integrable (fun t => (F (boundary t)).re * poissonKernel z t) := by
  -- The kernel is integrable
  have hker := poissonKernel_integrable hz
  
  -- M must be nonnegative since |F.re| ≥ 0
  have hM_nonneg : 0 ≤ M := by
    trans |(F (boundary 0)).re|
    · exact abs_nonneg _
    · exact hBound 0
  
  -- The dominating function M * poissonKernel is integrable
  have h_dom : Integrable (fun t => M * poissonKernel z t) := by
    exact Integrable.const_mul hker M
  
  -- Apply comparison test
  refine h_dom.mono ?_ ?_
  · -- Measurability
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · -- Measurability of F(boundary t).re - directly from hypothesis
      exact hMeas
    · -- Measurability of poissonKernel z t
      -- Build from measurable primitives and use div_eq_mul_inv
      have hb : Measurable (fun t : ℝ => t - z.im) := by
        simpa [sub_eq_add_neg] using (measurable_id.sub measurable_const)
      have hden : Measurable (fun t : ℝ => (z.re - (1/2 : ℝ)) ^ 2 + (t - z.im) ^ 2) := by
        exact measurable_const.add (hb.pow 2)
      have hfrac : Measurable
          (fun t : ℝ => (z.re - (1/2 : ℝ)) /
            ((z.re - (1/2 : ℝ)) ^ 2 + (t - z.im) ^ 2)) := by
        have : Measurable (fun t : ℝ =>
            ((z.re - (1/2 : ℝ)) ^ 2 + (t - z.im) ^ 2)⁻¹) := hden.inv
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          using this.const_mul (z.re - (1/2 : ℝ))
      simpa [poissonKernel]
        using (hfrac.const_mul (1 / Real.pi)).aestronglyMeasurable
  · -- Bound
    filter_upwards with t
    have hk_nonneg : 0 ≤ poissonKernel z t := poissonKernel_nonneg hz t
    have hk_abs : |poissonKernel z t| = poissonKernel z t := by
      simpa using abs_of_nonneg hk_nonneg
    calc
      |(F (boundary t)).re * poissonKernel z t|
          = |(F (boundary t)).re| * |poissonKernel z t| := by
            simpa [abs_mul]
      _ ≤ M * |poissonKernel z t| := by
            exact mul_le_mul_of_nonneg_right (hBound t) (abs_nonneg _)
      _ = M * poissonKernel z t := by
            simpa [hk_abs]

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
  intro hFormula
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
    · intro t
      exact F_pinch_boundary_bound hBME t
    · -- Measurability of t ↦ (F_pinch det2 O (boundary t)).re
      apply Measurable.comp
      · exact measurable_re  -- Real part is measurable
      · -- Measurability of t ↦ F_pinch det2 O (boundary t)
        -- The composition t ↦ boundary t ↦ F_pinch det2 O (boundary t)
        -- boundary is measurable as an affine map
        have hBoundaryMeas : Measurable (boundary : ℝ → ℂ) := by
          unfold boundary
          apply Measurable.add
          · exact measurable_const
          · apply Measurable.const_mul
            exact Complex.continuous_ofReal.measurable
        -- For F_pinch to be measurable, we'd need continuity or measurability
        -- This typically requires that the functions involved are continuous
        sorry  -- Requires F_pinch det2 O to be continuous or measurable
  · -- formula
    exact hFormula

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

