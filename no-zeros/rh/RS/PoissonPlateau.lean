/-
  rh/RS/PoissonPlateau.lean

  Poisson plateau: a concrete even window ψ with a uniform positive lower bound
  for its Poisson smoothing on the unit Carleson box (|x| ≤ 1, 0 < b ≤ 1).

  We use the simple top-hat window ψ = (1/4)·1_{[-2,2]} and show that
    (P_b * ψ)(x) ≥ 1/(4π) for all 0 < b ≤ 1 and |x| ≤ 1.

  Mathlib-only; no axioms.
-/

-- NOTE: Demonstration marker edit. Safe to keep or remove; has no effect on proofs.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Topology.Support

noncomputable section

namespace RH
namespace RS

open Set MeasureTheory
open scoped MeasureTheory

/-- Normalized half-plane Poisson kernel on ℝ. -/
def poissonKernel (b u : ℝ) : ℝ := (1 / Real.pi) * (b / (u ^ 2 + b ^ 2))

lemma poissonKernel_nonneg {b u : ℝ} (hb : 0 ≤ b) : 0 ≤ poissonKernel b u := by
  have hπ : 0 ≤ (1 / Real.pi) := by
    have : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    simpa [one_div] using (inv_nonneg.mpr this)
  have hden : 0 ≤ u ^ 2 + b ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfrac : 0 ≤ b / (u ^ 2 + b ^ 2) := div_nonneg hb hden
  simpa [poissonKernel] using mul_nonneg hπ hfrac

/-- Fixed even, nonnegative, compactly supported window ψ = (1/4)·1_{[-2,2]}. -/
@[simp] def psi (t : ℝ) : ℝ := (Icc (-2 : ℝ) 2).indicator (fun _ => (1 / 4 : ℝ)) t

lemma psi_nonneg : ∀ t, 0 ≤ psi t := by
  intro t; by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · simp [psi, Set.indicator_of_mem ht]
  · simp [psi, Set.indicator_of_not_mem ht]

-- (Optional) ψ is even (not used below, but recorded for completeness)
lemma psi_even_pointwise : ∀ t, psi (-t) = psi t := by
  intro t
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · have hneg : -t ∈ Icc (-2 : ℝ) 2 := by
      rcases ht with ⟨hL, hR⟩; exact ⟨by simpa using (neg_le_neg hR), by simpa using (neg_le_neg hL)⟩
    simp [psi, Set.indicator_of_mem ht, Set.indicator_of_mem hneg]
  · have hneg : -t ∉ Icc (-2 : ℝ) 2 := by
      by_contra hmem; rcases hmem with ⟨hL, hR⟩
      exact ht ⟨by simpa using (neg_le_neg hR), by simpa using (neg_le_neg hL)⟩
    simp [psi, Set.indicator_of_not_mem ht, Set.indicator_of_not_mem hneg]

lemma psi_even : Function.Even psi := by
  intro t; exact psi_even_pointwise t

lemma psi_hasCompactSupport : HasCompactSupport psi := by
  -- Topological support equals the closed interval [-2,2]
  change IsCompact (tsupport psi)
  have hts : tsupport psi = Icc (-2 : ℝ) 2 := by
    -- tsupport = closure of pointwise support; here support is exactly Icc (-2,2)
    have : Function.support psi = Icc (-2 : ℝ) 2 := by
      ext t; constructor
      · intro ht
        by_contra hnot
        have : psi t = 0 := by simp [psi, Set.indicator_of_not_mem hnot]
        exact ht this
      · intro ht
        have : psi t = (1 / (4 : ℝ)) := by simp [psi, Set.indicator_of_mem ht]
        exact by simpa [this]
    simpa [tsupport, this, isClosed_Icc.closure_eq]
  simpa [hts] using (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2))

lemma psi_integral_one : ∫ t, psi t ∂(volume) = 1 := by
  have hmeas : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
  have hpt : (fun t => psi t) = (Icc (-2 : ℝ) 2).indicator (fun _ => (1 / (4 : ℝ))) := by
    funext t; by_cases ht : t ∈ Icc (-2 : ℝ) 2 <;> simp [psi, ht]
  -- Use indicator integral with integrability on a finite-measure set
  have hμS : (volume (Icc (-2 : ℝ) 2)) < ⊤ := by
    simp [Real.volume_Icc]
  have hIntS : IntegrableOn (fun _ => (1 / (4 : ℝ))) (Icc (-2 : ℝ) 2) (volume) :=
    integrableOn_const.mpr (Or.inr hμS)
  have hindEq : ∫ t, (Icc (-2 : ℝ) 2).indicator (fun _ => (1 / (4 : ℝ))) t ∂(volume)
      = ∫ t in Icc (-2 : ℝ) 2, (1 / (4 : ℝ)) ∂(volume) := by
    simpa [integral_indicator, hmeas] using hIntS
  calc
    ∫ t, psi t ∂(volume)
        = ∫ t, (Icc (-2 : ℝ) 2).indicator (fun _ => (1 / (4 : ℝ))) t ∂(volume) := by
              simpa [hpt]
    _   = ∫ t in Icc (-2 : ℝ) 2, (1 / (4 : ℝ)) ∂(volume) := hindEq
    _   = (volume (Icc (-2 : ℝ) 2)).toReal * (1 / (4 : ℝ)) := by
              simp [integral_const]
    _   = ((2 : ℝ) - (-2)) * (1 / (4 : ℝ)) := by
              simp [Real.volume_Icc, sub_eq_add_neg]
    _   = 1 := by norm_num

/-- The Poisson smoothing of ψ at height b and horizontal coordinate x. -/
@[simp] def poissonSmooth (b x : ℝ) : ℝ := ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t)

@[simp] def c0_plateau : ℝ := 4⁻¹ * Real.pi⁻¹

lemma c0_plateau_pos : 0 < c0_plateau := by
  have h4 : 0 < (4 : ℝ) := by norm_num
  have hπ : 0 < Real.pi := Real.pi_pos
  have h4inv : 0 < (4 : ℝ)⁻¹ := inv_pos.mpr h4
  have hπinv : 0 < Real.pi⁻¹ := inv_pos.mpr hπ
  have : 0 < (4 : ℝ)⁻¹ * Real.pi⁻¹ := mul_pos h4inv hπinv
  simpa [c0_plateau] using this

/-- Uniform plateau lower bound: (P_b * ψ)(x) ≥ 1/(4π) for 0 < b ≤ 1, |x| ≤ 1. -/
theorem poisson_plateau_lower_bound
  {b x : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hx : |x| ≤ 1) :
  c0_plateau ≤ poissonSmooth b x := by
  classical
  -- The big interval S and a length-2b subinterval J around x
  set S : Set ℝ := Icc (-2 : ℝ) 2
  have hS_meas : MeasurableSet S := isClosed_Icc.measurableSet
  have hb0 : 0 ≤ b := le_of_lt hb
  have hxI : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
  -- J := [x - b, x + b] ⊆ [-2,2]
  have hJsubset : Icc (x - b) (x + b) ⊆ S := by
    intro t ht
    exact ⟨by linarith [hxI.1, hb1, ht.1], by linarith [hxI.2, hb1, ht.2]⟩
  -- Nonnegativity of the kernel
  have hnonneg : ∀ t, 0 ≤ poissonKernel b (x - t) :=
    fun t => poissonKernel_nonneg (b := b) (u := x - t) hb0
  -- Monotonicity of integrals on sets (nonnegative integrand)
  have int_mono : ∫ t in S, poissonKernel b (x - t)
                    ≥ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) := by
    -- reduce to indicators and compare pointwise
    have hpt : (S.indicator fun t => poissonKernel b (x - t))
                ≥ (Icc (x - b) (x + b)).indicator (fun t => poissonKernel b (x - t)) := by
      intro t
      by_cases htJ : t ∈ Icc (x - b) (x + b)
      · have htS : t ∈ S := hJsubset htJ
        have : poissonKernel b (x - t) ≤ poissonKernel b (x - t) := le_rfl
        simpa [Set.indicator_of_mem htS, Set.indicator_of_mem htJ] using this
      · by_cases htS : t ∈ S
        · have : 0 ≤ poissonKernel b (x - t) := hnonneg t
          simpa [Set.indicator_of_mem htS, Set.indicator_of_not_mem htJ] using this
        · have : 0 ≤ 0 := le_rfl
          simpa [Set.indicator_of_not_mem htS, Set.indicator_of_not_mem htJ] using this
    have hintS : Integrable (S.indicator fun t => poissonKernel b (x - t)) := by
      -- continuity on compact interval ⇒ integrable
      have cont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
        have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
          Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
        have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
          intro t; have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb); exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
        have hrec : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) :=
          continuous_const.div hden (by intro t; exact hpos t)
        simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using continuous_const.mul (continuous_const.mul hrec)
      -- use continuity on compact interval [-2,2]
      -- provide IntegrableOn on the set and switch via indicator
      have hI : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (-2 : ℝ) 2) volume := by
        have hInt : IntervalIntegrable (fun t : ℝ => poissonKernel b (x - t)) volume (-2 : ℝ) 2 :=
          (cont.intervalIntegrable (μ := volume) (-2 : ℝ) 2)
        have hle : (-2 : ℝ) ≤ 2 := by norm_num
        simpa [intervalIntegrable_iff_integrableOn_Icc_of_le hle] using hInt
      simpa [integrable_indicator_iff, hS_meas] using hI
    have hintJ : Integrable ((Icc (x - b) (x + b)).indicator fun t => poissonKernel b (x - t)) := by
      have cont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
        have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
          Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
        have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
          intro t; have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb); exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
        have hrec : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) :=
          continuous_const.div hden (by intro t; exact hpos t)
        simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using continuous_const.mul (continuous_const.mul hrec)
      have : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (x - b) (x + b)) volume := by
        have hInt : IntervalIntegrable (fun t : ℝ => poissonKernel b (x - t)) volume (x - b) (x + b) :=
          (cont.intervalIntegrable (μ := volume) (x - b) (x + b))
        have hle : (x - b) ≤ (x + b) := by linarith [hb0]
        simpa [intervalIntegrable_iff_integrableOn_Icc_of_le hle] using hInt
      have hmeasJ : MeasurableSet (Icc (x - b) (x + b)) := isClosed_Icc.measurableSet
      simpa [integrable_indicator_iff, hmeasJ] using this
    have := integral_mono_ae (μ := volume) hintJ hintS (ae_of_all _ hpt)
    simpa [integral_indicator, hS_meas, isClosed_Icc.measurableSet] using this
  -- Pointwise lower bound on J: for t ∈ J, |x - t| ≤ b ⇒ denominator ≤ 2 b^2
  have kernel_lb : ∀ t ∈ Icc (x - b) (x + b), b⁻¹ * (Real.pi⁻¹ * 2⁻¹) ≤ poissonKernel b (x - t) := by
    intro t ht
    have hdist : |x - t| ≤ b := by
      have h1 : -b ≤ t - x := by linarith [ht.1]
      have h2 : t - x ≤ b := by linarith [ht.2]
      have : |t - x| ≤ b := abs_le.mpr ⟨h1, h2⟩
      simpa [abs_sub_comm] using this
    have hbpos : 0 < b := hb
    have hb2pos : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hbpos)
    have sq_le : (x - t) ^ 2 ≤ b ^ 2 := by
      have habs : |x - t| ≤ |b| := by simpa [abs_of_nonneg hb0, abs_sub_comm] using hdist
      simpa [pow_two] using (sq_le_sq.mpr habs)
    have den_le : (x - t) ^ 2 + b ^ 2 ≤ 2 * b ^ 2 := by
      have := add_le_add_right sq_le (b ^ 2); simpa [two_mul] using this
    have den_pos : 0 < (x - t) ^ 2 + b ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) hb2pos
    have inv_le : (1 : ℝ) / (2 * b ^ 2) ≤ (1 : ℝ) / ((x - t) ^ 2 + b ^ 2) :=
      one_div_le_one_div_of_le den_pos den_le
    have cnonneg : 0 ≤ (1 / Real.pi) * b :=
      mul_nonneg (le_of_lt (one_div_pos.mpr Real.pi_pos)) hb0
    -- multiply by nonnegative constant and rewrite to kernel form
    have hstep := mul_le_mul_of_nonneg_left inv_le cnonneg
    -- canonical constant shape
    have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
    have : b⁻¹ * (Real.pi⁻¹ * 2⁻¹)
        ≤ (1 / Real.pi) * b * (1 / ((x - t) ^ 2 + b ^ 2)) := by
      -- (1/π)·b·(1/(2b²)) = b⁻¹·(π⁻¹·2⁻¹)
      have h' := hstep
      simpa [one_div, pow_two, hbne, mul_comm, mul_left_comm, mul_assoc]
        using h'
    -- identify RHS with the kernel
    have : b⁻¹ * (Real.pi⁻¹ * 2⁻¹) ≤ poissonKernel b (x - t) := by
      simpa [poissonKernel, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this
    exact this
  -- Lower bound the integral over J by a constant times its length 2b
  have measJ_toReal : (volume (Icc (x - b) (x + b))).toReal = 2 * b := by
    have hxblt : x - b ≤ x + b := by linarith [hb0]
    calc
      (volume (Icc (x - b) (x + b))).toReal
          = (ENNReal.ofReal ((x + b) - (x - b))).toReal := by
              simpa [Real.volume_Icc, hxblt, sub_eq_add_neg]
      _ = ((x + b) - (x - b)) := by
              have hnn : 0 ≤ ((x + b) - (x - b)) := by linarith [hb0]
              simpa [ENNReal.toReal_ofReal, hnn]
      _ = 2 * b := by ring
  have constJ : (∫ t in Icc (x - b) (x + b), poissonKernel b (x - t))
                  ≥ (b⁻¹ * (Real.pi⁻¹ * 2⁻¹)) * (volume (Icc (x - b) (x + b))).toReal := by
    have hmeasJ : MeasurableSet (Icc (x - b) (x + b)) := isClosed_Icc.measurableSet
    have hμJ : (volume (Icc (x - b) (x + b))) < ⊤ := by
      simp [Real.volume_Icc]
    -- continuity → integrableOn on J
    have hcont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
      have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
        Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
      have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
        intro t
        have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb)
        exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
      have hrec : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) :=
        continuous_const.div hden (by intro t; exact hpos t)
      simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
        using continuous_const.mul (continuous_const.mul hrec)
    have hint_on : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (x - b) (x + b)) volume := by
      have hInt : IntervalIntegrable (fun t : ℝ => poissonKernel b (x - t)) volume (x - b) (x + b) :=
        (hcont.intervalIntegrable (μ := volume) (x - b) (x + b))
      have hle : (x - b) ≤ (x + b) := by linarith [hb0]
      simpa [intervalIntegrable_iff_integrableOn_Icc_of_le hle] using hInt
    -- Turn both integrals on J into indicator-form whole-line integrals
    have hint : Integrable ((Icc (x - b) (x + b)).indicator (fun t => poissonKernel b (x - t))) := by
      simpa [integrable_indicator_iff, hmeasJ] using hint_on
    have hint_c : Integrable ((Icc (x - b) (x + b)).indicator (fun _ => (b⁻¹ * (Real.pi⁻¹ * 2⁻¹)))) := by
      have : IntegrableOn (fun _ => (b⁻¹ * (Real.pi⁻¹ * 2⁻¹))) (Icc (x - b) (x + b)) volume :=
        (integrableOn_const.mpr (Or.inr hμJ))
      simpa [integrable_indicator_iff, hmeasJ] using this
    -- Pointwise indicator inequality a.e.
    have hpt : (Icc (x - b) (x + b)).indicator (fun _ => (b⁻¹ * (Real.pi⁻¹ * 2⁻¹)))
                ≤ᵐ[volume]
                (Icc (x - b) (x + b)).indicator (fun t => poissonKernel b (x - t)) := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      by_cases ht : t ∈ Icc (x - b) (x + b)
      · have hk := kernel_lb t ht
        simpa [Set.indicator_of_mem ht] using hk
      · simp [Set.indicator_of_not_mem ht]
    -- Compare integrals on ℝ of indicators
    have hineq := integral_mono_ae (μ := volume) hint_c hint hpt
    -- Evaluate constant indicator integral
    -- Evaluate the constant-indicator integral with the measure factor on the left
    have hconst : ∫ t, (Icc (x - b) (x + b)).indicator (fun _ => (b⁻¹ * (Real.pi⁻¹ * 2⁻¹))) t
                    = (volume (Icc (x - b) (x + b))).toReal * (b⁻¹ * (Real.pi⁻¹ * 2⁻¹)) := by
      -- ∫ indicator c = ∫_J c = (μ J).toReal * c
      simpa [integral_indicator, hmeasJ, integral_const, mul_comm, mul_left_comm, mul_assoc]
        using rfl
    -- Identify the function indicator integral with the set integral (poissonKernel form)
    have hfun : ∫ t, (Icc (x - b) (x + b)).indicator (fun t => poissonKernel b (x - t)) t
                  = ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) := by
      -- ∫ indicator f = ∫_J f
      simp [integral_indicator, hmeasJ]
    -- Same identification for the expanded kernel form used by simp
    have hfun_explicit : ∫ t,
        (Icc (x - b) (x + b)).indicator (fun t => Real.pi⁻¹ * (b / ((x - t) ^ 2 + b ^ 2))) t
        = ∫ t in Icc (x - b) (x + b), Real.pi⁻¹ * (b / ((x - t) ^ 2 + b ^ 2)) := by
      simp [integral_indicator, hmeasJ]
    -- Start from hineq and rewrite both sides step by step
    have h1 : (volume (Icc (x - b) (x + b))).toReal * (b⁻¹ * (Real.pi⁻¹ * 2⁻¹))
              ≤ ∫ t, (Icc (x - b) (x + b)).indicator (fun t => poissonKernel b (x - t)) t := by
      simpa [hconst, mul_comm, mul_left_comm, mul_assoc] using hineq
    have h2 : (volume (Icc (x - b) (x + b))).toReal * (b⁻¹ * (Real.pi⁻¹ * 2⁻¹))
              ≤ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) := by
      simpa [hfun, integral_indicator, hmeasJ] using h1
    -- Reorder factors to match the statement
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2
  -- Integral over S ≥ integral over J; rewrite |J| = 2b and compute constants to get π⁻¹ ≤ ∫_S ...
  have base2 : Real.pi⁻¹ ≤ ∫ t in S, poissonKernel b (x - t) := by
    have hge := ge_trans int_mono constJ
    have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb
    have hcollapse : (b⁻¹ * (Real.pi⁻¹ * 2⁻¹)) * (2 * b) = Real.pi⁻¹ := by
      have : b⁻¹ * (2 * b) = 2 := by field_simp [hbne]
      calc
        (b⁻¹ * (Real.pi⁻¹ * 2⁻¹)) * (2 * b)
            = (Real.pi⁻¹ * 2⁻¹) * (b⁻¹ * (2 * b)) := by ring
        _ = (Real.pi⁻¹ * 2⁻¹) * 2 := by simpa [this]
        _ = Real.pi⁻¹ := by simp [one_div]
    -- move from ≥ to ≤ by commuting sides
    have : (b⁻¹ * (Real.pi⁻¹ * 2⁻¹)) * (2 * b) ≤ ∫ t in S, poissonKernel b (x - t) := by
      simpa [measJ_toReal, mul_comm, mul_left_comm, mul_assoc] using hge
    simpa [hcollapse] using this
  -- Since 0 ≤ π⁻¹ and (1/4) ≤ 1, we have (1/4)·π⁻¹ ≤ π⁻¹ ≤ ∫_S ...
  have hπ_nonneg : 0 ≤ (1 / Real.pi) := by
    have : 0 ≤ Real.pi := (le_of_lt Real.pi_pos)
    simpa [one_div] using inv_nonneg.mpr this
  have hshrink : (1 / (4 : ℝ)) * (1 / Real.pi) ≤ (1 / Real.pi) := by
    have hle : (1 / (4 : ℝ)) ≤ (1 : ℝ) := by norm_num
    exact mul_le_of_le_one_left hπ_nonneg hle
  -- also useful: rewrite b*(b⁻¹*π⁻¹) into π⁻¹ explicitly (for later simpa's)
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb
  have hbbinv : b * b⁻¹ = (1 : ℝ) := by field_simp [hbne]
  have hcollapse2 : b * (b⁻¹ * Real.pi⁻¹) = Real.pi⁻¹ := by
    calc
      b * (b⁻¹ * Real.pi⁻¹)
          = (b * b⁻¹) * Real.pi⁻¹ := by ring
      _ = Real.pi⁻¹ := by simpa [hbbinv]
  -- strengthen base2 into the expected b-form when needed
  have base_b_form : b * (b⁻¹ * Real.pi⁻¹) ≤ ∫ t in S, poissonKernel b (x - t) := by
    have : Real.pi⁻¹ ≤ ∫ t in S, poissonKernel b (x - t) := base2
    simpa [hcollapse2]
  have : (1 / (4 : ℝ)) * (1 / Real.pi) ≤ ∫ t in S, poissonKernel b (x - t) := by
    exact le_trans (by simpa [mul_comm, mul_left_comm, mul_assoc] using hshrink) base2
  -- Rewrite to `poissonSmooth` and `c0_plateau`
  have conv_eq : poissonSmooth b x = ∫ t in S, poissonKernel b (x - t) := rfl
  have c0_eq : c0_plateau = (1 / (4 : ℝ)) * (1 / Real.pi) := by
    simp [c0_plateau, one_div, mul_comm, mul_left_comm, mul_assoc]
  simpa [conv_eq, c0_eq, one_div] using this

/-!
Existence form consumed by the wedge assembly: pick ψ, prove the basic
properties, and supply c0 = 1/(4π) with the uniform lower bound.
-/
lemma poisson_plateau_c0 :
  ∃ ψ : ℝ → ℝ, Function.Even ψ ∧ (∀ t, 0 ≤ ψ t) ∧ HasCompactSupport ψ ∧
    (∫ t, psi t ∂(volume) = 1) ∧
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ {b x : ℝ}, 0 < b → b ≤ 1 → |x| ≤ 1 →
      (∫ t, poissonKernel b (x - t) * psi t ∂(volume)) ≥ c0 := by
  refine ⟨psi, psi_even, psi_nonneg, psi_hasCompactSupport, ?mass, ⟨c0_plateau, c0_plateau_pos, ?bound⟩⟩
  · simpa using psi_integral_one
  · intro b x hb hb1 hx
    -- rewrite convolution against ψ as a set integral on [-2,2]
    have hmeas : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
    have hpt : (fun t => poissonKernel b (x - t) * psi t)
                = (Icc (-2 : ℝ) 2).indicator (fun t => (1/4 : ℝ) * poissonKernel b (x - t)) := by
      funext t
      by_cases ht : t ∈ Icc (-2 : ℝ) 2
      · simp [psi, Set.indicator_of_mem ht, mul_comm, mul_left_comm, mul_assoc]
      · simp [psi, Set.indicator_of_not_mem ht]
    -- Rewrite the convolution as a set integral
    have hcont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
      have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
        Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
      have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
        intro t; have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb)
        exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
      have hrec : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) :=
        continuous_const.div hden (by intro t; exact hpos t)
      simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
        using continuous_const.mul (continuous_const.mul hrec)
    have hInt_on : IntegrableOn (fun t => poissonKernel b (x - t)) (Icc (-2 : ℝ) 2) (volume) := by
      -- continuity on compact ⇒ integrableOn
      have hInt : IntervalIntegrable (fun t : ℝ => poissonKernel b (x - t)) volume (-2 : ℝ) 2 :=
        (hcont.intervalIntegrable (μ := volume) (-2 : ℝ) 2)
      have hle : (-2 : ℝ) ≤ 2 := by norm_num
      simpa [intervalIntegrable_iff_integrableOn_Icc_of_le hle] using hInt
    have hindEq : ∫ t, (Icc (-2 : ℝ) 2).indicator (fun t => (1/4 : ℝ) * poissonKernel b (x - t)) t ∂(volume)
                    = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := by
      -- Move between indicator and set integral, then pull out the constant
      have hInt_on' : IntegrableOn (fun t => (1/4 : ℝ) * poissonKernel b (x - t)) (Icc (-2 : ℝ) 2) (volume) := by
        have : IntegrableOn (fun t => poissonKernel b (x - t)) (Icc (-2 : ℝ) 2) (volume) := hInt_on
        simpa [mul_comm, mul_left_comm, mul_assoc] using this.const_mul (1/4 : ℝ)
      have hset : ∫ t, (Icc (-2 : ℝ) 2).indicator (fun t => (1/4 : ℝ) * poissonKernel b (x - t)) t ∂(volume)
                    = ∫ t in Icc (-2 : ℝ) 2, (1/4 : ℝ) * poissonKernel b (x - t) ∂(volume) := by
        have hmeas : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
        simpa [integral_indicator, hmeas] using hInt_on'
      -- pull out the constant from the set integral
      have hlin : (∫ t in Icc (-2 : ℝ) 2, (1/4 : ℝ) * poissonKernel b (x - t) ∂(volume))
                    = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := by
        have hconst : (∫ t in Icc (-2 : ℝ) 2, (1/4 : ℝ) * poissonKernel b (x - t) ∂(volume))
                        = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := by
          simp [mul_comm, mul_left_comm, mul_assoc]
        simpa using hconst
      simpa [hlin, one_div] using hset
    have conv_eq : (∫ t, poissonKernel b (x - t) * psi t ∂(volume))
                    = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := by
      have hpt' : (fun t => poissonKernel b (x - t) * psi t)
                = (Icc (-2 : ℝ) 2).indicator (fun t => (1/4 : ℝ) * poissonKernel b (x - t)) := by
        funext t; by_cases ht : t ∈ Icc (-2 : ℝ) 2
        · simp [psi, Set.indicator_of_mem ht, mul_comm, mul_left_comm, mul_assoc]
        · simp [psi, Set.indicator_of_not_mem ht]
      simpa [hpt', mul_comm, mul_left_comm, mul_assoc] using hindEq
    -- apply the set bound proved above
    have base := poisson_plateau_lower_bound (b := b) (x := x) hb hb1 hx
    simpa [c0_plateau, conv_eq, one_div, mul_comm, mul_left_comm, mul_assoc] using base

end RS
end RH
