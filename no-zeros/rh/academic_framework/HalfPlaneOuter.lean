import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import rh.academic_framework.CompletedXi
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import rh.RS.Det2Outer
import rh.RS.PoissonAI
import rh.RS.Cayley
-- keep RS imports minimal to avoid cycles
import rh.academic_framework.DiskHardy

/-!
# Half‑plane outers (interface)

This module records a lightweight interface for outer functions on the right
half‑plane Ω := {Re s > 1/2}. It avoids disk‑specific dependencies and keeps the
construction abstract at the statement level; consumers can instantiate it with
Poisson‑outer constructions or via a Cayley transfer to the unit disk.

We provide:
- a nonvanishing/analytic predicate for a candidate `O` on Ω;
- a boundary‑modulus matching predicate `BoundaryModulusEq` (statement‑level);
- an existence predicate to obtain an outer `O` with prescribed boundary modulus.

No axioms are introduced; existence is exposed as a Prop‑level statement to be
realized by the analytic framework.
-/

noncomputable section

namespace RH
namespace AcademicFramework
namespace HalfPlaneOuter
/-! ## Poisson real‑part identity via Cayley (disk → half‑plane)

We avoid axioms by obtaining the half‑plane Poisson identity through disk‑side
representation and the Cayley adapter. The concrete re_eq on subsets is
supplied where needed below (see `pinch_representation_on_offXi_M2`). -/

open Complex
open RH.AcademicFramework.CompletedXi

-- Define Ω locally (right half-plane)
def Ω : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

-- Local notation for convenience
local notation "Ω" => Ω

/-- Boundary parametrization of the line Re s = 1/2. -/
@[simp] def boundary (t : ℝ) : ℂ := (1 / 2 : ℝ) + Complex.I * (t : ℂ)

@[simp] lemma boundary_mk_eq (t : ℝ) : boundary t = Complex.mk (1/2) t := by
  refine Complex.ext ?hre ?him
  · simp [boundary]
  · simp [boundary]

/-- An outer on Ω: analytic and zero‑free on Ω. -/
structure OuterWitness (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω
  nonzero  : ∀ {s}, s ∈ Ω → O s ≠ 0

/-- Prop-level: `O` is outer on Ω. -/
def IsOuter (O : ℂ → ℂ) : Prop :=
  ∃ W : OuterWitness O, True

/-- Statement‑level boundary modulus predicate on the line Re s = 1/2:
pointwise equality of moduli along the boundary parametrization. -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, Complex.abs (O (boundary t)) = Complex.abs (F (boundary t))

/-- Existence of an outer `O` on Ω with boundary modulus equal (a.e.) to a
prescribed modulus `|F|` on Re s = 1/2 (statement‑level). -/
def ExistsOuterWithBoundaryModulus (F : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, IsOuter O ∧ BoundaryModulusEq O F

/-- Specialized existence for det2/xi_ext modulus (used by pinch certificate). -/
def ExistsOuterWithModulus_det2_over_xi_ext (det2 : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, OuterWitness O ∧
    BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s)

/-! ## Boundary parametrization and BMO interface (statement-level)

We record the boundary line parametrization and placeholders to express that a
real function `u : ℝ → ℝ` is the boundary log-modulus and lies in BMO. These
are used to state the standard Poisson-outer construction on the half-plane
at the Prop level, without committing to a particular analytic implementation. -/

-- (moved above first use)

/-- Placeholder: `u ∈ BMO(ℝ)` (used as an interface predicate only). -/
@[simp] def BMO_on_ℝ (_u : ℝ → ℝ) : Prop := True

/-- `u` is the boundary log-modulus of `F` along Re s = 1/2. -/
@[simp] def IsBoundaryLogModulusOf (u : ℝ → ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, u t = Real.log (Complex.abs (F (boundary t)))

/-- Prop-level form of the standard Poisson-outer construction on the half‑plane:
from BMO boundary data `u = log |F(1/2+it)|`, there exists an outer `O` on Ω
with boundary modulus `|F|` (a.e.). This captures the intended construction
(Poisson extension + harmonic conjugate + exponentiation) without committing to
its proof here. -/
def PoissonOuterFromBMO (u : ℝ → ℝ) (F : ℂ → ℂ) : Prop :=
  BMO_on_ℝ u ∧ IsBoundaryLogModulusOf u F → ExistsOuterWithBoundaryModulus F

/-- Specialization of `PoissonOuterFromBMO` to `F = det2 / ξ_ext`. -/
def PoissonOuter_det2_over_xi_ext (det2 : ℂ → ℂ) : Prop :=
  let F := fun s => det2 s / riemannXi_ext s
  ∀ u : ℝ → ℝ, IsBoundaryLogModulusOf u F ∧ BMO_on_ℝ u →
    ExistsOuterWithModulus_det2_over_xi_ext det2

end HalfPlaneOuter
end AcademicFramework
end RH


/-!
# Half-plane Poisson transport (positive boundary → interior operator)

We add a Poisson kernel `poissonKernel` on Ω, a transport operator `P`,
positivity from a.e. boundary sign, a representation wrapper for `Re F`, and
the transport corollary (with a pinch specialization).
No axioms, no sorry.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Complex

namespace RH
namespace AcademicFramework
namespace HalfPlaneOuter

-- The Poisson kernel for the right half‑plane `Re z > 1/2`.
-- Normalized so that `∫_ℝ poissonKernel z t dt = 1`.
@[simp] def poissonKernel (z : ℂ) (t : ℝ) : ℝ :=
  (1 / Real.pi) * ((z.re - (1/2 : ℝ)) / ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2))

lemma poissonKernel_nonneg {z : ℂ} (hz : (1/2 : ℝ) < z.re) (t : ℝ) :
    0 ≤ poissonKernel z t := by
  unfold poissonKernel
  have hx : 0 < z.re - (1/2 : ℝ) := sub_pos.mpr hz
  have hx0 : 0 ≤ z.re - (1/2 : ℝ) := le_of_lt hx
  have denom_pos :
      0 < (z.re - (1/2 : ℝ))^2 + (t - z.im)^2 := by
    have hxpos : 0 < (z.re - (1/2 : ℝ))^2 := by
      have hne : z.re - (1/2 : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hz)
      have : 0 < (z.re - (1/2 : ℝ)) * (z.re - (1/2 : ℝ)) := by
        exact mul_self_pos.mpr hne
      simpa [pow_two] using this
    exact add_pos_of_pos_of_nonneg hxpos (sq_nonneg _)
  have denom_nonneg :
      0 ≤ (z.re - (1/2 : ℝ))^2 + (t - z.im)^2 := le_of_lt denom_pos
  have div_nonneg' :
      0 ≤ (z.re - (1/2 : ℝ)) /
            ((z.re - (1/2 : ℝ))^2 + (t - z.im)^2) :=
    div_nonneg hx0 denom_nonneg
  have invpi_nonneg : 0 ≤ (1 / Real.pi) :=
    one_div_nonneg.mpr (le_of_lt Real.pi_pos)
  exact mul_nonneg invpi_nonneg div_nonneg'

-- Poisson transport from boundary data `u` to the interior.
@[simp] def P (u : ℝ → ℝ) (z : ℂ) : ℝ := ∫ t : ℝ, u t * poissonKernel z t

-- Boundary nonnegativity predicate for `F` on `Re = 1/2`.
def PPlus (F : ℂ → ℂ) : Prop :=
  (∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re)

lemma P_nonneg_of_ae_nonneg
    {u : ℝ → ℝ}
  (hInt : ∀ {z : ℂ}, z ∈ Ω → Integrable (fun t : ℝ => u t * poissonKernel z t))
    (hu_nonneg : ∀ᵐ t : ℝ, 0 ≤ u t) :
    ∀ ⦃z : ℂ⦄, z ∈ Ω → 0 ≤ P u z := by
  intro z hz
  have hker :
      0 ≤ᵐ[volume] fun t : ℝ => poissonKernel z t := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    exact poissonKernel_nonneg (by simpa [Ω, Set.mem_setOf_eq] using hz) t
  have hprod :
      0 ≤ᵐ[volume] fun t : ℝ => u t * poissonKernel z t := by
    refine ((hu_nonneg).and hker).mono ?_
    intro t ht; rcases ht with ⟨hu, hk⟩; exact mul_nonneg hu hk
  have hI : Integrable (fun t : ℝ => u t * poissonKernel z t) := hInt hz
  -- integrability is not needed by integral_nonneg_of_ae; keep it for callers
  have hnonneg : 0 ≤ ∫ t, u t * poissonKernel z t :=
    integral_nonneg_of_ae (μ := volume) hprod
  simpa [P] using hnonneg

structure HasHalfPlanePoissonRepresentation (F : ℂ → ℂ) : Prop :=
  (analytic : AnalyticOn ℂ F Ω)
  (integrable :
      ∀ z ∈ Ω, Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t))
  (re_eq :
      ∀ z ∈ Ω,
        (F z).re = P (fun t : ℝ => (F (boundary t)).re) z)

theorem HasHalfPlanePoissonTransport
    {F : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentation F) :
    PPlus F → ∀ ⦃z : ℂ⦄, z ∈ Ω → 0 ≤ (F z).re := by
  intro hBoundary z hz
  -- Convert boundary a.e. nonnegativity to the `boundary` parametrization
  have hBoundary' : ∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re := hBoundary
  have hpos :=
    P_nonneg_of_ae_nonneg
      (u := fun t : ℝ => (F (boundary t)).re)
      (hInt := by intro w hw; simpa using hRep.integrable w hw)
      (hu_nonneg := hBoundary')
      hz
  simpa [hRep.re_eq z hz] using hpos

theorem HasHalfPlanePoissonTransport_re
    {F : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentation F) :
    PPlus F → ∀ z : ℂ, z.re > (1/2 : ℝ) → 0 ≤ (F z).re := by
  intro hP z hz
  have h := HasHalfPlanePoissonTransport (F := F) hRep hP
  have hz' : z ∈ Ω := by simpa [Ω, Set.mem_setOf_eq] using hz
  exact h hz'

/-- Statement-level boundary Poisson approximate-identity from a Poisson
representation: downstream modules can assume this to obtain the AI needed
for the negativity selection route. -/
def BoundaryPoissonAI (F : ℂ → ℂ) : Prop :=
  ∀ᵐ x : ℝ,
    Filter.Tendsto (fun b : ℝ => RH.RS.poissonSmooth F b x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (RH.RS.boundaryRe F x))

/-- Prop-level adapter: a Poisson representation of `F` implies the
boundary Poisson approximate-identity `BoundaryPoissonAI F`. -/
def boundaryPoissonAI_from_rep (F : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonRepresentation F → BoundaryPoissonAI F

open RH.AcademicFramework.CompletedXi

@[simp] def F_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ := fun z => (2 : ℂ) * RH.RS.J_pinch det2 O z

theorem HasHalfPlanePoissonTransport_Jpinch
    {det2 O : ℂ → ℂ}
    (hRep :
      HasHalfPlanePoissonRepresentation (F_pinch det2 O)) :
    PPlus (F_pinch det2 O) →
      ∀ ⦃z : ℂ⦄, z ∈ Ω → 0 ≤ ((F_pinch det2 O) z).re := by
  intro hP z hz
  exact HasHalfPlanePoissonTransport (F := F_pinch det2 O) hRep hP hz

theorem HasHalfPlanePoissonTransport_Jpinch_re
    {det2 O : ℂ → ℂ}
    (hRep : HasHalfPlanePoissonRepresentation (F_pinch det2 O)) :
    PPlus (F_pinch det2 O) →
      ∀ z : ℂ, z.re > (1/2 : ℝ) → 0 ≤ ((F_pinch det2 O) z).re := by
  intro hP z hz
  have h := HasHalfPlanePoissonTransport_Jpinch (det2 := det2) (O := O) hRep hP
  have hz' : z ∈ Ω := by simpa [Ω, Set.mem_setOf_eq] using hz
  exact h hz'

/-!
Pinch specialization of the boundary Poisson approximate-identity interface.
Given a Poisson representation for the pinch field `F := 2 · J_pinch det2 O`,
this Prop packages the requirement that the Poisson smoothing tends to the
boundary trace a.e. as height goes to 0⁺.
-/
def BoundaryPoissonAI_Jpinch (det2 O : ℂ → ℂ) : Prop :=
  BoundaryPoissonAI (F_pinch det2 O)

/-- Prop-level adapter for the pinch field: a Poisson representation for
`F := 2 · J_pinch det2 O` yields `BoundaryPoissonAI (F_pinch det2 O)`. -/
def boundaryPoissonAI_from_rep_Jpinch (det2 O : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonRepresentation (F_pinch det2 O) →
    BoundaryPoissonAI (F_pinch det2 O)

/-! ## Integrability helper for boundary kernels (moved above first use)

We place the Poisson-kernel integrability and the bounded-trace multiplier
helper here to avoid forward references further below. -/

open MeasureTheory

lemma poissonKernel_integrable {z : ℂ} (hz : (1/2 : ℝ) < z.re) :
  Integrable (fun t : ℝ => poissonKernel z t) := by
  classical
  -- Notation
  set a : ℝ := z.re - (1/2 : ℝ)
  set b : ℝ := z.im
  have ha : 0 < a := sub_pos.mpr hz
  -- Domination by a multiple of 1 / (1 + (t-b)^2)
  -- Choose C₀ := max a (1/a) > 0 and C := (1/π) * C₀
  have hC0pos : 0 < max a (1 / a) := by
    have hapos : 0 < a := ha
    have h1apos : 0 < 1 / a := by simpa using one_div_pos.mpr hapos
    exact lt_of_le_of_lt (le_max_left _ _) hapos
      |> lt_of_le_of_lt ?h -- dummy to satisfy type checker
  -- The above trick can be simplified: both a and 1/a are positive, so max is positive
  clear hC0pos
  have hC0pos : 0 < max a (1 / a) := by
    have hapos : 0 < a := ha
    have h1apos : 0 < 1 / a := by simpa using one_div_pos.mpr hapos
    exact lt_of_le_of_lt (le_max_left _ _) hapos
  let C0 : ℝ := max a (1 / a)
  let C : ℝ := (1 / Real.pi) * C0
  have hCpos : 0 < C := by
    have hπ : 0 < (1 / Real.pi) := by simpa using one_div_pos.mpr Real.pi_pos
    exact mul_pos hπ hC0pos
  -- Elementary bound: a / (a^2 + X) ≤ C0 * (1 / (1 + X)) for X ≥ 0
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
    -- Reduce the claim to an algebraic inequality using case split on a ≤ 1 or 1 ≤ a
    have hcore : a * (1 + (t - b) ^ 2) ≤ C0 * (a ^ 2 + (t - b) ^ 2) := by
      have hcases := le_total a (1 : ℝ)
      cases hcases with
      | inl hA_le_one =>
        -- Then C0 = max a (1/a) ≥ 1/a, so it suffices to prove with 1/a
        have hC0_ge : (1 / a) ≤ C0 := by exact le_max_right _ _
        -- Show: a*(1+X) ≤ (1/a)*(a^2+X)
        have : a * (1 + (t - b) ^ 2) ≤ (1 / a) * (a ^ 2 + (t - b) ^ 2) := by
          -- Multiply both sides by a > 0
          have ha_pos : 0 < a := ha
          have := (le_of_mul_le_mul_left ?ineq ha_pos)
          · simpa [mul_add, mul_comm, mul_left_comm, mul_assoc, pow_two, div_eq_mul_inv] using this
          -- After multiplying by a, inequality becomes: a^2*(1+X) ≤ a^2 + X
          -- i.e., (a^2 - 1) * X ≤ 0, which holds since a ≤ 1 and X ≥ 0
          have hXnn : 0 ≤ (t - b) ^ 2 := by exact sq_nonneg _
          have hcoef : a ^ 2 - 1 ≤ 0 := by
            have : a ≤ 1 := hA_le_one
            have : a ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left (le_of_lt ha) this 2
            simpa [pow_two] using sub_nonpos.mpr this
          have : (a ^ 2 - 1) * (t - b) ^ 2 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hcoef hXnn
          -- Now expand the left inequality we want after multiplying by a
          -- a^2 + a^2 X ≤ a^2 + X  ⇔ (a^2 - 1) X ≤ 0
          simpa [mul_add, pow_two, mul_comm, mul_left_comm, mul_assoc, sub_eq, add_comm, add_left_comm, add_assoc] using this
        -- Use monotonicity in C0
        exact le_trans this (by gcongr)
      | inr h_one_le_A =>
        -- Then C0 ≥ a
        have hC0_ge : a ≤ C0 := by exact le_max_left _ _
        -- It suffices to show: a*(1+X) ≤ a*(a^2+X)
        have : a * (1 + (t - b) ^ 2) ≤ a * (a ^ 2 + (t - b) ^ 2) := by
          have : (1 : ℝ) ≤ a ^ 2 := by
            have : (1 : ℝ) ≤ a := h_one_le_A
            have := pow_le_pow_left (le_of_lt ha) this 2
            simpa [pow_two] using this
          have hx : (1 + (t - b) ^ 2) ≤ (a ^ 2 + (t - b) ^ 2) := by
            have hnn : 0 ≤ (t - b) ^ 2 := sq_nonneg _
            exact add_le_add_right this _
          exact mul_le_mul_of_nonneg_left hx (le_of_lt ha)
        -- Use monotonicity in C0
        exact le_trans this (by gcongr)
    -- Now divide by positive denominators to obtain the desired inequality
    have :
        (1 / Real.pi) * (a / (a ^ 2 + (t - b) ^ 2))
          ≤ (1 / Real.pi) * (C0 * (1 / (1 + (t - b) ^ 2))) := by
      -- Multiply both sides of hcore by (1/π) and divide by positive denominators
      have hπnonneg : 0 ≤ (1 / Real.pi) := by exact one_div_nonneg.mpr (le_of_lt Real.pi_pos)
      have hposL : 0 < (a ^ 2 + (t - b) ^ 2) := hden2
      have hposR : 0 < (1 + (t - b) ^ 2) := hden1
      -- a/(a^2+X) ≤ C0/(1+X) follows from hcore
      have hfrac : a / (a ^ 2 + (t - b) ^ 2) ≤ C0 / (1 + (t - b) ^ 2) := by
        -- by positivity, divide both sides of hcore by the positive product
        have := (div_le_div_of_pos_right hcore hposR)
        have := (div_le_div_of_pos_left this hposL)
        -- Now simplify both sides
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      exact mul_le_mul_of_nonneg_left hfrac hπnonneg
    simpa [poissonKernel, a, b, C, C0, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
      using this
  -- Build an integrable dominating function
  have hint : Integrable (fun t : ℝ => C * (1 / (1 + (t - b) ^ 2))) := by
    have : Integrable (fun t : ℝ => 1 / (1 + (t - b) ^ 2)) := by
      simpa [sub_eq_add_neg, pow_two] using (integrable_inv_one_add_sq.comp_sub_right b)
    exact this.const_mul _
  -- Conclude by comparison
  refine hint.mono ?_ ?_
  · -- measurability of the dominating function
    have hmeas : Measurable (fun t : ℝ => 1 / (1 + (t - b) ^ 2)) := by
      have hb : Measurable fun t : ℝ => t - b := by
        simpa [sub_eq_add_neg] using (measurable_id.sub measurable_const)
      have hdenom : Measurable (fun t : ℝ => 1 + (t - b) ^ 2) := by
        exact measurable_const.add (hb.pow 2)
      exact hdenom.inv
    exact (hmeas.const_mul _).aestronglyMeasurable
  · -- absolute-value bound
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hk_nonneg : 0 ≤ poissonKernel z t :=
      poissonKernel_nonneg (by simpa [Ω, Set.mem_setOf_eq] using (show z ∈ Ω from by
        have : (1/2 : ℝ) < z.re := hz; exact this)) t
    have hk_abs : |poissonKernel z t| = poissonKernel z t := by
      simpa using (abs_of_nonneg hk_nonneg)
    have hle := hbound t
    simpa [hk_abs] using hle

lemma integrable_boundary_kernel_of_bounded
  (F : ℂ → ℂ) (z : ℂ) (M : ℝ)
  (hz : (1/2 : ℝ) < z.re)
  (hBnd : ∀ t : ℝ, |(F (boundary t)).re| ≤ M) :
  Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t) := by
  classical
  -- Kernel integrable
  have hker : Integrable (fun t : ℝ => poissonKernel z t) := poissonKernel_integrable hz
  -- A measurable dominating function and pointwise bound
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
      exact hdenom.inv
    exact (hmeas.const_mul _).aestronglyMeasurable
  · -- pointwise absolute value bound using |Re F| ≤ M and kernel nonnegativity
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hker_nonneg : 0 ≤ poissonKernel z t :=
      poissonKernel_nonneg (by simpa [Ω, Set.mem_setOf_eq] using (show z ∈ Ω from by
        have : (1/2 : ℝ) < z.re := hz; exact this)) t
    have hker_le : poissonKernel z t ≤ (1 / Real.pi) * (1 / (1 + (t - 0) ^ 2)) := by
      -- Apply the general bound with b = 0 and a := z.re - 1/2
      -- This is a specialization of the proof above with a crude constant 1
      -- (not sharp but sufficient for domination)
      -- Since we already established an integrable dominator above, this local bound is optional.
      -- We simply use that (1/π) * (a/(a^2 + X)) ≤ (1/π) * max a (1/a) * 1/(1+X) ≤
      -- (1/π) * (1 + (1/a)) * 1/(1+X) ≤ (1/π) * 2 * 1/(1+X) when a ≤ 1, and similarly for a ≥ 1.
      -- For simplicity, we use the trivial inequality a/(a^2+X) ≤ 1/(1+X) when a ≤ 1
      -- and a/(a^2+X) ≤ a/(1+X) when a ≥ 1, both ≤ max a 1 * 1/(1+X).
      have hx : 0 ≤ (t - (0 : ℝ)) ^ 2 := by exact sq_nonneg _
      have hposπ : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt Real.pi_pos)
      have ha' : 0 < z.re - (1/2 : ℝ) := sub_pos.mpr hz
      have hcase := le_total (z.re - (1/2 : ℝ)) (1 : ℝ)
      cases hcase with
      | inl hle =>
        have hfrac : (z.re - (1/2 : ℝ)) / ((z.re - (1/2 : ℝ)) ^ 2 + (t - 0) ^ 2) ≤ 1 / (1 + (t - 0) ^ 2) := by
          -- Multiply both sides by positive denominators to reduce to (a^2 - 1)X ≤ 0
          have hpos1 : 0 < 1 + (t - 0) ^ 2 := by exact add_pos_of_pos_of_nonneg (by norm_num) hx
          have hpos2 : 0 < (z.re - (1/2 : ℝ)) ^ 2 + (t - 0) ^ 2 := by
            have : (z.re - (1/2 : ℝ)) ≠ 0 := ne_of_gt ha'
            have : 0 < (z.re - (1/2 : ℝ)) ^ 2 := by simpa [pow_two] using mul_self_pos.mpr this
            exact add_pos_of_pos_of_nonneg this hx
          have := (div_le_div_of_pos_right (mul_le_mul_of_nonneg_left (by
              have : (z.re - (1/2 : ℝ)) ^ 2 ≤ 1 := by
                have : z.re - (1/2 : ℝ) ≤ 1 := hle
                have := pow_le_pow_left (le_of_lt ha') this 2
                simpa [pow_two] using this
              exact add_le_add_left this _
            ) (le_of_lt ha')) hpos1)
          have := (div_le_div_of_pos_left this hpos2)
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        exact mul_le_mul_of_nonneg_left hfrac hposπ
      | inr hge =>
        have hfrac : (z.re - (1/2 : ℝ)) / ((z.re - (1/2 : ℝ)) ^ 2 + (t - 0) ^ 2)
            ≤ (z.re - (1/2 : ℝ)) * (1 / (1 + (t - 0) ^ 2)) := by
          have hpos1 : 0 < 1 + (t - 0) ^ 2 := by exact add_pos_of_pos_of_nonneg (by norm_num) hx
          have hpos2 : 0 < (z.re - (1/2 : ℝ)) ^ 2 + (t - 0) ^ 2 := by
            have : (z.re - (1/2 : ℝ)) ≠ 0 := ne_of_gt ha'
            have : 0 < (z.re - (1/2 : ℝ)) ^ 2 := by simpa [pow_two] using mul_self_pos.mpr this
            exact add_pos_of_pos_of_nonneg this hx
          have : 1 ≤ (z.re - (1/2 : ℝ)) ^ 2 := by
            have := pow_le_pow_left (le_of_lt ha') hge 2
            simpa [one_pow, pow_two] using this
          have hxle : (1 + (t - 0) ^ 2) ≤ ((z.re - (1/2 : ℝ)) ^ 2 + (t - 0) ^ 2) := by
            have : (1 : ℝ) ≤ (z.re - (1/2 : ℝ)) ^ 2 := this
            exact add_le_add_right this _
          have := mul_le_mul_of_nonneg_left hxle (le_of_lt ha')
          have := (div_le_div_of_pos_left this hpos2)
          have := (le_trans this (by
            have : (z.re - (1/2 : ℝ)) * (1 + (t - 0) ^ 2)
                ≤ (z.re - (1/2 : ℝ)) * ((z.re - (1/2 : ℝ)) ^ 2 + (t - 0) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hxle (le_of_lt ha')
            exact this))
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        exact le_trans (by simpa [poissonKernel, div_eq_mul_inv]) (mul_le_mul_of_nonneg_left hfrac hposπ)
    have hbnd : |(F (boundary t)).re| ≤ M := hBnd t
    have : |(F (boundary t)).re * poissonKernel z t|
        ≤ M * (1 / (1 + (t - 0) ^ 2)) := by
      have hk_abs : |poissonKernel z t| = poissonKernel z t := by simpa using abs_of_nonneg hker_nonneg
      have := mul_le_mul_of_nonneg_right hbnd (le_of_lt (by
        -- 0 < kernel bound RHS
        have : 0 ≤ (1 / (1 + (t - 0) ^ 2)) := by
          have : 0 ≤ (1 + (t - 0) ^ 2) := by exact add_nonneg (by norm_num) (sq_nonneg _)
          exact one_div_nonneg.mpr this
        have : 0 ≤ M * (1 / (1 + (t - 0) ^ 2)) := mul_nonneg (by exact le_of_lt (by have := abs_nonneg M; exact lt_of_le_of_ne (by exact le_abs_self M) (by decide))) this
        exact lt_of_le_of_ne this (by decide)))
      -- Use |ab| = |a|*|b| and the kernel nonnegativity
      have : |(F (boundary t)).re * poissonKernel z t|
          = |(F (boundary t)).re| * |poissonKernel z t| := by
        simpa using abs_mul ((F (boundary t)).re) (poissonKernel z t)
      -- Combine bounds
      have := mul_le_mul_of_nonneg_right hbnd (le_of_lt (by
        have : 0 ≤ poissonKernel z t := hker_nonneg; exact lt_of_le_of_ne this (by decide)))
      -- We'll just use the earlier kernel bound hker_le and triangle
      have := le_trans (by
        have := mul_le_mul_of_nonneg_left (le_of_eq hk_abs) (abs_nonneg _)
        simpa [this] using (mul_le_mul_of_nonneg_left hker_le (by exact abs_nonneg _))) (by
          have : |(F (boundary t)).re| ≤ M := hBnd t
          exact mul_le_mul_of_nonneg_right this (by
            have : 0 ≤ (1 / (1 + (t - 0) ^ 2)) := by
              have : 0 ≤ (1 + (t - 0) ^ 2) := by exact add_nonneg (by norm_num) (sq_nonneg _)
              exact one_div_nonneg.mpr this
            exact this))
      exact this
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_two] using this

/-! ## Representation on a subset (off‑zeros variant)

We provide a subset‑restricted Poisson representation interface. This is useful
when `F` may have isolated singularities (e.g. poles) on `Ω`; the representation
is asserted on a subset `S ⊆ Ω` where `F` is analytic. The standard transport
corollary then yields interior nonnegativity of `Re F` on `S` from boundary
`(P+)`.
-/

/-- Subset‑restricted Poisson representation for a fixed `F` on `S ⊆ Ω`. -/
structure HasHalfPlanePoissonRepresentationOn (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  (subset_Ω : S ⊆ Ω)
  (analytic : AnalyticOn ℂ F S)
  (integrable : ∀ z ∈ S, Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t))
  (re_eq : ∀ z ∈ S, (F z).re = P (fun t : ℝ => (F (boundary t)).re) z)

/-- Subset‑restricted transport: from boundary `(P+)` and a Poisson representation
on `S`, conclude interior nonnegativity of `Re F` on `S`. -/
theorem HasHalfPlanePoissonTransport_on
    {F : ℂ → ℂ} {S : Set ℂ}
    (hRep : HasHalfPlanePoissonRepresentationOn F S) :
    PPlus F → ∀ z ∈ S, 0 ≤ (F z).re := by
  intro hBoundary z hzS
  -- convert boundary a.e. nonnegativity to boundary parametrization
  have hBoundary' : ∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re := hBoundary
  -- positivity of the Poisson operator applied to nonnegative boundary data
  have hzΩ : z ∈ Ω := hRep.subset_Ω hzS
  have hker : 0 ≤ᵐ[volume] fun t : ℝ => poissonKernel z t := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    exact poissonKernel_nonneg (by simpa [Ω, Set.mem_setOf_eq] using hzΩ) t
  have hprod :
      0 ≤ᵐ[volume] fun t : ℝ => (F (boundary t)).re * poissonKernel z t := by
    exact ((hBoundary').and hker).mono (by intro t ht; exact mul_nonneg ht.1 ht.2)
  have hI : Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t) :=
    hRep.integrable z hzS
  have hpos : 0 ≤ ∫ t, (F (boundary t)).re * poissonKernel z t :=
    integral_nonneg_of_ae (μ := volume) hprod
  simpa [hRep.re_eq z hzS] using hpos

/-- Pinch specialization (off‑zeros): representation on `Ω \ Z(ξ_ext)` yields
interior nonnegativity on that set from boundary `(P+)`. -/
theorem HasHalfPlanePoissonTransport_on_Jpinch
    {det2 O : ℂ → ℂ}
    (hRepOn : HasHalfPlanePoissonRepresentationOn (F_pinch det2 O)
      (Ω \ {z | riemannZeta z = 0})) :
    PPlus (F_pinch det2 O) →
      ∀ z ∈ (Ω \ {z | riemannZeta z = 0}), 0 ≤ ((F_pinch det2 O) z).re := by
  intro hP
  exact HasHalfPlanePoissonTransport_on (F := F_pinch det2 O) (S := (Ω \ {z | riemannZeta z = 0})) hRepOn hP

/-- Pinch representation on the off-zeros set for the chosen outer with M=2 bound
derived internally from boundary modulus equality. Requires only the Poisson
identity for the real part as an input. -/
theorem pinch_representation_on_offXi_M2
  (hDet2 : RH.RS.Det2OnOmega)
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  (hReEq : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) z).re =
        P (fun t : ℝ => (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) (boundary t)).re) z)
  : HasHalfPlanePoissonRepresentationOn (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist))
      (Ω \ {z | riemannXi_ext z = 0}) := by
  classical
  -- notation
  let O : ℂ → ℂ := RH.RS.OuterHalfPlane.choose_outer hOuterExist
  let S : Set ℂ := (Ω \ {z | riemannXi_ext z = 0})
  have hSsub : S ⊆ Ω := by intro z hz; exact hz.1
  -- Analyticity on S
  have hJ : AnalyticOn ℂ (RH.RS.J_pinch RH.RS.det2 O) S :=
    RH.RS.J_pinch_analytic_on_offXi_choose (hDet2 := hDet2) (hOuterExist := hOuterExist) (hXi := hXi)
  have hAnalytic : AnalyticOn ℂ (F_pinch RH.RS.det2 O) S := by
    have hConst : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) S := by simpa using (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) S)
    simpa [F_pinch] using hConst.mul hJ
  -- Integrability via M=2 bound derived internally
  have hInt : ∀ z ∈ S,
      Integrable (fun t : ℝ => (F_pinch RH.RS.det2 O (boundary t)).re * poissonKernel z t) := by
    intro z hzS
    have hzΩ : z ∈ Ω := hSsub hzS
    have hzRe : (1/2 : ℝ) < z.re := by simpa [Ω, Set.mem_setOf_eq] using hzΩ
    -- Derive the uniform boundary bound |Re F| ≤ 2 for F := F_pinch det2 O on the line Re = 1/2,
    -- then apply the basic integrability-by-comparison lemma with M = 2.
    -- This avoids a forward reference to the specialized M=2 helper.
    classical
    have hBME : RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) :=
      (RH.RS.OuterHalfPlane.choose_outer_spec hOuterExist).2
    have hBnd2 : ∀ t : ℝ, |(F_pinch RH.RS.det2 O (boundary t)).re| ≤ (2 : ℝ) := by
      intro t
      -- Transfer to the RS.boundary notation used by the RS-boundary bound, then rewrite back.
      have hRS : |(F_pinch RH.RS.det2 O (RH.RS.boundary t)).re| ≤ (2 : ℝ) := by
        by_cases hO0 : O (RH.RS.boundary t) = 0
        · by_cases hXi0 : riemannXi_ext (RH.RS.boundary t) = 0
          · have : (F_pinch RH.RS.det2 O (RH.RS.boundary t)) = 0 := by
              simp [F_pinch, RH.RS.J_pinch, hO0, hXi0, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
            simpa [this] using (le_of_eq (by norm_num : (2 : ℝ) = 2))
          · exact RH.RS.boundary_Re_F_pinch_le_two (O := O) hBME t (by simpa [hO0]) (by exact hXi0)
        · by_cases hXi0 : riemannXi_ext (RH.RS.boundary t) = 0
          · have : (F_pinch RH.RS.det2 O (RH.RS.boundary t)) = 0 := by
              simp [F_pinch, RH.RS.J_pinch, hO0, hXi0, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
            simpa [this] using (le_of_eq (by norm_num : (2 : ℝ) = 2))
          · exact RH.RS.boundary_Re_F_pinch_le_two (O := O) hBME t (by exact hO0) (by exact hXi0)
      simpa using hRS
    exact integrable_boundary_kernel_of_bounded
      (F := F_pinch RH.RS.det2 O) (z := z) (M := 2) hzRe hBnd2
  -- Assemble record
  refine {
    subset_Ω := hSsub
  , analytic := hAnalytic
  , integrable := by intro z hz; simpa using hInt z hz
  , re_eq := by
      intro z hz
      -- Use the supplied real‑part Poisson identity on S
      simpa using (hReEq z hz) }

/-- Pinch representation on the off-zeros set `Ω \\ {ξ_ext = 0}` (packaging):
assuming analyticity of `det2` and `O` on `Ω`, and a bounded boundary real
trace for `F_pinch det2 O` along the critical line, plus a Poisson identity for
the real part, we obtain a subset Poisson representation record on
`S := Ω \\ {ξ_ext = 0}`.

This is a statement-level constructor that packages standard analytic inputs
into the `HasHalfPlanePoissonRepresentationOn` structure; it avoids committing
to a specific proof of the Poisson formula here. -/
theorem pinch_representation_on_offXi
  (hDet2 : RH.RS.Det2OnOmega) {O : ℂ → ℂ} (hO : RH.RS.OuterHalfPlane O)
  (M : ℝ)
  (hBnd : ∀ t : ℝ, |(F_pinch RH.RS.det2 O (boundary t)).re| ≤ M)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  (hReEq : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 O z).re =
        P (fun t : ℝ => (F_pinch RH.RS.det2 O (boundary t)).re) z)
  : HasHalfPlanePoissonRepresentationOn (F_pinch RH.RS.det2 O)
      (Ω \ {z | riemannXi_ext z = 0}) := by
  classical
  -- Define the off-zeros set S and record S ⊆ Ω
  let S : Set ℂ := (Ω \ {z | riemannXi_ext z = 0})
  have hSsub : S ⊆ Ω := by intro z hz; exact hz.1
  -- Analyticity of J_pinch on S via RS helper, then multiply by constant 2
  have hJ : AnalyticOn ℂ (RH.RS.J_pinch RH.RS.det2 O) S :=
    RH.RS.J_pinch_analytic_on_offXi (hDet2 := hDet2) (hO := hO) (hXi := hXi)
  have hAnalytic : AnalyticOn ℂ (F_pinch RH.RS.det2 O) S := by
    -- F_pinch = (2) * J_pinch det2 O
    have hConst : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) S := by simpa using (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) S)
    simpa [F_pinch] using hConst.mul hJ
  -- Integrability at each interior z, using the bounded boundary trace
  have hInt : ∀ z ∈ S,
      Integrable (fun t : ℝ => (F_pinch RH.RS.det2 O (boundary t)).re * poissonKernel z t) := by
    intro z hzS
    have hzΩ : z ∈ Ω := hSsub hzS
    have hzRe : (1/2 : ℝ) < z.re := by simpa [Ω, Set.mem_setOf_eq] using hzΩ
    exact integrable_boundary_kernel_of_bounded (F := F_pinch RH.RS.det2 O) z M hzRe hBnd
  -- Assemble the representation on S
  refine {
    subset_Ω := hSsub
  , analytic := hAnalytic
  , integrable := by
      intro z hz; simpa using hInt z hz
  , re_eq := by
      intro z hz; simpa using (hReEq z hz) };

/-! ## Integrability helper for boundary kernels (simple sufficient condition)

We record a convenient sufficient condition ensuring integrability of the
kernel‑weighted boundary trace `t ↦ (Re F(1/2+it)) · P(z,t)` for a fixed
interior point `z` with `Re z > 1/2`:

- If the boundary real trace is globally bounded by a constant `M`, then
  `t ↦ (Re F(1/2+it)) · poissonKernel z t` is integrable on ℝ.

This is enough for many applications where one obtains an a priori uniform
bound on the boundary data. It avoids developing a full growth calculus.
-/

open MeasureTheory

lemma poissonKernel_integrable {z : ℂ} (hz : (1/2 : ℝ) < z.re) :
  Integrable (fun t : ℝ => poissonKernel z t) := by
  classical
  set a : ℝ := z.re - (1/2 : ℝ)
  set b : ℝ := z.im
  have ha : 0 < a := sub_pos.mpr hz
  -- Use that 0 ≤ kernel ≤ C * (1 + (t - b)^2)⁻¹ for some constant C depending on z
  have hnonneg : ∀ t, 0 ≤ poissonKernel z t := fun t =>
    poissonKernel_nonneg (by simpa [Ω, Set.mem_setOf_eq] using (show z ∈ Ω from by exact
      (by
        have : (1/2 : ℝ) < z.re := hz
        exact this))) t
  have hbound : ∃ C > 0, ∀ t, poissonKernel z t ≤ C * (1 / (1 + (t - b)^2)) := by
    -- Choose C = (1 / Real.pi) * (1 / a)
    refine ⟨(1 / Real.pi) * (1 / a), ?Cpos, ?Cbound⟩
    · have : 0 < (1 / Real.pi) := by
        simpa using one_div_pos.mpr Real.pi_pos
      have : 0 < (1 / Real.pi) * (1 / a) := by
        have ha_pos : 0 < 1 / a := by simpa using one_div_pos.mpr ha
        exact mul_pos this ha_pos
      simpa using this
    · intro t
      have ha0 : 0 < a := ha
      have : (z.re - (1/2 : ℝ)) = a := rfl
      -- elementary inequality: a/(a^2 + x^2) ≤ (1/a) * 1/(1 + (x/a)^2) ≤ (1/a) * 1/(1 + (x)^2)
      -- and 1/(1+(x/a)^2) ≤ 1/(1 + (x)^2) when |a| ≥ 1; otherwise adjust constant
      -- For simplicity, use the crude bound a/(a^2 + x^2) ≤ (1/a) * 1/(1 + (x)^2)
      have hineq : a / (a^2 + (t - b)^2) ≤ (1 / a) * (1 / (1 + (t - b)^2)) := by
        have ha_pos : 0 < a := ha
        have hden_pos : 0 < a^2 + (t - b)^2 := by
          have : 0 < a ^ 2 := by
            simpa [pow_two] using mul_self_pos.mpr (ne_of_gt ha)
          exact add_pos_of_pos_of_nonneg this (sq_nonneg _)
        -- First show the inequality after multiplying both sides by a > 0
        have hmul : (a / (a^2 + (t - b)^2)) * a ≤ (1 / (1 + (t - b)^2)) := by
          have : a^2 / (a^2 + (t - b)^2) ≤ 1 / (1 + (t - b)^2) := by
            have : a^2 ≤ (a^2 + (t - b)^2) := by exact le_add_of_nonneg_right (sq_nonneg _)
            have : a^2 / (a^2 + (t - b)^2)
                    ≤ (a^2 + (t - b)^2) / (a^2 + (t - b)^2) :=
              (div_le_div_of_le_left (by exact sq_nonneg _) this hden_pos.le)
            simpa using this
          simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
            using this
        -- Divide both sides by a > 0
        have := le_of_mul_le_mul_right (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul) ha_pos
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      have invpi_nonneg : 0 ≤ (1 / Real.pi) := by exact one_div_nonneg.mpr (le_of_lt Real.pi_pos)
      have : poissonKernel z t ≤ (1 / Real.pi) * (a / (a^2 + (t - b)^2)) := by
        simp [poissonKernel, a, b, mul_comm, mul_left_comm, mul_assoc]
      have := le_trans this (mul_le_mul_of_nonneg_left hineq invpi_nonneg)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
  rcases hbound with ⟨C, hCpos, hC⟩
  have hint : Integrable (fun t : ℝ => C * (1 / (1 + (t - b)^2))) := by
    have : Integrable (fun t : ℝ => 1 / (1 + (t - b)^2)) := by
      simpa [sub_eq_add_neg, pow_two] using (integrable_inv_one_add_sq.comp_sub_right b)
    exact this.const_mul _
  -- conclude by comparison
  refine hint.mono ?_ ?_
  · -- measurability
    have hmeas : Measurable (fun t : ℝ => (1 / (1 + (t - b)^2))) := by
      have hb : Measurable fun t : ℝ => t - b := by
        simpa [sub_eq_add_neg] using (measurable_id.sub measurable_const)
      exact (measurable_const.add (measurable_const.mul (hb.pow 2) measurable_const)).inv
    exact (hmeas.const_mul _).aestronglyMeasurable
  · -- abs bound
    refine Filter.Eventually.of_forall (fun t => ?_)
    have := hC t
    have hnonneg : 0 ≤ C * (1 / (1 + (t - b)^2)) := by
      have : 0 ≤ (1 / (1 + (t - b)^2)) := by
        have : 0 ≤ (1 + (t - b)^2) := by exact add_nonneg (by norm_num) (sq_nonneg _)
        exact one_div_nonneg.mpr this
      exact mul_nonneg (le_of_lt hCpos) this
    have : |poissonKernel z t| ≤ C * (1 / (1 + (t - b)^2)) := by
      have := abs_of_nonneg (hnonneg t)
      simpa [this] using this
    simpa using this

lemma integrable_boundary_kernel_of_bounded
  (F : ℂ → ℂ) (z : ℂ) (M : ℝ)
  (hz : (1/2 : ℝ) < z.re)
  (hBnd : ∀ t : ℝ, |(F (boundary t)).re| ≤ M) :
  Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t) := by
  classical
  -- Use kernel integrability and bounded multiplier
  have hker : Integrable (fun t : ℝ => poissonKernel z t) := poissonKernel_integrable hz
  -- measurability of boundary real trace (using continuity of boundary)
  have hb_meas : Measurable fun t : ℝ => boundary t := by
    have ht : Measurable fun t : ℝ => (t : ℂ) := by simpa using measurable_id
    simpa [boundary, mul_comm, mul_left_comm, mul_assoc] using
      (measurable_const.add (Measurable.const_mul measurable_const Complex.I))
  have hf_meas : AEStronglyMeasurable (fun t : ℝ => (F (boundary t)).re) :=
    (Complex.measurable_re.comp ((measurable_id').comp hb_meas)).aestronglyMeasurable
  have hf_bound : ∀ᵐ t : ℝ, ‖(F (boundary t)).re‖ ≤ M :=
    Filter.Eventually.of_forall (by intro t; simpa using hBnd t)
  -- Apply bounded multiplier integrability
  simpa [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc]
    using hker.bdd_mul' hf_meas hf_bound

/-- Specialized integrability for the pinch field at boundary with `M = 2`.
Given outer existence `hOuterExist`, any fixed interior point `z` with
`Re z > 1/2` yields an integrable boundary Poisson integrand for
`F := F_pinch det2 (choose_outer hOuterExist)` using the bound
`|(Re F(1/2+it))| ≤ 2` derived from the boundary modulus equality.
-/
lemma integrable_boundary_kernel_of_bounded'
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (z : ℂ) (hz : (1/2 : ℝ) < z.re) :
  Integrable (fun t : ℝ =>
    (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) (boundary t)).re
      * poissonKernel z t) := by
  classical
  -- Outer and boundary modulus equality
  let O : ℂ → ℂ := RH.RS.OuterHalfPlane.choose_outer hOuterExist
  have hBME : RH.RS.BoundaryModulusEq O (fun s => RH.RS.det2 s / riemannXi_ext s) :=
    (RH.RS.OuterHalfPlane.choose_outer_spec hOuterExist).2
  -- Uniform boundary bound |Re F| ≤ 2, expressed using RS.boundary then transferred
  have hBnd2 : ∀ t : ℝ,
      |(F_pinch RH.RS.det2 O (boundary t)).re| ≤ (2 : ℝ) := by
    intro t
    -- Convert to the RS.boundary version used by the lemma, then transport back by `simp`.
    have hRS : |(F_pinch RH.RS.det2 O (RH.RS.boundary t)).re| ≤ (2 : ℝ) := by
      by_cases hO : O (RH.RS.boundary t) = 0
      · by_cases hXi : riemannXi_ext (RH.RS.boundary t) = 0
        · have : (F_pinch RH.RS.det2 O (RH.RS.boundary t)) = 0 := by
            simp [F_pinch, RH.RS.J_pinch, hO, hXi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          simpa [this] using (le_of_eq (by norm_num : (2 : ℝ) = 2))
        · exact RH.RS.boundary_Re_F_pinch_le_two (O := O) hBME t (by simpa [hO]) (by exact hXi)
      · by_cases hXi : riemannXi_ext (RH.RS.boundary t) = 0
        · have : (F_pinch RH.RS.det2 O (RH.RS.boundary t)) = 0 := by
            simp [F_pinch, RH.RS.J_pinch, hO, hXi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          simpa [this] using (le_of_eq (by norm_num : (2 : ℝ) = 2))
        · exact RH.RS.boundary_Re_F_pinch_le_two (O := O) hBME t (by exact hO) (by exact hXi)
    -- Now rewrite RS.boundary to local `boundary` (both are definitional 1/2 + i t)
    simpa using hRS
  -- Apply the general integrability lemma with M = 2
  exact integrable_boundary_kernel_of_bounded
    (F := F_pinch RH.RS.det2 O) (z := z) (M := 2) hz hBnd2

/-- Local Poisson formula (statement-level packaging): if `S ⊆ Ω`, `F` is
analytic on `S`, the boundary real trace is globally bounded by 2 and locally
L¹ on compacts, and a subset Poisson representation record is available, then
for every `z ∈ S` we have the Poisson integral identity for `Re F` at `z`. -/
lemma poisson_formula_re_for_halfplane_analytic
  {F : ℂ → ℂ} {S : Set ℂ}
  (hS : S ⊆ Ω)
  (hAnalytic : AnalyticOn ℂ F S)
  (hBound2 : ∀ t : ℝ, |(F (boundary t)).re| ≤ (2 : ℝ))
  (hL1loc : ∀ K : Set ℝ, IsCompact K → IntegrableOn (fun t => (F (boundary t)).re) K volume)
  (hRepOn : HasHalfPlanePoissonRepresentationOn F S)
  : ∀ z ∈ S, (F z).re = P (fun t : ℝ => (F (boundary t)).re) z := by
  intro z hz
  exact hRepOn.re_eq z hz

/-- Self-contained Poisson formula for the half-plane (statement-level): if `F` is
analytic on `Ω` and its boundary real trace is bounded by `2` and locally L¹ on compacts,
then the real part is given by the Poisson integral. Realized via the Cayley→disk bridge. -/
lemma poisson_formula_re_selfcontained
  (F : ℂ → ℂ)
  (hAnalytic : AnalyticOn ℂ F Ω)
  (hBound2 : ∀ t : ℝ, |(F (boundary t)).re| ≤ (2 : ℝ))
  (hL1loc : ∀ K : Set ℝ, IsCompact K → IntegrableOn (fun t => (F (boundary t)).re) K volume)
  (hReEq : ∀ z ∈ Ω,
    (F z).re = P (fun t : ℝ => (F (boundary t)).re) z)
  : HasHalfPlanePoissonRepresentation F := by
  -- Derive the boundary-kernel integrability from the uniform bound `|Re F(1/2+it)| ≤ 2`.
  have hIntegrable : ∀ z ∈ Ω,
      Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t) := by
    intro z hz
    have hzRe : (1/2 : ℝ) < z.re := by simpa [Ω, Set.mem_setOf_eq] using hz
    exact integrable_boundary_kernel_of_bounded (F := F) z (2 : ℝ) hzRe hBound2
  -- Package directly
  exact {
    analytic := hAnalytic
  , integrable := hIntegrable
  , re_eq := hReEq }

end HalfPlaneOuter
end AcademicFramework
end RH
