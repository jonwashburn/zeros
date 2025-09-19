import rh.academic_framework.DiskHardy
import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Analysis.Trigonometry.Trigonometric
import rh.academic_framework.HalfPlaneOuter

namespace RH
namespace AcademicFramework
namespace CayleyAdapters

open Complex RH.AcademicFramework
open scoped Real

/-- Cayley map from the right half-plane Ω = {Re s > 1/2} to the unit disk. -/
@[simp] def toDisk (s : ℂ) : ℂ := (s - (1 : ℂ)) / s

/-- Inverse Cayley map from the unit disk to the right half-plane Ω. -/
@[simp] def toHalf (w : ℂ) : ℂ := 1 / (1 - w)

/-- Boundary parametrization transport under Cayley: on Re s=1/2, the image lies on ∂𝔻. -/
@[simp] def boundaryToDisk (t : ℝ) : ℂ := toDisk (HalfPlaneOuter.boundary t)

/-! ## Geometry facts for the Cayley transform -/

lemma map_Ω_to_unitDisk {z : ℂ}
  (hz : z ∈ HalfPlaneOuter.Ω) : toDisk z ∈ DiskHardy.unitDisk := by
  -- Re z > 1/2 ⇒ |z-1| < |z| ⇒ |(z-1)/z| < 1
  have hzRe : (1/2 : ℝ) < z.re := by simpa [HalfPlaneOuter.Ω, Set.mem_setOf_eq] using hz
  have hzNe : z ≠ 0 := by
    intro h; have hre := congrArg Complex.re h; simpa using (lt_irrefl_of_le_of_lt (by simpa [h] : (0:ℝ) = z.re) hzRe)
  have hsq : (Complex.abs (z - 1))^2 = (Complex.abs z)^2 - 2 * z.re + 1 := by
    simpa using Complex.abs.sub_sq z (1 : ℂ)
  have hlt : Complex.abs (z - 1) < Complex.abs z := by
    -- Compare squares using Re z > 1/2
    have hlt_sq : (Complex.abs (z - 1))^2 < (Complex.abs z)^2 := by
      have : - 2 * z.re + 1 < 0 := by linarith
      simpa [hsq] using this
    exact (sq_lt_sq).1 hlt_sq
  have : Complex.abs (toDisk z) = Complex.abs (z - 1) / Complex.abs z := by
    simp [toDisk, Complex.abs_div, hzNe]
  have hlt' : Complex.abs (toDisk z) < 1 := by
    have hzpos : 0 < Complex.abs z := Complex.abs.pos_iff.mpr hzNe
    simpa [this] using (div_lt_one_of_lt hlt hzpos)
  simpa [DiskHardy.unitDisk, Set.mem_setOf_eq] using hlt'

lemma boundary_maps_to_unitCircle (t : ℝ) : Complex.abs (boundaryToDisk t) = 1 := by
  -- |(s-1)/s| = 1 when Re s = 1/2 with s = 1/2 + i t
  have hrepr : HalfPlaneOuter.boundary t = Complex.mk (1/2) t := by
    simpa [HalfPlaneOuter.boundary_mk_eq]
  have hne : HalfPlaneOuter.boundary t ≠ 0 := by
    intro h; have hre := congrArg Complex.re h; simpa [hrepr] using hre
  have h1 : Complex.abs (HalfPlaneOuter.boundary t - 1)
            = Real.sqrt (((- (1/2 : ℝ))^2) + t^2) := by
    have : HalfPlaneOuter.boundary t - 1 = Complex.mk (- (1/2 : ℝ)) t := by
      simp [hrepr, sub_eq_add_neg]
    simpa [this, Complex.abs_def]
  have h2 : Complex.abs (HalfPlaneOuter.boundary t)
            = Real.sqrt (((1/2 : ℝ)^2) + t^2) := by
    simpa [hrepr, Complex.abs_def]
  have : Complex.abs (boundaryToDisk t) = Complex.abs (HalfPlaneOuter.boundary t - 1) / Complex.abs (HalfPlaneOuter.boundary t) := by
    simp [boundaryToDisk, toDisk, Complex.abs_div, hne]
  have : Complex.abs (boundaryToDisk t)
      = Real.sqrt ((1/2 : ℝ)^2 + t^2) / Real.sqrt ((1/2 : ℝ)^2 + t^2) := by
    simpa [this, h1, h2, pow_two, neg_sq] using rfl
  simpa using (div_self (by
    have : 0 < Real.sqrt ((1/2 : ℝ)^2 + t^2) := by
      have : 0 < ((1/2 : ℝ)^2 + t^2) := by
        have : (0 : ℝ) ≤ t^2 := sq_nonneg _
        have : 0 < (1/2 : ℝ)^2 + t^2 := by
          have : (0 : ℝ) < (1/2 : ℝ)^2 := by norm_num
          exact add_pos_of_pos_of_nonneg this (sq_nonneg _)
        simpa
      simpa using Real.sqrt_pos.mpr this
    exact ne_of_gt this))

/-!
## Change-of-variables helpers for Cayley

We record algebraic identities used in the half‑plane↔disk Poisson kernel
change‑of‑variables calculation.
-/

open Complex

/-- Closed form for `boundaryToDisk t` as a rational expression in `t`. -/
lemma boundaryToDisk_closed_form (t : ℝ) :
  boundaryToDisk t =
    ((t : ℂ)^2 - (1/4 : ℂ) + Complex.I * (t : ℂ)) / ((t : ℂ)^2 + (1/4 : ℂ)) := by
  -- boundaryToDisk t = toDisk (1/2 + i t) = ((-1/2 + i t) / (1/2 + i t))
  simp [boundaryToDisk, toDisk, HalfPlaneOuter.boundary,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  -- rewrite (a+bi) algebraically into the rational form
  ring

/-- Absolute value of `toDisk z` as the ratio `|z−1|/|z|` (valid for `z ≠ 0`). -/
lemma abs_toDisk (z : ℂ) (hz : z ≠ 0) :
  Complex.abs (toDisk z) = Complex.abs (z - 1) / Complex.abs z := by
  simp [toDisk, Complex.abs_div, hz]

/-- `1 - ‖toDisk z‖^2` in terms of `z` (valid for `z ≠ 0`). -/
lemma one_minus_absSq_toDisk (z : ℂ) (hz : z ≠ 0) :
  1 - (Complex.abs (toDisk z))^2 =
    ((2 : ℝ) * z.re - 1) / (Complex.abs z)^2 := by
  have h : Complex.abs (toDisk z) = Complex.abs (z - 1) / Complex.abs z :=
    abs_toDisk z hz
  -- 1 - (|z-1|/|z|)^2 = (|z|^2 - |z-1|^2) / |z|^2
  have : 1 - (Complex.abs (z - 1) / Complex.abs z)^2
        = ((Complex.abs z)^2 - (Complex.abs (z - 1))^2) / (Complex.abs z)^2 := by
    field_simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  -- |z|^2 - |z-1|^2 = 2 Re z - 1
  have hdiff : (Complex.abs z)^2 - (Complex.abs (z - 1))^2
      = (2 : ℝ) * z.re - 1 := by
    -- Expand |z-1|^2 = |z|^2 - 2 Re z + 1
    have hsq : (Complex.abs (z - 1))^2 = (Complex.abs z)^2 - 2 * z.re + 1 := by
      simpa using Complex.abs.sub_sq z (1 : ℂ)
    linear_combination hsq
  simpa [h, this, hdiff]

/-- The boundary point `s = 1/2 + i t` is never zero. -/
lemma boundary_ne_zero (t : ℝ) : HalfPlaneOuter.boundary t ≠ 0 := by
  intro h
  have : (HalfPlaneOuter.boundary t).re = (0 : ℝ) := by simpa [h]
  simp [HalfPlaneOuter.boundary] at this

/-- Difference of Cayley images in terms of original points. Requires both nonzero. -/
lemma toDisk_sub (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
  toDisk u - toDisk v = (u - v) / (u * v) := by
  -- toDisk w = 1 - 1/w
  simp [toDisk, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc, inv_mul_eq_iff_eq_mul₀ hu, inv_mul_eq_iff_eq_mul₀ hv]
  field_simp [hu, hv]

/-- Absolute value of the boundary/disk difference in terms of original points. -/
lemma abs_boundaryToDisk_sub_toDisk (t : ℝ) (z : ℂ) (hz : z ≠ 0) :
  Complex.abs (boundaryToDisk t - toDisk z)
    = Complex.abs (HalfPlaneOuter.boundary t - z)
        / (Complex.abs (HalfPlaneOuter.boundary t) * Complex.abs z) := by
  have hs0 : HalfPlaneOuter.boundary t ≠ 0 := boundary_ne_zero t
  have hdiff : boundaryToDisk t - toDisk z
      = (HalfPlaneOuter.boundary t - z) / (HalfPlaneOuter.boundary t * z) := by
    -- use the general difference formula specialized to u=s, v=z
    simpa [boundaryToDisk] using toDisk_sub (u := HalfPlaneOuter.boundary t) (v := z) hs0 hz
  -- take absolute values
  simpa [hdiff, Complex.abs_div, Complex.abs_mul]

/-- Core density identity: rewrite `(1 - |w|^2)/|ξ − w|^2` in half‑plane variables. -/
lemma density_ratio_boundary (z : ℂ) (hzΩ : z ∈ HalfPlaneOuter.Ω) (t : ℝ) :
  let w := toDisk z
  let ξ := boundaryToDisk t
  (1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2
    = ((2 : ℝ) * z.re - 1) * (Complex.abs (HalfPlaneOuter.boundary t))^2
        / (Complex.abs (HalfPlaneOuter.boundary t - z))^2 := by
  classical
  intro w ξ
  have hz0 : z ≠ 0 := by
    -- Re z > 1/2 ⇒ z ≠ 0
    intro h; have : (0 : ℝ) < (1/2 : ℝ) := by norm_num
    have hRe : (1/2 : ℝ) < z.re := by simpa [HalfPlaneOuter.Ω, Set.mem_setOf_eq] using hzΩ
    exact (lt_irrefl _ (lt_trans this hRe))
  have hs0 : HalfPlaneOuter.boundary t ≠ 0 := boundary_ne_zero t
  -- Evaluate denominator via difference identity
  have hDen : (Complex.abs (ξ - w))^2
      = (Complex.abs (HalfPlaneOuter.boundary t - z))^2
          / ((Complex.abs (HalfPlaneOuter.boundary t))^2 * (Complex.abs z)^2) := by
    have := abs_boundaryToDisk_sub_toDisk t z hz0
    -- square both sides
    have : (Complex.abs (boundaryToDisk t - toDisk z))^2
        = (Complex.abs (HalfPlaneOuter.boundary t - z))^2
            / ((Complex.abs (HalfPlaneOuter.boundary t) * Complex.abs z)^2) := by
      simpa [pow_two, mul_pow] using congrArg (fun r => r^2) this
    -- simplify (ab)^2 = a^2 b^2
    simpa [ξ, w, pow_two, mul_pow] using this
  -- Evaluate numerator via one_minus_absSq_toDisk
  have hNum : 1 - (Complex.abs w)^2
      = ((2 : ℝ) * z.re - 1) / (Complex.abs z)^2 := by
    simpa [w] using one_minus_absSq_toDisk z hz0
  -- assemble the ratio
  have hPos : (Complex.abs (HalfPlaneOuter.boundary t) * Complex.abs z)^2
      = (Complex.abs (HalfPlaneOuter.boundary t))^2 * (Complex.abs z)^2 := by
    ring
  -- compute: (A/|z|^2) / (B/(|s|^2|z|^2)) = A*|s|^2/B
  have : (1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2
      = (((2 : ℝ) * z.re - 1) / (Complex.abs z)^2)
          / ((Complex.abs (HalfPlaneOuter.boundary t - z))^2
              / ((Complex.abs (HalfPlaneOuter.boundary t))^2 * (Complex.abs z)^2)) := by
    simpa [hNum, hDen]
  -- finish with field algebra
  field_simp [this]

/-- Real parameters `a(z) = Re z − 1/2` and `b(z) = Im z` for change-of-variables. -/
def a (z : ℂ) : ℝ := z.re - (1/2 : ℝ)
def b (z : ℂ) : ℝ := z.im

lemma a_pos_of_mem_Ω {z : ℂ} (hz : z ∈ HalfPlaneOuter.Ω) : 0 < a z := by
  simpa [a, HalfPlaneOuter.Ω, Set.mem_setOf_eq] using (hz : (1/2 : ℝ) < z.re)

/-- Angle map for a fixed interior point `z`: θ_z(t) := 2 · arctan((t − b)/a). -/
def theta_of (z : ℂ) (t : ℝ) : ℝ := 2 * Real.arctan ((t - b z) / (a z))

/-- Derivative of the angle map: dθ/dt = 2a / ((t − b)^2 + a^2). -/
lemma hasDerivAt_theta_of {z : ℂ} (hz : z ∈ HalfPlaneOuter.Ω) (t : ℝ) :
  HasDerivAt (fun t => theta_of z t)
    (2 * (a z) / ((t - b z)^2 + (a z)^2)) t := by
  -- θ(t) = 2 * arctan(u(t)), u(t) = (t - b)/a
  have ha_ne : (a z) ≠ 0 := ne_of_gt (a_pos_of_mem_Ω hz)
  -- derivative of u(t) = (t - b)/a is 1/a
  have hDu : HasDerivAt (fun t => (t - b z) / (a z)) ((1 : ℝ) / (a z)) t := by
    simpa [one_div, a, b] using (HasDerivAt.const_sub t (b z)).div_const (a z)
  -- derivative of arctan is 1 / (1 + u^2)
  have hDatan : HasDerivAt (fun u => Real.arctan u)
      (1 / (1 + ((t - b z) / (a z))^2)) ((t - b z) / (a z)) :=
    Real.hasDerivAt_arctan _
  -- chain rule and scale by 2
  have hChain : HasDerivAt (fun t => Real.arctan ((t - b z) / (a z)))
      (((1 : ℝ) / (a z)) * (1 / (1 + ((t - b z) / (a z))^2))) t :=
    hDatan.comp t hDu
  have hSimpl : ((1 : ℝ) / (a z)) * (1 / (1 + ((t - b z) / (a z))^2))
      = (a z) / ((t - b z)^2 + (a z)^2) := by
    -- (1/a) * 1 / (1 + ((t-b)/a)^2) = a / ((t-b)^2 + a^2)
    field_simp [pow_two, mul_comm, mul_left_comm, mul_assoc, ha_ne]
  have hDer : HasDerivAt (fun t => Real.arctan ((t - b z) / (a z)))
      ((a z) / ((t - b z)^2 + (a z)^2)) t := by
    simpa [hSimpl]
      using hChain
  simpa [theta_of, two_mul] using hDer.const_mul (2 : ℝ)

/-- z‑independent boundary angle: θ₀(t) := π − 2 arctan(2t), so that
`boundaryToDisk t = DiskHardy.boundary (θ₀ t)`. -/
def theta0 (t : ℝ) : ℝ := Real.pi - 2 * Real.arctan (2 * t)

/-- Regularity: derivative of θ₀ is `dθ₀/dt = - 4 / (1 + 4 t^2)`. -/
lemma hasDerivAt_theta0 (t : ℝ) :
  HasDerivAt theta0 (-(4 : ℝ) / (1 + 4 * t^2)) t := by
  -- θ₀(t) = π − 2 * arctan (2t)
  have hDu : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) t := by
    simpa using (hasDerivAt_id' t).const_mul (2 : ℝ)
  have hDatan : HasDerivAt (fun u : ℝ => Real.arctan u) (1 / (1 + (2 * t)^2)) (2 * t) := by
    simpa using Real.hasDerivAt_arctan (2 * t)
  have hChain : HasDerivAt (fun t : ℝ => Real.arctan (2 * t))
      ((2 : ℝ) * (1 / (1 + (2 * t)^2))) t :=
    hDatan.comp t hDu
  have hSimp : (2 : ℝ) * (1 / (1 + (2 * t)^2)) = 4 / (1 + 4 * t^2) := by
    field_simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hDer : HasDerivAt (fun t : ℝ => Real.arctan (2 * t)) (4 / (1 + 4 * t^2)) t := by
    simpa [hSimp] using hChain
  -- Combine with scaling by -2 and addition of constant π
  have hMain : HasDerivAt (fun t : ℝ => - 2 * Real.arctan (2 * t)) (-(8 : ℝ) / (1 + 4 * t^2)) t := by
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hDer.const_mul (-2 : ℝ)
  -- final scaling: -(8)/(...) / 2 = -(4)/(...) since θ₀ = π + ( -2 * arctan(2t) )
  simpa [theta0, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul]
    using hMain

/-- Continuity of θ₀. -/
lemma continuous_theta0 : Continuous theta0 := by
  -- built from continuous arctan and polynomial maps
  refine Continuous.sub ?h1 ?h2
  · exact continuous_const
  · exact (continuous_const.mul (Real.continuous_arctan.comp (continuous_const.mul continuous_id))).mul continuous_const

/-- Measurability of θ₀. -/
lemma measurable_theta0 : Measurable theta0 :=
  (continuous_theta0.measurable)

/-- Trig identities: cos(2 arctan u) and sin(2 arctan u). -/
lemma cos_double_arctan (u : ℝ) :
  Real.cos (2 * Real.arctan u) = (1 - u^2) / (1 + u^2) := by
  -- cos(2x) = cos^2 x - sin^2 x; use cos(arctan u) and sin(arctan u)
  have hcos : Real.cos (Real.arctan u) = 1 / Real.sqrt (1 + u^2) := Real.cos_arctan _
  have hsin : Real.sin (Real.arctan u) = u / Real.sqrt (1 + u^2) := Real.sin_arctan _
  have hcos2 : (Real.cos (Real.arctan u))^2 = 1 / (1 + u^2) := by
    simpa [pow_two] using by
      have := congrArg (fun x => x^2) hcos
      simpa [pow_two, one_div] using this
  have hsin2 : (Real.sin (Real.arctan u))^2 = u^2 / (1 + u^2) := by
    simpa [pow_two] using by
      have := congrArg (fun x => x^2) hsin
      simpa [pow_two, one_div] using this
  have hcos2' : Real.cos (2 * Real.arctan u) =
      (Real.cos (Real.arctan u))^2 - (Real.sin (Real.arctan u))^2 := by
    have := Real.cos_two_mul (Real.arctan u)
    simpa [two_mul] using this
  simpa [hcos2, hsin2] using hcos2'

lemma sin_double_arctan (u : ℝ) :
  Real.sin (2 * Real.arctan u) = (2 * u) / (1 + u^2) := by
  -- sin(2x) = 2 sin x cos x; use cos/sin of arctan
  have hcos : Real.cos (Real.arctan u) = 1 / Real.sqrt (1 + u^2) := Real.cos_arctan _
  have hsin : Real.sin (Real.arctan u) = u / Real.sqrt (1 + u^2) := Real.sin_arctan _
  have hsin2 : Real.sin (2 * Real.arctan u)
      = 2 * Real.sin (Real.arctan u) * Real.cos (Real.arctan u) := by
    have := Real.sin_two_mul (Real.arctan u)
    simpa [two_mul] using this
  simpa [hsin, hcos, one_div, pow_two, mul_comm, mul_left_comm, mul_assoc]
    using hsin2

/-- Boundary angle equality (statement): the Cayley image of the half‑plane
boundary at height `t` is the unit‑circle point at angle `θ₀(t)`.
Proof proceeds by explicit trigonometric evaluation of `exp(iθ₀)` and the
closed form `boundaryToDisk_closed_form`.
This proof will be completed by expanding `Complex.exp (I θ)` and
double/half‑angle formulas. -/
theorem boundaryToDisk_eq_boundary_theta0 (t : ℝ) :
  boundaryToDisk t = DiskHardy.boundary (theta0 t) := by
  -- boundaryToDisk has a closed rational form
  have hrat := boundaryToDisk_closed_form t
  -- Trig evaluation for θ₀(t) := π − 2 arctan(2t)
  have hcos0 : Real.cos (theta0 t) = (4 * t^2 - 1) / (1 + 4 * t^2) := by
    have : Real.cos (Real.pi - 2 * Real.arctan (2 * t))
        = - Real.cos (2 * Real.arctan (2 * t)) := by
      simpa [theta0, two_mul] using Real.cos_pi_sub (2 * Real.arctan (2 * t))
    have hcos2 := cos_double_arctan (2 * t)
    simpa [theta0, two_mul, hcos2, mul_pow, pow_two, sub_eq_add_neg, add_comm, add_left_comm,
           add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hsin0 : Real.sin (theta0 t) = (4 * t) / (1 + 4 * t^2) := by
    have : Real.sin (Real.pi - 2 * Real.arctan (2 * t))
        = Real.sin (2 * Real.arctan (2 * t)) := by
      simpa [theta0, two_mul] using Real.sin_pi_sub (2 * Real.arctan (2 * t))
    have hsin2 := sin_double_arctan (2 * t)
    simpa [theta0, two_mul, hsin2, mul_pow, pow_two, sub_eq_add_neg, add_comm, add_left_comm,
           add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using this
  -- Rewrite the unit-circle boundary via cos/sin
  have hExp : DiskHardy.boundary (theta0 t)
      = ((4 * (t:ℝ)^2 - 1 : ℝ) + Complex.I * (4 * t)) / (1 + 4 * t^2) := by
    -- exp(iθ) = cos θ + i sin θ
    have : Complex.exp (Complex.I * (theta0 t))
        = Complex.ofReal (Real.cos (theta0 t)) + Complex.I * Complex.ofReal (Real.sin (theta0 t)) := by
      simpa using Complex.exp_mul_I (theta0 t)
    -- convert to a single fraction
    simp [DiskHardy.boundary, this, hcos0, hsin0, Complex.ofReal_div, Complex.ofReal_mul,
          Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one,
          Complex.ofReal_bit0, Complex.ofReal_bit1, Complex.ofReal_mul, mul_comm, mul_left_comm,
          mul_assoc, add_comm, add_left_comm, add_assoc, two_mul, sub_eq_add_neg, pow_two]
  -- Also rewrite the rational form to the same denominator to compare
  have hrat' : boundaryToDisk t
      = ((4 * (t:ℝ)^2 - 1 : ℝ) + Complex.I * (4 * t)) / (1 + 4 * t^2) := by
    -- boundaryToDisk t = ((t^2 - 1/4) + i t) / (t^2 + 1/4)
    -- multiply numerator and denominator by 4 using (a/b) = (4a)/(4b)
    have h4nz : (4 : ℂ) ≠ 0 := by norm_num
    have hscaled :
        ((t : ℂ)^2 - (1/4 : ℂ) + Complex.I * (t : ℂ)) / ((t : ℂ)^2 + (1/4 : ℂ))
        = ((4 : ℂ) * ((t : ℂ)^2 - (1/4 : ℂ) + Complex.I * (t : ℂ)))
            / ((4 : ℂ) * ((t : ℂ)^2 + (1/4 : ℂ))) := by
      -- (a/b) = (c*a)/(c*b)
      simpa using (mul_div_mul_left
        (((t : ℂ)^2 - (1/4 : ℂ) + Complex.I * (t : ℂ)))
        (((t : ℂ)^2 + (1/4 : ℂ))) (4 : ℂ)).symm
    have hnum : (4 : ℂ) * ((t : ℂ)^2 - (1/4 : ℂ) + Complex.I * (t : ℂ))
        = (((4 : ℂ) * (t : ℂ)^2 - 1) + Complex.I * ((4 : ℂ) * (t : ℂ))) := by
      ring
    have hden : (4 : ℂ) * ((t : ℂ)^2 + (1/4 : ℂ))
        = ((4 : ℂ) * (t : ℂ)^2 + 1) := by
      ring
    -- combine
    simpa [hrat, hscaled, hnum, hden, Complex.ofReal_mul, Complex.ofReal_add,
           Complex.ofReal_one, Complex.ofReal_bit0, Complex.ofReal_bit1,
           Complex.ofReal_pow, mul_comm, mul_left_comm, mul_assoc, add_comm,
           add_left_comm, add_assoc, pow_two, two_mul, sub_eq_add_neg]

  -- Conclude by transitivity
  simpa [hExp] using hrat'


/-- Bridge (packaging form): Given the Cayley relation between `F` and a disk-side
transform `Hdisk`, together with half-plane analyticity, boundary integrability,
and the Poisson identity on Ω, produce the half-plane Poisson representation
record. This removes internal admits; callers supply the analytic facts. -/
def HalfPlanePoisson_from_Disk
  (F : ℂ → ℂ)
  (Hdisk : ℂ → ℂ)
  (hRel : Set.EqOn F (fun z => Hdisk (toDisk z)) HalfPlaneOuter.Ω)
  (hAnalytic : AnalyticOn ℂ F HalfPlaneOuter.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuter.Ω,
    Integrable (fun t : ℝ => (F (HalfPlaneOuter.boundary t)).re * HalfPlaneOuter.poissonKernel z t))
  (hReEq : ∀ z ∈ HalfPlaneOuter.Ω,
    (F z).re = HalfPlaneOuter.P (fun t : ℝ => (F (HalfPlaneOuter.boundary t)).re) z)
  : HalfPlaneOuter.HasHalfPlanePoissonRepresentation F := by
  -- Package the provided half-plane facts directly; no internal admits.
  exact {
    analytic := hAnalytic
  , integrable := hIntegrable
  , re_eq := hReEq }

/-!
Change-of-variables (structural) adapter: from a disk Poisson representation to a
half‑plane Poisson representation of the real part, provided the Cayley boundary
change-of-variables holds at the level of the Poisson integrals.

This lemma captures the geometric bridge without re-proving kernel change-of-variables
internally. It is designed so that specialized callers can supply the equality of Poisson
integrals `hChange` and the map property `hMap`.
-/

open MeasureTheory

lemma HalfPlanePoisson_real_from_Disk
  (F Hdisk : ℂ → ℂ)
  (hDisk : DiskHardy.HasDiskPoissonRepresentation Hdisk)
  (hRel : Set.EqOn F (fun z => Hdisk (toDisk z)) HalfPlaneOuter.Ω)
  (hMap : ∀ z ∈ HalfPlaneOuter.Ω, toDisk z ∈ DiskHardy.unitDisk)
  (hAnalytic : AnalyticOn ℂ F HalfPlaneOuter.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuter.Ω,
    Integrable (fun t : ℝ => (F (HalfPlaneOuter.boundary t)).re * HalfPlaneOuter.poissonKernel z t))
  (hChange : ∀ z ∈ HalfPlaneOuter.Ω,
    (∫ θ : ℝ, (Hdisk (DiskHardy.boundary θ)).re * DiskHardy.poissonKernel (toDisk z) θ)
      = (∫ t : ℝ, (F (HalfPlaneOuter.boundary t)).re * HalfPlaneOuter.poissonKernel z t))
  : HalfPlaneOuter.HasHalfPlanePoissonRepresentation F := by
  -- Derive the half‑plane real‑part identity from the disk representation and `hChange`.
  have hReEq : ∀ z ∈ HalfPlaneOuter.Ω,
      (F z).re = HalfPlaneOuter.P (fun t : ℝ => (F (HalfPlaneOuter.boundary t)).re) z := by
    intro z hz
    -- From disk representation at w := toDisk z
    have hw : toDisk z ∈ DiskHardy.unitDisk := hMap z hz
    have hDiskEq : (Hdisk (toDisk z)).re
        = ∫ θ : ℝ, (Hdisk (DiskHardy.boundary θ)).re * DiskHardy.poissonKernel (toDisk z) θ :=
      hDisk.re_eq (toDisk z) hw
    -- Relate F z and Hdisk (toDisk z)
    have hRelz : F z = Hdisk (toDisk z) := by
      have := hRel hz
      simpa using this
    -- Change variables on the integral side via the supplied identity `hChange`
    have hCoV := hChange z hz
    -- Conclude equality for Re F
    simpa [HalfPlaneOuter.P, hRelz] using hCoV.symm.trans (by simpa [hRelz] using congrArg id hDiskEq)
  -- Package the half‑plane representation
  exact HalfPlanePoisson_from_Disk F Hdisk hRel hAnalytic hIntegrable hReEq

end CayleyAdapters
end AcademicFramework
end RH
