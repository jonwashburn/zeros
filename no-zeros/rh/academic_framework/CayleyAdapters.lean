import rh.academic_framework.DiskHardy
-- (no additional mathlib imports needed here)
import rh.academic_framework.HalfPlaneOuterV2

noncomputable section

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
@[simp] def boundaryToDisk (t : ℝ) : ℂ := toDisk (HalfPlaneOuterV2.boundary t)

/-! ## Geometry facts for the Cayley transform -/

lemma map_Ω_to_unitDisk {z : ℂ}
  (hz : z ∈ HalfPlaneOuterV2.Ω) : toDisk z ∈ DiskHardy.unitDisk := by
  -- Re z > 1/2 ⇒ |z-1| < |z| ⇒ |(z-1)/z| < 1
  have hzRe : (1/2 : ℝ) < z.re := by simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using hz
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
  have hrepr : HalfPlaneOuterV2.boundary t = Complex.mk (1/2) t := by
    simpa [HalfPlaneOuterV2.boundary_mk_eq]
  have hne : HalfPlaneOuterV2.boundary t ≠ 0 := by
    intro h; have hre := congrArg Complex.re h; simpa [hrepr] using hre
  have h1 : Complex.abs (HalfPlaneOuterV2.boundary t - 1)
            = Real.sqrt (((- (1/2 : ℝ))^2) + t^2) := by
    have : HalfPlaneOuterV2.boundary t - 1 = Complex.mk (- (1/2 : ℝ)) t := by
      simp [hrepr, sub_eq_add_neg]
    simpa [this, Complex.abs_def]
  have h2 : Complex.abs (HalfPlaneOuterV2.boundary t)
            = Real.sqrt (((1/2 : ℝ)^2) + t^2) := by
    simpa [hrepr, Complex.abs_def]
  have : Complex.abs (boundaryToDisk t) = Complex.abs (HalfPlaneOuterV2.boundary t - 1) / Complex.abs (HalfPlaneOuterV2.boundary t) := by
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
  simp [boundaryToDisk, toDisk, HalfPlaneOuterV2.boundary,
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
lemma boundary_ne_zero (t : ℝ) : HalfPlaneOuterV2.boundary t ≠ 0 := by
  intro h
  have : (HalfPlaneOuterV2.boundary t).re = (0 : ℝ) := by simpa [h]
  simp [HalfPlaneOuterV2.boundary] at this

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
    = Complex.abs (HalfPlaneOuterV2.boundary t - z)
        / (Complex.abs (HalfPlaneOuterV2.boundary t) * Complex.abs z) := by
  have hs0 : HalfPlaneOuterV2.boundary t ≠ 0 := boundary_ne_zero t
  have hdiff : boundaryToDisk t - toDisk z
      = (HalfPlaneOuterV2.boundary t - z) / (HalfPlaneOuterV2.boundary t * z) := by
    -- use the general difference formula specialized to u=s, v=z
    simpa [boundaryToDisk] using toDisk_sub (u := HalfPlaneOuterV2.boundary t) (v := z) hs0 hz
  -- take absolute values
  simpa [hdiff, Complex.abs_div, Complex.abs_mul]

/-- Core density identity: rewrite `(1 - |w|^2)/|ξ − w|^2` in half‑plane variables. -/
lemma density_ratio_boundary (z : ℂ) (hzΩ : z ∈ HalfPlaneOuterV2.Ω) (t : ℝ) :
  let w := toDisk z
  let ξ := boundaryToDisk t
  (1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2
    = ((2 : ℝ) * z.re - 1) * (Complex.abs (HalfPlaneOuterV2.boundary t))^2
        / (Complex.abs (HalfPlaneOuterV2.boundary t - z))^2 := by
  classical
  intro w ξ
  have hz0 : z ≠ 0 := by
    -- Re z > 1/2 ⇒ z ≠ 0
    intro h; have : (0 : ℝ) < (1/2 : ℝ) := by norm_num
    have hRe : (1/2 : ℝ) < z.re := by simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using hzΩ
    exact (lt_irrefl _ (lt_trans this hRe))
  have hs0 : HalfPlaneOuterV2.boundary t ≠ 0 := boundary_ne_zero t
  -- Evaluate denominator via difference identity
  have hDen : (Complex.abs (ξ - w))^2
      = (Complex.abs (HalfPlaneOuterV2.boundary t - z))^2
          / ((Complex.abs (HalfPlaneOuterV2.boundary t))^2 * (Complex.abs z)^2) := by
    have := abs_boundaryToDisk_sub_toDisk t z hz0
    -- square both sides
    have : (Complex.abs (boundaryToDisk t - toDisk z))^2
        = (Complex.abs (HalfPlaneOuterV2.boundary t - z))^2
            / ((Complex.abs (HalfPlaneOuterV2.boundary t) * Complex.abs z)^2) := by
      simpa [pow_two, mul_pow] using congrArg (fun r => r^2) this
    -- simplify (ab)^2 = a^2 b^2
    simpa [ξ, w, pow_two, mul_pow] using this
  -- Evaluate numerator via one_minus_absSq_toDisk
  have hNum : 1 - (Complex.abs w)^2
      = ((2 : ℝ) * z.re - 1) / (Complex.abs z)^2 := by
    simpa [w] using one_minus_absSq_toDisk z hz0
  -- assemble the ratio
  have hPos : (Complex.abs (HalfPlaneOuterV2.boundary t) * Complex.abs z)^2
      = (Complex.abs (HalfPlaneOuterV2.boundary t))^2 * (Complex.abs z)^2 := by
    ring
  -- compute: (A/|z|^2) / (B/(|s|^2|z|^2)) = A*|s|^2/B
  have : (1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2
      = (((2 : ℝ) * z.re - 1) / (Complex.abs z)^2)
          / ((Complex.abs (HalfPlaneOuterV2.boundary t - z))^2
              / ((Complex.abs (HalfPlaneOuterV2.boundary t))^2 * (Complex.abs z)^2)) := by
    simpa [hNum, hDen]
  -- finish with field algebra
  field_simp [this]

/-- Real parameters `a(z) = Re z − 1/2` and `b(z) = Im z` for change-of-variables. -/
def a (z : ℂ) : ℝ := z.re - (1/2 : ℝ)
def b (z : ℂ) : ℝ := z.im

lemma a_pos_of_mem_Ω {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) : 0 < a z := by
  simpa [a, HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using (hz : (1/2 : ℝ) < z.re)

-- (Angle parametrization lemmas omitted here; not needed for algebraic identities above.)


/-- Bridge (packaging form): Given the Cayley relation between `F` and a disk-side
transform `Hdisk`, together with half-plane analyticity, boundary integrability,
and the Poisson identity on Ω, produce the half-plane Poisson representation
record. This removes internal admits; callers supply the analytic facts. -/
def HalfPlanePoisson_from_Disk
  (F : ℂ → ℂ)
  (Hdisk : ℂ → ℂ)
  (hRel : Set.EqOn F (fun z => Hdisk (toDisk z)) HalfPlaneOuterV2.Ω)
  (hAnalytic : AnalyticOn ℂ F HalfPlaneOuterV2.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuterV2.Ω,
    Integrable (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t))
  (hReEq : ∀ z ∈ HalfPlaneOuterV2.Ω,
    (F z).re = HalfPlaneOuterV2.poissonIntegral (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re) z)
  : HalfPlaneOuterV2.HasPoissonRep F := by
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
  (hRel : Set.EqOn F (fun z => Hdisk (toDisk z)) HalfPlaneOuterV2.Ω)
  (hMap : ∀ z ∈ HalfPlaneOuterV2.Ω, toDisk z ∈ DiskHardy.unitDisk)
  (hAnalytic : AnalyticOn ℂ F HalfPlaneOuterV2.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuterV2.Ω,
    Integrable (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t))
  (hChange : ∀ z ∈ HalfPlaneOuterV2.Ω,
    (∫ θ : ℝ, (Hdisk (DiskHardy.boundary θ)).re * DiskHardy.poissonKernel (toDisk z) θ)
      = (∫ t : ℝ, (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t))
  : HalfPlaneOuterV2.HasPoissonRep F := by
  -- Derive the half‑plane real‑part identity from the disk representation and `hChange`.
  have hReEq : ∀ z ∈ HalfPlaneOuterV2.Ω,
      (F z).re = HalfPlaneOuterV2.poissonIntegral (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re) z := by
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
    simpa [HalfPlaneOuterV2.poissonIntegral, hRelz] using hCoV.symm.trans (by simpa [hRelz] using congrArg id hDiskEq)
  -- Package the half‑plane representation
  exact HalfPlanePoisson_from_Disk F Hdisk hRel hAnalytic hIntegrable hReEq

end CayleyAdapters
end AcademicFramework
end RH
