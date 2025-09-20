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
    intro h; subst h; simp at hzRe; linarith
  have hsq : (Complex.abs (z - 1))^2 = (Complex.abs z)^2 - 2 * z.re + 1 := by
    simp [Complex.sq_abs, Complex.normSq_sub, Complex.normSq_one]
    ring
  have hlt : Complex.abs (z - 1) < Complex.abs z := by
    -- Compare squares using Re z > 1/2, then drop squares on nonnegative reals
    have hlt_sq : (Complex.abs (z - 1))^2 < (Complex.abs z)^2 := by
      rw [hsq]
      have : - 2 * z.re + 1 < 0 := by linarith
      linarith
    -- Convert a^2 < b^2 to a < b using sq_lt_sq on ℝ
    have habs_lt : |Complex.abs (z - 1)| < |Complex.abs z| := (sq_lt_sq).1 hlt_sq
    simpa using habs_lt
  have : Complex.abs (toDisk z) = Complex.abs (z - 1) / Complex.abs z := by
    -- directly by abs_div
    have : Complex.abs ((z - 1) / z) = Complex.abs (z - 1) / Complex.abs z := by
      simpa using Complex.abs_div (z - 1) z
    simpa [toDisk, hzNe] using this
  have hlt' : Complex.abs (toDisk z) < 1 := by
    rw [this]
    have hzpos : 0 < Complex.abs z := AbsoluteValue.pos Complex.abs hzNe
    exact div_lt_one hzpos |>.mpr hlt
  simpa [DiskHardy.unitDisk, Set.mem_setOf_eq] using hlt'

lemma boundary_maps_to_unitCircle (t : ℝ) : Complex.abs (boundaryToDisk t) = 1 := by
  -- Abbreviate s := 1/2 + i t
  set s : ℂ := HalfPlaneOuterV2.boundary t
  have hrepr : s = Complex.mk (1/2) t := HalfPlaneOuterV2.boundary_mk_eq t
  -- Boundary point is nonzero since Re s = 1/2
  have hs0 : s ≠ 0 := by
    intro h
    have hre : s.re = (1/2 : ℝ) := by simpa [hrepr]
    have : (0 : ℝ) = (1/2 : ℝ) := by simpa [h] using hre
    norm_num at this
  -- |toDisk s| = |s-1|/|s|
  have hratio : Complex.abs (boundaryToDisk t) = Complex.abs (s - 1) / Complex.abs s := by
    -- Use abs_div; boundaryToDisk t = (s-1)/s
    have hdiv : Complex.abs ((s - 1) / s) = Complex.abs (s - 1) / Complex.abs s := by
      simpa using Complex.abs_div (s - 1) s
    simpa [boundaryToDisk, toDisk, hs0] using hdiv
  -- Compute both absolute values explicitly
  have hsub : s - 1 = Complex.mk (-(1/2 : ℝ)) t := by
    refine Complex.ext ?hre ?him
    · have : (1/2 : ℝ) - 1 = - (1/2 : ℝ) := by norm_num
      simp [hrepr, this]
    · simp [hrepr]
  have habs_sub : Complex.abs (s - 1) = Real.sqrt (((1/2 : ℝ)^2) + t^2) := by
    simp [hsub, Complex.abs_def, Complex.normSq_mk, pow_two]
  have habs_s : Complex.abs s = Real.sqrt (((1/2 : ℝ)^2) + t^2) := by
    simp [hrepr, Complex.abs_def, Complex.normSq_mk, pow_two]
  have hpos : 0 < Real.sqrt (((1/2 : ℝ)^2) + t^2) := by
    apply Real.sqrt_pos.mpr
    have : 0 < (1/2 : ℝ)^2 + t^2 := by nlinarith
    simpa using this
  -- Finish: ratio of equal positive quantities is 1
  have hratio' : Complex.abs (boundaryToDisk t)
      = Real.sqrt (((1/2 : ℝ)^2) + t^2) / Real.sqrt (((1/2 : ℝ)^2) + t^2) := by
    simpa [hratio, habs_sub, habs_s]
  have hden_ne : Real.sqrt (((1/2 : ℝ)^2) + t^2) ≠ 0 := ne_of_gt hpos
  have hunit : Real.sqrt (((1/2 : ℝ)^2) + t^2) / Real.sqrt (((1/2 : ℝ)^2) + t^2) = (1 : ℝ) := by
    simp [hden_ne]
  simpa [hratio', hunit]

/-!
## Change-of-variables helpers for Cayley

We record algebraic identities used in the half‑plane↔disk Poisson kernel
change‑of‑variables calculation.
-/

open Complex

/-- Closed form for `boundaryToDisk t` as a rational expression in `t`. -/
-- Removed closed-form lemma; not required for current adapters

/-- Absolute value of `toDisk z` as the ratio `|z−1|/|z|` (valid for `z ≠ 0`). -/
lemma abs_toDisk (z : ℂ) (hz : z ≠ 0) :
  Complex.abs (toDisk z) = Complex.abs (z - 1) / Complex.abs z := by
  -- Use abs_div to split the absolute value
  have : Complex.abs ((z - 1) / z) = Complex.abs (z - 1) / Complex.abs z := by
    simpa using Complex.abs_div (z - 1) z
  simpa [toDisk, hz] using this

/-- `1 - ‖toDisk z‖^2` in terms of `z` (valid for `z ≠ 0`). -/
lemma one_minus_absSq_toDisk (z : ℂ) (hz : z ≠ 0) :
  1 - (Complex.abs (toDisk z))^2 =
    ((2 : ℝ) * z.re - 1) / (Complex.abs z)^2 := by
  have h : Complex.abs (toDisk z) = Complex.abs (z - 1) / Complex.abs z :=
    abs_toDisk z hz
  -- 1 - (|z-1|/|z|)^2 = (|z|^2 - |z-1|^2) / |z|^2
  rw [h]
  have : 1 - (Complex.abs (z - 1) / Complex.abs z)^2
        = ((Complex.abs z)^2 - (Complex.abs (z - 1))^2) / (Complex.abs z)^2 := by
    have hz_ne : Complex.abs z ≠ 0 := AbsoluteValue.ne_zero Complex.abs hz
    field_simp [hz_ne]
    ring
  -- |z|^2 - |z-1|^2 = 2 Re z - 1
  have hdiff : (Complex.abs z)^2 - (Complex.abs (z - 1))^2
      = (2 : ℝ) * z.re - 1 := by
    -- Expand |z-1|^2 = |z|^2 - 2 Re z + 1
    rw [Complex.sq_abs, Complex.sq_abs, Complex.normSq_sub]
    simp [Complex.normSq_one]
    ring
  simp [this, hdiff]

/-- The boundary point `s = 1/2 + i t` is never zero. -/
lemma boundary_ne_zero (t : ℝ) : HalfPlaneOuterV2.boundary t ≠ 0 := by
  -- Use the real part: Re(boundary t) = 1/2 ≠ 0
  have hre : (HalfPlaneOuterV2.boundary t).re = (1/2 : ℝ) := by
    simp [HalfPlaneOuterV2.boundary_mk_eq]
  intro h
  simpa [h] using hre

/-- Difference of Cayley images in terms of original points. Requires both nonzero. -/
lemma toDisk_sub (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
  toDisk u - toDisk v = (u - v) / (u * v) := by
  -- toDisk w = 1 - 1/w
  simp [toDisk]
  field_simp [hu, hv]
  ring

/-- Absolute value of the boundary/disk difference in terms of original points. -/
lemma abs_boundaryToDisk_sub_toDisk (t : ℝ) (z : ℂ) (hz : z ≠ 0) :
  Complex.abs (boundaryToDisk t - toDisk z)
    = Complex.abs (HalfPlaneOuterV2.boundary t - z)
        / (Complex.abs (HalfPlaneOuterV2.boundary t) * Complex.abs z) := by
  have hs0 : HalfPlaneOuterV2.boundary t ≠ 0 := boundary_ne_zero t
  have hdiff : boundaryToDisk t - toDisk z
      = (HalfPlaneOuterV2.boundary t - z) / (HalfPlaneOuterV2.boundary t * z) := by
    -- use the general difference formula specialized to u=s, v=z
    have := toDisk_sub (HalfPlaneOuterV2.boundary t) z hs0 hz
    -- boundaryToDisk t = toDisk (boundary t)
    simpa [boundaryToDisk] using this
  -- take absolute values
  rw [hdiff]
  have hdiv : Complex.abs ((HalfPlaneOuterV2.boundary t - z) / (HalfPlaneOuterV2.boundary t * z))
      = Complex.abs (HalfPlaneOuterV2.boundary t - z)
          / Complex.abs (HalfPlaneOuterV2.boundary t * z) := by
    simpa using Complex.abs_div (HalfPlaneOuterV2.boundary t - z) (HalfPlaneOuterV2.boundary t * z)
  have hmul : Complex.abs (HalfPlaneOuterV2.boundary t * z)
      = Complex.abs (HalfPlaneOuterV2.boundary t) * Complex.abs z := by
    simpa using Complex.abs_mul (HalfPlaneOuterV2.boundary t) z
  simpa [hdiv, hmul]

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
    intro h; subst h
    have : (0 : ℝ) < (1/2 : ℝ) := by norm_num
    have hRe : (1/2 : ℝ) < (0:ℂ).re := by simpa [HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] using hzΩ
    simp at hRe
    linarith
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
      rw [this]
      simp [pow_two, mul_pow, div_pow]
    -- simplify (ab)^2 = a^2 b^2
    simp [ξ, w] at this ⊢
    rw [this, mul_pow]
  -- Evaluate numerator via one_minus_absSq_toDisk
  have hNum : 1 - (Complex.abs w)^2
      = ((2 : ℝ) * z.re - 1) / (Complex.abs z)^2 := by
    simp only [w]
    exact one_minus_absSq_toDisk z hz0
  -- assemble the ratio
  have hPos : (Complex.abs (HalfPlaneOuterV2.boundary t) * Complex.abs z)^2
      = (Complex.abs (HalfPlaneOuterV2.boundary t))^2 * (Complex.abs z)^2 := 
    mul_pow _ _ 2
  -- compute: (A/|z|^2) / (B/(|s|^2|z|^2)) = A*|s|^2/B
  have : (1 - (Complex.abs w)^2) / (Complex.abs (ξ - w))^2
      = (((2 : ℝ) * z.re - 1) / (Complex.abs z)^2)
          / ((Complex.abs (HalfPlaneOuterV2.boundary t - z))^2
              / ((Complex.abs (HalfPlaneOuterV2.boundary t))^2 * (Complex.abs z)^2)) := by
    rw [hNum, hDen]
  -- finish with field algebra
  rw [this, hPos]
  -- Simplify (A/B) / (C/(D*E)) = (A/B) * (D*E/C) = A*D*E/(B*C)
  rw [div_div]
  rw [mul_div_assoc, mul_div_assoc]
  congr 1
  ring

/-- Real parameters `a(z) = Re z − 1/2` and `b(z) = Im z` for change-of-variables. -/
def a (z : ℂ) : ℝ := z.re - (1/2 : ℝ)
def b (z : ℂ) : ℝ := z.im

lemma a_pos_of_mem_Ω {z : ℂ} (hz : z ∈ HalfPlaneOuterV2.Ω) : 0 < a z := by
  simp only [a, HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] at hz ⊢
  linarith

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
    MeasureTheory.Integrable (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t))
  (hReEq : ∀ z ∈ HalfPlaneOuterV2.Ω,
    (F z).re = HalfPlaneOuterV2.poissonIntegral (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re) z)
  : HalfPlaneOuterV2.HasPoissonRep F := by
  -- Package the provided half-plane facts directly; no internal admits.
  exact {
    analytic := hAnalytic
    integrable := hIntegrable
    formula := hReEq }

/-!
Change-of-variables (structural) adapter: from a disk Poisson representation to a
half‑plane Poisson representation of the real part, provided the Cayley boundary
change-of-variables holds at the level of the Poisson integrals.

This lemma captures the geometric bridge without re-proving kernel change-of-variables
internally. It is designed so that specialized callers can supply the equality of Poisson
integrals `hChange` and the map property `hMap`.
-/

open MeasureTheory

-- Add using declaration to make Integrable accessible without prefix
lemma HalfPlanePoisson_real_from_Disk
  (F Hdisk : ℂ → ℂ)
  (hDisk : DiskHardy.HasDiskPoissonRepresentation Hdisk)
  (hRel : Set.EqOn F (fun z => Hdisk (toDisk z)) HalfPlaneOuterV2.Ω)
  (hMap : ∀ z ∈ HalfPlaneOuterV2.Ω, toDisk z ∈ DiskHardy.unitDisk)
  (hAnalytic : AnalyticOn ℂ F HalfPlaneOuterV2.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuterV2.Ω,
    MeasureTheory.Integrable (fun t : ℝ => (F (HalfPlaneOuterV2.boundary t)).re * HalfPlaneOuterV2.poissonKernel z t))
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
    have hRelz : F z = Hdisk (toDisk z) := 
      hRel hz
    -- Change variables on the integral side via the supplied identity `hChange`
    have hCoV := hChange z hz
    -- Conclude equality for Re F
    rw [HalfPlaneOuterV2.poissonIntegral, hRelz, hDiskEq]
    exact hCoV
  -- Package the half‑plane representation
  exact HalfPlanePoisson_from_Disk F Hdisk hRel hAnalytic hIntegrable hReEq

end CayleyAdapters
end AcademicFramework
end RH
