import rh.academic_framework.DiskHardy
import Mathlib.Analysis.Calculus.Deriv
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
