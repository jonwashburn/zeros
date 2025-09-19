import rh.academic_framework.DiskHardy
import rh.academic_framework.HalfPlaneOuter

namespace RH
namespace AcademicFramework
namespace CayleyAdapters

open Complex RH.AcademicFramework

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
