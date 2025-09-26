import rh.academic_framework.PoissonHalfPlane
import Mathlib.Tactic

/-!
  Small sanity tests for the Poisson half-plane module.
-/

noncomputable section

open RH.HalfPlanePoisson

example : (boundary (3 : ℝ)).re = (1/2 : ℝ) := by
  simpa using boundary_re (3 : ℝ)

example : (boundary (3 : ℝ)).im = (3 : ℝ) := by
  simpa using boundary_im (3 : ℝ)

-- Kernel nonnegativity at a sample point
example : 0 ≤ poissonKernel ((1 : ℝ) + (1 : ℝ) * I) 0 := by
  -- z = 1 + i so Re z - 1/2 = 1/2 > 0
  have hz : ((1 : ℝ) + (1 : ℝ) * I) ∈ Ω := by
    change (1/2 : ℝ) < ((1 : ℝ) + (1 : ℝ) * I).re
    simpa using (show (1/2 : ℝ) < (1 : ℝ) from by norm_num)
  simpa using poissonKernel_nonneg hz 0

-- Kernel integrability at a sample point
example : Integrable (fun t : ℝ => poissonKernel ((1 : ℝ) + (2 : ℝ) * I) t) := by
  have hz : ((1 : ℝ) + (2 : ℝ) * I) ∈ Ω := by
    change (1/2 : ℝ) < ((1 : ℝ) + (2 : ℝ) * I).re
    simpa using (show (1/2 : ℝ) < (1 : ℝ) from by norm_num)
  simpa using poissonKernel_integrable hz
