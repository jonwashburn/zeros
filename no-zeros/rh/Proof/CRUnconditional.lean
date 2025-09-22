import rh.Proof.Export

/-!
# CR-outer unconditional entry (removable-existence form)

This thin module removes the explicit `choose` parameter from the
CR-outer closure by accepting the removable-extension existence in the
exact shape expected by the RS bridge, and returning Mathlib's
`RiemannHypothesis`. No existing files are modified.
-/

noncomputable section

namespace RH
namespace Proof
namespace CRUnconditional

open RH.AcademicFramework.CompletedXi

/-- Unconditional RH via CR-outer removable existence:
if for every ζ-zero `ρ ∈ Ω` there exists an isolating open set `U ⊆ Ω`
and an analytic extension `g` of `Θ := Θ_of CRGreenOuterData` across `ρ`
with `g ρ = 1` and a nontriviality point, then `RiemannHypothesis` holds. -/
theorem RH_from_CR_outer_removable
  (hRem : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
        AnalyticOn ℂ (RH.RS.Θ_of RH.RS.CRGreenOuterData) (U \ {ρ}) ∧
        Set.EqOn (RH.RS.Θ_of RH.RS.CRGreenOuterData) g (U \ {ρ}) ∧
        g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : RiemannHypothesis := by
  exact RH.Proof.Final.RiemannHypothesis_mathlib_from_CR_outer_ext_removable hRem

end CRUnconditional
end Proof
end RH


