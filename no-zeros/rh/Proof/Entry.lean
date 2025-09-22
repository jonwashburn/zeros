import rh.Proof.CRClosure

/-!
# Entry: One-shot RH from CR-outer chooser

This small entry module exposes a single theorem that takes only the
CR-outer removable chooser at ζ-zeros and returns Mathlib's
`RiemannZeta.RiemannHypothesis`. It is intended as a clear public entry
point for readers.
-/

noncomputable section

namespace RH
namespace Proof
namespace Entry

open RH.AcademicFramework.CompletedXi

/-- Public entry theorem: from CR-outer local-data chooser at ζ-zeros
on Ω, conclude Mathlib's `RiemannHypothesis`. -/
theorem RiemannHypothesis_from_CR_outer
  (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
  : RiemannHypothesis :=
  RH.Proof.CRClosure.RH_from_CR_outer_choose choose

end Entry
end Proof
end RH


