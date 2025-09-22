import rh.Proof.Export

/-!
# CR-outer closure shim (non-invasive)

This tiny module exposes a single entry point that takes only the
CR-outer removable chooser at ζ-zeros and returns mathlib's
`RiemannZeta.RiemannHypothesis`, without touching existing files.
-/

noncomputable section

namespace RH
namespace Proof
namespace CRClosure

open RH.AcademicFramework.CompletedXi

/-- One-shot CR-outer closure: given a local-data chooser at each ζ-zero on Ω,
conclude mathlib's `RiemannHypothesis`. -/
theorem RH_from_CR_outer_choose
  (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
  : RiemannHypothesis := by
  -- Nonvanishing of the Archimedean factor on Ω is available
  have hGnz : ∀ ρ ∈ RH.RS.Ω, G_ext ρ ≠ 0 := G_ext_nonzero_on_Ω
  -- Use the final export wrapper
  exact RH.Proof.Export.RiemannHypothesis_mathlib_from_CR_outer_ext choose hGnz

end CRClosure
end Proof
end RH


