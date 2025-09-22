import rh.RS.Det2Outer

/-!
# RS Outer witness export (non-invasive)

This small module re-exports a concrete existence witness for
`OuterHalfPlane.ofModulus_det2_over_xi_ext` and a convenient
chosen outer function, without modifying existing files.

It allows downstream code to depend on a stable `ofModulus_det2_over_xi_ext`
provider by importing this file.
-/

noncomputable section

namespace RH
namespace RS

open RH.AcademicFramework.CompletedXi

/-- Exported existence witness: outer on Ω with boundary modulus |det₂/ξ_ext|. -/
theorem outer_exists_det2_over_xi_ext : OuterHalfPlane.ofModulus_det2_over_xi_ext :=
  OuterHalfPlane.ofModulus_det2_over_xi_ext_proved

/-- Chosen outer from the exported existence witness. -/
noncomputable def O_default : ℂ → ℂ :=
  OuterHalfPlane.choose_outer outer_exists_det2_over_xi_ext

/-- The chosen default outer satisfies the RS outer interface and boundary modulus. -/
lemma O_default_spec :
    OuterHalfPlane O_default ∧
    BoundaryModulusEq O_default (fun s => det2 s / riemannXi_ext s) := by
  simpa [O_default] using OuterHalfPlane.choose_outer_spec outer_exists_det2_over_xi_ext

end RS
end RH


