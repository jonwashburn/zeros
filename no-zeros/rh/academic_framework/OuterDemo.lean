import rh.academic_framework.HalfPlaneOuterV2

/-!
# Demo: Montel/Hurwitz packaging usage

This short file demonstrates instantiating the A1/A2 packaging from
`HalfPlaneOuterV2` with a trivial constant boundary datum `F ≡ 1`.
It produces an outer function on Ω with boundary modulus `|1|`.
-/

noncomputable section

namespace RH
namespace AcademicFramework
namespace OuterDemo

open RH.AcademicFramework.HalfPlaneOuterV2

/-- Demo theorem: existence of an outer on Ω with constant boundary modulus. -/
theorem demo_existsOuter_const : ExistsOuterWithModulus Demo.Fconst := by
  simpa using Demo.existsOuter_const

end OuterDemo
end AcademicFramework
end RH
