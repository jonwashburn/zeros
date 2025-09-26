import rh.RS.OuterWitness
import rh.academic_framework.HalfPlaneOuterV2
import rh.Cert.KxiPPlus

/--!
Proof-layer packaging: Poisson representation on the off-zeros set from a supplied formula.

This module provides a lightweight wrapper that builds the half-plane Poisson representation
record for the pinch field `F_pinch det2 O` on the working subdomain
`Ω \ { z | riemannXi_ext z = 0 }`, under the hypothesis of the Poisson real-part identity
on that set. It avoids deriving the identity (e.g. via a Cayley change of variables) and
simply packages the AF assumptions to unblock transport.

Dependencies used from the Academic Framework (AF):
- `measurable_boundary_F_pinch` — boundary measurability of the pinch field along the line;
- `pinch_poissonRepOn_offZeros` — packages analyticity, integrability, and the supplied formula
  into `HasPoissonRepOn` on the off-zeros subdomain.

We use the RS default outer `O_default` and its boundary-modulus equality from
`rh/RS/OuterWitness.lean`. No cyclic imports are introduced.
-/

noncomputable section

namespace RH
namespace Proof
namespace Transport
/-/ Small bridge: certificate boundary wedge (PPlus) implies AF BoundaryPositive for
the default pinch field. Both predicates evaluate the boundary line `t ↦ 1/2 + i t`.
-/
lemma boundaryPositive_of_PPlus_default :
  RH.Cert.PPlus (F_pinch RH.RS.det2 RH.RS.O_default) →
  BoundaryPositive (F_pinch RH.RS.det2 RH.RS.O_default) := by
  intro h
  -- Unfold both sides and identify `Complex.mk (1/2) t` with `boundary t`.
  simpa [RH.Cert.PPlus, BoundaryPositive, boundary_mk_eq]
    using h


open Complex Set

-- Short aliases for AF namespaces we use
open RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2

/-- Package a half-plane Poisson representation for the pinch field on the off-zeros set,
from a supplied Poisson real-part identity `hFormula`. The outer is the RS default `O_default`.

Inputs:
- `hDet2` — analyticity and nonvanishing of `det2` on `Ω` (RS interface);
- `hXi` — analyticity of `riemannXi_ext` on `Ω` (AF layer);
- boundary measurability facts for `det2`, `O_default`, and `riemannXi_ext` along the line;
- `hFormula` — the Poisson real-part identity for `F_pinch det2 O_default` on
  `Ω \ {riemannXi_ext = 0}`.

Output:
- `HasPoissonRepOn (F_pinch det2 O_default) (Ω \ {riemannXi_ext = 0})`.

This is a thin wrapper around `HalfPlaneOuterV2.pinch_poissonRepOn_offZeros`.
-/
theorem hasRepOn_default_of_formula
  (hDet2 : RH.RS.Det2OnOmega)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  (hDet_meas : Measurable (fun t : ℝ => RH.RS.det2 (boundary t)))
  (hO_meas : Measurable (fun t : ℝ => RH.RS.O_default (boundary t)))
  (hXi_meas : Measurable (fun t : ℝ => riemannXi_ext (boundary t)))
  (hFormula : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 RH.RS.O_default z).re
        = poissonIntegral (fun t => (F_pinch RH.RS.det2 RH.RS.O_default (boundary t)).re) z)
  : HasPoissonRepOn (F_pinch RH.RS.det2 RH.RS.O_default)
      (Ω \ {z | riemannXi_ext z = 0}) := by
  classical
  -- RS default outer and its properties
  have hSpec := RH.RS.O_default_spec
  have hO_RS : RH.RS.OuterHalfPlane RH.RS.O_default := hSpec.1
  -- Convert RS boundary modulus equality to the AF predicate (same boundary parameterization)
  have hBME_AF : BoundaryModulusEq RH.RS.O_default (fun s => RH.RS.det2 s / riemannXi_ext s) := by
    intro t
    -- RS and AF boundary maps are definitional equals up to simp; reuse the RS equality
    have := hSpec.2 t
    -- Rewrite both sides over the AF boundary
    simpa [RH.RS.boundary, boundary] using this
  -- Package via the AF helper
  refine pinch_poissonRepOn_offZeros
    (hDet2 := hDet2) (hO := hO_RS) (hBME := hBME_AF) (hXi := hXi)
    (hDet_meas := hDet_meas) (hO_meas := hO_meas) (hXi_meas := hXi_meas) ?_
  -- Supply the formula hypothesis directly
  intro z hz
  exact hFormula z hz

end Transport
end Proof
end RH

/-!
Transport (P+) ⇒ interior nonnegativity on Ω for the default outer.

We show that a boundary wedge `(P+)` for the concrete pinch field
`F(z) := (2 : ℂ) * J_pinch det2 O_default z` transports to interior
nonnegativity of `Re F` on the right half–plane `Ω`. The Poisson
representation we use is available on the off–zeros set
`Ω \/\/ {riemannXi_ext = 0}`, hence the proof dispatches points `z ∈ Ω`
by cases: on `Ω \\ {riemannXi_ext = 0}` we apply the subset transport;
at `ξ_ext`–zeros, the field evaluates to `0` by definition, so the
nonnegativity is trivial. This restriction is exactly what is needed
downstream.
-/

namespace RH
namespace Proof
namespace Transport

open Complex Set
open RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2

/-- From boundary positivity `(P+)` for the concrete default pinch field
`F(z) := (2 : ℂ) * J_pinch det2 O_default z`, conclude interior
nonnegativity of `Re F` on `Ω`. The proof uses the Poisson representation
on the off–zeros set `Ω \\ {riemannXi_ext = 0}` (built by
`hasRepOn_default_of_formula`) and `HalfPlaneOuterV2.pinch_transport`.

At points where `riemannXi_ext z = 0`, the field evaluates to `0` by
definition, so the inequality is trivial. This off–zeros restriction is
precisely sufficient for downstream applications.
-/
theorem hTrans_default
  (hDet2 : RH.RS.Det2OnOmega)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  (hDet_meas : Measurable (fun t : ℝ => RH.RS.det2 (boundary t)))
  (hO_meas : Measurable (fun t : ℝ => RH.RS.O_default (boundary t)))
  (hXi_meas : Measurable (fun t : ℝ => riemannXi_ext (boundary t)))
  (hFormula : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 RH.RS.O_default z).re =
        poissonIntegral
          (fun t => (F_pinch RH.RS.det2 RH.RS.O_default (boundary t)).re)
          z)
  : RH.Cert.PPlus (fun z => (2 : ℂ) * RH.RS.J_pinch RH.RS.det2 RH.RS.O_default z)
    → ∀ z : ℂ, z.re > (1/2 : ℝ) →
        0 ≤ ((2 : ℂ) * RH.RS.J_pinch RH.RS.det2 RH.RS.O_default z).re := by
  intro hPPlus z hzRe
  classical
  -- Build the Poisson representation on the off-zeros set for the default outer
  have hRepOn :
      HasPoissonRepOn (F_pinch RH.RS.det2 RH.RS.O_default)
        (Ω \ {z | riemannXi_ext z = 0}) :=
    hasRepOn_default_of_formula hDet2 hXi hDet_meas hO_meas hXi_meas hFormula
  -- Interpret certificate-level (P+) as AF BoundaryPositive (boundary maps coincide)
  have hBoundary : BoundaryPositive (F_pinch RH.RS.det2 RH.RS.O_default) := by
    -- `PPlus` tests `t ↦ (1/2 : ℝ, t)`, which is definitional to `boundary t`
    simpa [F_pinch, RH.RS.J_pinch, boundary_mk_eq, boundary]
      using hPPlus
  -- Now dispatch on whether we are off the ξ_ext zeros
  have hzΩ : z ∈ Ω := by simpa [Ω, Set.mem_setOf_eq] using hzRe
  by_cases hXi0 : riemannXi_ext z = 0
  · -- At ξ_ext-zeros, the pinch field evaluates to 0 by definition
    have : (F_pinch RH.RS.det2 RH.RS.O_default z) = 0 := by
      simp [F_pinch, RH.RS.J_pinch, hXi0]
    -- Hence the real part is 0 ≤ 0
    simpa [F_pinch, RH.RS.J_pinch, hXi0]
      using (show 0 ≤ ((F_pinch RH.RS.det2 RH.RS.O_default z).re) from
        by simpa [this] using (le_of_eq (by simp [this])))
  · -- Off-zeros: apply subset transport
    have hzOff : z ∈ (Ω \ {z | riemannXi_ext z = 0}) := by exact ⟨hzΩ, by simpa [Set.mem_setOf_eq] using hXi0⟩
    have : 0 ≤ (F_pinch RH.RS.det2 RH.RS.O_default z).re :=
      poissonTransportOn hRepOn hBoundary z hzOff
    simpa [F_pinch] using this

end Transport
end Proof
end RH
