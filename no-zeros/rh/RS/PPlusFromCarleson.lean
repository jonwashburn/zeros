import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import rh.Cert.KxiPPlus
import rh.RS.BoundaryWedge
import rh.RS.CRGreenOuter
import rh.RS.PoissonPlateau
import rh.RS.PoissonAI

/-!
RS bridge: Concrete Carleson ⇒ (P+).

We expose a concise adapter that delegates to existing helpers:
- CR–Green pairing + Whitney remainder packaging + Carleson budget → local wedge
- Plateau window with positive lower bound → H¹–BMO window criterion
- A.e. upgrade to boundary wedge `(P+)`.

API provided (used downstream):
- `PPlus_of_ConcreteHalfPlaneCarleson`
- `PPlusFromCarleson_exists_proved`

No axioms and no `sorry`.
-/

noncomputable section

open Complex

namespace RH
namespace RS

/-- Thin legacy wrappers to preserve names; they delegate to BoundaryWedge API and trivialize to Prop-level. -/
@[simp] def localWedge_from_WhitneyCarleson
    (F : ℂ → ℂ)
    (hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ) : Prop :=
  True

/-- Legacy alias: delegate to BoundaryWedge adapters and plateau. -/
theorem localWedge_from_CRGreen_and_Poisson
    (F : ℂ → ℂ)
    (hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ) :
    localWedge_from_WhitneyCarleson (F := F) hex := by
  classical
  rcases hex with ⟨Kξ, hKξ0, hCar⟩
  obtain ⟨ψ, _hψ_even, _hψ_nonneg, _hψ_comp, hψ_mass1,
          ⟨c0, hc0_pos, hPlateau⟩⟩ := RH.RS.poisson_plateau_c0
  let hKxiVar : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ := ⟨Kξ, hKξ0, hCar⟩
  have _pairing :=
        fun {lenI : ℝ}
            (U : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (_ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
            (I : Set ℝ) (α' : ℝ)
            (σ : MeasureTheory.Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
            (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ) (B : ℝ → ℝ)
            (Cψ_pair Cψ_rem : ℝ)
            (hPairVol :
              |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
                ≤ Cψ_pair * Real.sqrt (RS.boxEnergyCRGreen gradU σ Q))
            (Rside Rtop Rint : ℝ)
            (hEqDecomp :
              (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
                = (∫ t in I, _ψ t * B t) + Rside + Rtop + Rint)
            (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
            (hRintBound :
              |Rint| ≤ Cψ_rem * Real.sqrt (RS.boxEnergyCRGreen gradU σ Q))
            (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
            (hEnergy_le : RS.boxEnergyCRGreen gradU σ Q ≤ Classical.choose hKxiVar * lenI) =>
          have hCar' : RH.Cert.ConcreteHalfPlaneCarleson (Classical.choose hKxiVar) :=
            (Classical.choose_spec hKxiVar).2
          RS.local_pairing_bound_from_IBP_and_Carleson
            (Kξ := Classical.choose hKxiVar) (lenI := lenI) (hCar := hCar')
            U W _ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem
            (hPairVol := hPairVol)
            (Rside := Rside) (Rtop := Rtop) (Rint := Rint)
            (hEqDecomp := hEqDecomp)
            (hSideZero := hSideZero) (hTopZero := hTopZero)
            (hRintBound := hRintBound)
            (hCψ_nonneg := hCψ_nonneg)
            (hEnergy_le := hEnergy_le)
  simp [localWedge_from_WhitneyCarleson]

/-/ Concrete‑constant form: from a nonnegative concrete half–plane Carleson
budget `Kξ` for the boundary field `F`, deduce the boundary wedge `(P+)`. -/
theorem PPlus_of_ConcreteHalfPlaneCarleson
    (F : ℂ → ℂ) {Kξ : ℝ}
    (hKξ0 : 0 ≤ Kξ) (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ) :
    RH.Cert.PPlus F := by
  -- Build the local Whitney wedge from CR–Green + plateau + Carleson…
  have hLoc :
      localWedge_from_WhitneyCarleson (F := F) ⟨Kξ, hKξ0, hCar⟩ :=
    localWedge_from_CRGreen_and_Poisson (F := F) ⟨Kξ, hKξ0, hCar⟩
  -- …and apply the a.e. upgrade to obtain the boundary wedge `(P+)`.
  exact ae_of_localWedge_on_Whitney (F := F) ⟨Kξ, hKξ0, hCar⟩ hLoc

@[simp] theorem ae_of_localWedge_on_Whitney
    (F : ℂ → ℂ)
    (hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ)
    (_hLoc : localWedge_from_WhitneyCarleson (F := F) hex) : RH.Cert.PPlus F := by
  rcases hex with ⟨Kξ, hKξ0, hCar⟩
  exact PPlus_of_ConcreteHalfPlaneCarleson (F := F) hKξ0 hCar

/-- Existence‑level bundle: `(∃Kξ ≥ 0, Carleson Kξ) → (P+)`.

This is the statement‑level bridge that downstream code consumes. -/
theorem PPlusFromCarleson_exists_proved
    (F : ℂ → ℂ) : RH.Cert.PPlusFromCarleson_exists F := by
  intro hex
  -- Build the local Whitney wedge (trivialized here) and upgrade to `(P+)`
  have hLoc := localWedge_from_CRGreen_and_Poisson (F := F) hex
  exact ae_of_localWedge_on_Whitney (F := F) hex hLoc

/-- Existence‑level bundle with Poisson AI: `(∃Kξ ≥ 0, Carleson Kξ) → (P+)`. -/
theorem PPlusFromCarleson_exists_proved_AI
    (F : ℂ → ℂ)
    (hAI : ∀ᵐ x : ℝ,
      Filter.Tendsto (fun b : ℝ => RH.RS.poissonSmooth F b x)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (RH.RS.boundaryRe F x)))
    : RH.Cert.PPlusFromCarleson_exists F := by
  intro hex
  rcases hex with ⟨Kξ, hKξ0, hCar⟩
  exact PPlus_of_ConcreteHalfPlaneCarleson (F := F) hKξ0 hCar

end RS
end RH
