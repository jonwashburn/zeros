import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Instances.Complex
import rh.RS.CRGreenOuter
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import rh.Cert.KxiPPlus
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace RH
namespace RS

open Set MeasureTheory Filter
open scoped MeasureTheory

def tent (I : Set ℝ) (α : ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ I ∧ 0 < p.2 ∧ p.2 ≤ α}
def shadow (Q : Set (ℝ × ℝ)) : Set ℝ := {t | ∃ σ, 0 < σ ∧ (t, σ) ∈ Q}
@[simp] lemma mem_tent {I : Set ℝ} {α : ℝ} {p : ℝ × ℝ} :
  p ∈ tent I α ↔ p.1 ∈ I ∧ 0 < p.2 ∧ p.2 ≤ α := Iff.rfl
@[simp] lemma mem_shadow {Q : Set (ℝ × ℝ)} {t : ℝ} :
  t ∈ shadow Q ↔ ∃ σ, 0 < σ ∧ (t, σ) ∈ Q := Iff.rfl
lemma tent_mono {I J : Set ℝ} {α : ℝ} (hIJ : I ⊆ J) : tent I α ⊆ tent J α := by
  intro p hp; exact ⟨hIJ hp.1, hp.2.1, hp.2.2⟩
lemma shadow_mono {Q R : Set (ℝ × ℝ)} (hQR : Q ⊆ R) : shadow Q ⊆ shadow R := by
  intro t ht; rcases ht with ⟨σ,hσ,hmem⟩; exact ⟨σ,hσ,hQR hmem⟩
def length (I : Set ℝ) : ℝ := (volume I).toReal
@[simp] def poissonKernel (b x : ℝ) : ℝ := b / (Real.pi * (b^2 + x^2))
def boundaryMap (t : ℝ) : ℂ := (1/2 : ℂ) + Complex.I * (t : ℂ)
@[simp] lemma boundaryMap_re (t : ℝ) : (boundaryMap t).re = (1/2 : ℝ) := by simp [boundaryMap]
def boundaryRe (F : ℂ → ℂ) (t : ℝ) : ℝ := (F (boundaryMap t)).re
@[simp] def poissonSmooth (F : ℂ → ℂ) (b x : ℝ) : ℝ :=
  ∫ t, RH.RS.poissonKernel b (x - t) * boundaryRe F t ∂(volume)

def HasNegativityWindowPoisson (F : ℂ → ℂ) : Prop :=
  ∃ (κ : ℝ) (I : Set ℝ) (b : ℝ) (E : Set ℝ),
    0 < κ ∧ κ ≤ 1 ∧ RS.length I ≤ 1 ∧ 0 < b ∧ b ≤ 1 ∧
    MeasurableSet E ∧ E ⊆ I ∧ RS.length E > 0 ∧
    (∀ x ∈ E, poissonSmooth F b x ≤ -κ)

end RS
end RH
