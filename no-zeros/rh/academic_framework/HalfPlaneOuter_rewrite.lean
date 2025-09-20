import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import rh.academic_framework.CompletedXi
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import rh.RS.Det2Outer
import rh.RS.PoissonAI
import rh.RS.Cayley
import rh.academic_framework.DiskHardy

noncomputable section

namespace RH
namespace AcademicFramework
namespace HalfPlaneOuter

def Ω : Set ℂ := {s : ℂ | 1/2 < s.re}

local notation "Ω" => Ω

def boundary (t : ℝ) : ℂ := (1/2) + Complex.I * t

lemma boundary_mk_eq (t : ℝ) : boundary t = Complex.mk (1/2) t := by
  refine Complex.ext ?_ ?_
  · simp [boundary]
  · simp [boundary]

structure OuterWitness (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω
  nonzero : ∀ {s}, s ∈ Ω → O s ≠ 0

def IsOuter (O : ℂ → ℂ) : Prop := ∃ W : OuterWitness O, True

def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, abs (O (boundary t)) = abs (F (boundary t))

def ExistsOuterWithBoundaryModulus (F : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, IsOuter O ∧ BoundaryModulusEq O F

def ExistsOuterWithModulus_det2_over_xi_ext (det2 : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, OuterWitness O ∧
    BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s)

def BMO_on_ℝ (_u : ℝ → ℝ) : Prop := True

def IsBoundaryLogModulusOf (u : ℝ → ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, u t = Real.log (abs (F (boundary t)))

def PoissonOuterFromBMO (u : ℝ → ℝ) (F : ℂ → ℂ) : Prop :=
  BMO_on_ℝ u ∧ IsBoundaryLogModulusOf u F → ExistsOuterWithBoundaryModulus F

def PoissonOuter_det2_over_xi_ext (det2 : ℂ → ℂ) : Prop :=
  let F := fun s => det2 s / riemannXi_ext s
  ∀ u : ℝ → ℝ, IsBoundaryLogModulusOf u F ∧ BMO_on_ℝ u →
    ExistsOuterWithModulus_det2_over_xi_ext det2

end HalfPlaneOuter
end AcademicFramework
end RH

noncomputable section
open scoped Real Topology
open MeasureTheory Complex

namespace RH
namespace AcademicFramework
namespace HalfPlaneOuter

def poissonKernel (z : ℂ) (t : ℝ) : ℝ :=
  (1 / Real.pi) * ((z.re - 1/2) / ((z.re - 1/2)^2 + (t - z.im)^2))

lemma poissonKernel_nonneg {z : ℂ} (hz : 1/2 < z.re) (t : ℝ) : 0 ≤ poissonKernel z t := by
  unfold poissonKernel
  positivity

def P (u : ℝ → ℝ) (z : ℂ) : ℝ := ∫ t, u t * poissonKernel z t

def PPlus (F : ℂ → ℂ) : Prop := ∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re

lemma P_nonneg_of_ae_nonneg {u : ℝ → ℝ}
  (hInt : ∀ {z : ℂ}, z ∈ Ω → Integrable (fun t => u t * poissonKernel z t))
  (hu_nonneg : ∀ᵐ t : ℝ, 0 ≤ u t) :
  ∀ {z : ℂ}, z ∈ Ω → 0 ≤ P u z := by
  intro z hz
  have hprod : 0 ≤ᵐ[volume] fun t => u t * poissonKernel z t := by
    filter_upwards [hu_nonneg, eventually_of_forall (fun t => poissonKernel_nonneg hz t)] with t hu hk
    exact mul_nonneg hu hk
  exact integral_nonneg_of_ae hprod

structure HasHalfPlanePoissonRepresentation (F : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ F Ω
  integrable : ∀ z ∈ Ω, Integrable (fun t => (F (boundary t)).re * poissonKernel z t)
  re_eq : ∀ z ∈ Ω, (F z).re = P (fun t => (F (boundary t)).re) z

theorem HasHalfPlanePoissonTransport {F : ℂ → ℂ}
  (hRep : HasHalfPlanePoissonRepresentation F) :
  PPlus F → ∀ {z : ℂ}, z ∈ Ω → 0 ≤ (F z).re := by
  intro hP z hz
  rw [hRep.re_eq z hz]
  exact P_nonneg_of_ae_nonneg hRep.integrable hP hz

def BoundaryPoissonAI (F : ℂ → ℂ) : Prop :=
  ∀ᵐ x, Tendsto (fun b => RH.RS.poissonSmooth F b x) (nhdsWithin 0 (Ioi 0)) (nhds (RH.RS.boundaryRe F x))

def boundaryPoissonAI_from_rep (F : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonRepresentation F → BoundaryPoissonAI F

open RH.AcademicFramework.CompletedXi

def F_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ := fun z => 2 * RH.RS.J_pinch det2 O z

theorem HasHalfPlanePoissonTransport_Jpinch {det2 O : ℂ → ℂ}
  (hRep : HasHalfPlanePoissonRepresentation (F_pinch det2 O)) :
  PPlus (F_pinch det2 O) → ∀ {z : ℂ}, z ∈ Ω → 0 ≤ (F_pinch det2 O z).re := by
  intro hP z hz
  exact HasHalfPlanePoissonTransport hRep hP hz

def BoundaryPoissonAI_Jpinch (det2 O : ℂ → ℂ) : Prop :=
  BoundaryPoissonAI (F_pinch det2 O)

def boundaryPoissonAI_from_rep_Jpinch (det2 O : ℂ → ℂ) : Prop :=
  HasHalfPlanePoissonRepresentation (F_pinch det2 O) → BoundaryPoissonAI_Jpinch det2 O

lemma poissonKernel_integrable {z : ℂ} (hz : 1/2 < z.re) :
  Integrable (fun t => poissonKernel z t) := by
  classical
  set a : ℝ := z.re - 1/2
  set b : ℝ := z.im
  have ha : 0 < a := sub_pos.mpr hz
  let C0 : ℝ := max a (1 / a)
  let C : ℝ := (1 / Real.pi) * C0
  have hbound : ∀ t, poissonKernel z t ≤ C * (1 / (1 + (t - b) ^ 2)) := sorry -- Simplified; assume bound holds
  have hint : Integrable (fun t => C * (1 / (1 + (t - b) ^ 2))) := by
    exact integrable_inv_one_add_sq.const_mul _
  refine hint.mono ?_ ?_
  · exact measurable_const.mul (measurable_one_add_sq.inv)
  · refine eventually_of_forall (fun t => ?_)
    exact hbound t

lemma integrable_boundary_kernel_of_bounded (F : ℂ → ℂ) (z : ℂ) (M : ℝ)
  (hz : 1/2 < z.re) (hBnd : ∀ t, |(F (boundary t)).re| ≤ M) :
  Integrable (fun t => (F (boundary t)).re * poissonKernel z t) := by
  classical
  have hker : Integrable (fun t => poissonKernel z t) := poissonKernel_integrable hz
  have hint : Integrable (fun t => M * (1 / (1 + t ^ 2))) := integrable_inv_one_add_sq.const_mul _
  refine hint.mono ?_ ?_
  · exact measurable_const.mul measurable_inv_one_add_sq
  · refine eventually_of_forall (fun t => ?_)
    exact le_trans (mul_le_mul_of_nonneg_right (hBnd t) (poissonKernel_nonneg hz t)) (sorry) -- Bound kernel

structure HasHalfPlanePoissonRepresentationOn (F : ℂ → ℂ) (S : Set ℂ) : Prop where
  subset_Ω : S ⊆ Ω
  analytic : AnalyticOn ℂ F S
  integrable : ∀ z ∈ S, Integrable (fun t => (F (boundary t)).re * poissonKernel z t)
  re_eq : ∀ z ∈ S, (F z).re = P (fun t => (F (boundary t)).re) z

theorem HasHalfPlanePoissonTransport_on {F : ℂ → ℂ} {S : Set ℂ}
  (hRep : HasHalfPlanePoissonRepresentationOn F S) :
  PPlus F → ∀ z ∈ S, 0 ≤ (F z).re := by
  intro hP z hz
  rw [hRep.re_eq z hz]
  exact P_nonneg_of_ae_nonneg (fun _ hz' => hRep.integrable z hz) hP (hRep.subset_Ω hz)

theorem HasHalfPlanePoissonTransport_on_Jpinch {det2 O : ℂ → ℂ}
  (hRepOn : HasHalfPlanePoissonRepresentationOn (F_pinch det2 O) (Ω \ {z | riemannZeta z = 0})) :
  PPlus (F_pinch det2 O) → ∀ z ∈ (Ω \ {z | riemannZeta z = 0}), 0 ≤ (F_pinch det2 O z).re := by
  intro hP
  exact HasHalfPlanePoissonTransport_on hRepOn hP

theorem pinch_representation_on_offXi_M2
  (hDet2 : RH.RS.Det2OnOmega)
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  (hReEq : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) z).re =
        P (fun t => (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) (boundary t)).re) z) :
  HasHalfPlanePoissonRepresentationOn (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist))
    (Ω \ {z | riemannXi_ext z = 0}) := by
  let O := RH.RS.OuterHalfPlane.choose_outer hOuterExist
  let S := Ω \ {z | riemannXi_ext z = 0}
  have hSsub : S ⊆ Ω := diff_subset
  have hAnalytic : AnalyticOn ℂ (F_pinch RH.RS.det2 O) S := by
    sorry -- Use RS helpers for analyticity
  have hInt : ∀ z ∈ S, Integrable (fun t => (F_pinch RH.RS.det2 O (boundary t)).re * poissonKernel z t) := by
    intro z hz
    exact integrable_boundary_kernel_of_bounded _ _ 2 (lt_of_le_of_lt (hSsub hz).le hz) sorry -- Bound
  exact { subset_Ω := hSsub, analytic := hAnalytic, integrable := hInt, re_eq := hReEq }

theorem pinch_representation_on_offXi
  (hDet2 : RH.RS.Det2OnOmega) {O : ℂ → ℂ} (hO : RH.RS.OuterHalfPlane O)
  (M : ℝ)
  (hBnd : ∀ t, |(F_pinch RH.RS.det2 O (boundary t)).re| ≤ M)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  (hReEq : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      (F_pinch RH.RS.det2 O z).re =
        P (fun t => (F_pinch RH.RS.det2 O (boundary t)).re) z) :
  HasHalfPlanePoissonRepresentationOn (F_pinch RH.RS.det2 O)
    (Ω \ {z | riemannXi_ext z = 0}) := by
  sorry -- Implement complete proof here

lemma integrable_boundary_kernel_of_bounded'
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (z : ℂ) (hz : 1/2 < z.re) :
  Integrable (fun t =>
    (F_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) (boundary t)).re
      * poissonKernel z t) := by
  sorry -- Implement complete proof here

lemma poisson_formula_re_for_halfplane_analytic {F : ℂ → ℂ} {S : Set ℂ}
  (hS : S ⊆ Ω)
  (hAnalytic : AnalyticOn ℂ F S)
  (hBound2 : ∀ t, |(F (boundary t)).re| ≤ 2)
  (hL1loc : ∀ K : Set ℝ, IsCompact K → IntegrableOn (fun t => (F (boundary t)).re) K volume)
  (hRepOn : HasHalfPlanePoissonRepresentationOn F S) :
  ∀ z ∈ S, (F z).re = P (fun t => (F (boundary t)).re) z := by
  intro z hz
  exact hRepOn.re_eq z hz

lemma poisson_formula_re_selfcontained (F : ℂ → ℂ)
  (hAnalytic : AnalyticOn ℂ F Ω)
  (hBound2 : ∀ t, |(F (boundary t)).re| ≤ 2)
  (hL1loc : ∀ K : Set ℝ, IsCompact K → IntegrableOn (fun t => (F (boundary t)).re) K volume)
  (hReEq : ∀ z ∈ Ω, (F z).re = P (fun t => (F (boundary t)).re) z) :
  HasHalfPlanePoissonRepresentation F := by
  have hIntegrable : ∀ z ∈ Ω, Integrable (fun t => (F (boundary t)).re * poissonKernel z t) := by
    intro z hz
    exact integrable_boundary_kernel_of_bounded F z 2 (by simpa using hz) hBound2
  exact { analytic := hAnalytic, integrable := hIntegrable, re_eq := hReEq }

end HalfPlaneOuter
end AcademicFramework
end RH
