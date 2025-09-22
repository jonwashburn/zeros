- file: rh/RS/Det2Outer.lean line: 33 tag: noncomputable_opaque_decl
```
000023: 
000024: namespace RH
000025: namespace RS
000026: 
000027: open Complex Set RH.AcademicFramework.CompletedXi
000028: 
000029: /-- Right half–plane domain Ω. -/
000030: local notation "Ω" => RH.RS.Ω
000031: 
000032: /-- RS symbol for det₂ on Ω (defined elsewhere; reserved here as an opaque symbol). -/
000033: noncomputable opaque det2 : ℂ → ℂ
000034: 
000035: /-- Analytic/nonvanishing facts for `det2` on Ω (interface record). -/
000036: structure Det2OnOmega where
000037:   analytic : AnalyticOn ℂ det2 Ω
000038:   nonzero  : ∀ {s}, s ∈ Ω → det2 s ≠ 0
000039: 
000040: /-- Convenience: package assumed analyticity and nonvanishing of `det2` on `Ω`
000041: into the `Det2OnOmega` interface. -/
000042: def det2_on_Ω_assumed
000043:   (hA : AnalyticOn ℂ det2 Ω)
```

- file: rh/RS/DirectWedgeProof.lean line: 16 tag: sorry
```
000006: import Mathlib.Analysis.SpecialFunctions.Complex.Log
000007: import rh.Cert.KxiPPlus
000008: import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
000009: import rh.RS.PoissonPlateau
000010: import rh.RS.CRGreenOuter
000011: -- Import only low-level modules to avoid cycles with `PPlusFromCarleson`
000012: 
000013: /-!
000014: # Direct Proof of Local Wedge (Implementation)
000015: 
000016: This file provides the actual implementation that replaces the `sorry` in
000017: `localWedge_from_pairing_and_uniformTest`, following the direct approach
000018: from the written proof that avoids H¹-BMO duality.
000019: 
000020: ## Key Strategy
000021: 
000022: The written proof (Riemann-lean-verified.tex) shows that we can avoid the
000023: full H¹-BMO theory by:
000024: 1. Using even windows that annihilate affine functions
000025: 2. Applying direct Cauchy-Schwarz with scale-invariant bounds
000026: 3. Exploiting the specific structure of our problem
```

- file: rh/RS/H1BMOWindows.lean line: 32 tag: opaque_decl
```
000022: 
000023: namespace RS
000024: 
000025: /-- A Whitney window encoded only by the base length `ℓ = |I| > 0`. -/
000026: structure Window where
000027:   ℓ   : ℝ
000028:   pos : 0 < ℓ
000029: 
000030: /-- Opaque: window "mass" induced by a fixed kernel `ψ`.
000031: We only use nonnegativity and a uniform lower bound `≥ c0⋅ℓ`. -/
000032: opaque windowMass (ψ : ℝ → ℝ) (W : Window) : ℝ
000033: 
000034: /-- Opaque: Carleson "box energy" of `u` measured through `ψ` on `W`.
000035: We only use nonnegativity and the linear bound `≤ Cbox⋅ℓ`. -/
000036: opaque boxEnergy (ψ u : ℝ → ℝ) (W : Window) : ℝ
000037: 
000038: /-- Kernel-side data assumed for the fixed window `ψ`: evenness and mass
000039: comparability from below with constant `c0 > 0`. -/
000040: class WindowKernelData (ψ : ℝ → ℝ) where
000041:   even        : ∀ t, ψ t = ψ (-t)
000042:   c0          : ℝ
```

- file: rh/RS/H1BMOWindows.lean line: 36 tag: opaque_decl
```
000026: structure Window where
000027:   ℓ   : ℝ
000028:   pos : 0 < ℓ
000029: 
000030: /-- Opaque: window "mass" induced by a fixed kernel `ψ`.
000031: We only use nonnegativity and a uniform lower bound `≥ c0⋅ℓ`. -/
000032: opaque windowMass (ψ : ℝ → ℝ) (W : Window) : ℝ
000033: 
000034: /-- Opaque: Carleson "box energy" of `u` measured through `ψ` on `W`.
000035: We only use nonnegativity and the linear bound `≤ Cbox⋅ℓ`. -/
000036: opaque boxEnergy (ψ u : ℝ → ℝ) (W : Window) : ℝ
000037: 
000038: /-- Kernel-side data assumed for the fixed window `ψ`: evenness and mass
000039: comparability from below with constant `c0 > 0`. -/
000040: class WindowKernelData (ψ : ℝ → ℝ) where
000041:   even        : ∀ t, ψ t = ψ (-t)
000042:   c0          : ℝ
000043:   c0_pos      : 0 < c0
000044:   mass_nonneg : ∀ W, 0 ≤ windowMass ψ W
000045:   mass_lower  : ∀ W, c0 * W.ℓ ≤ windowMass ψ W
000046: 
```

- file: rh/RS/PPlusFromCarleson.lean line: 22 tag: sorry
```
000012: 
000013: We expose a concise adapter that delegates to existing helpers:
000014: - CR–Green pairing + Whitney remainder packaging + Carleson budget → local wedge
000015: - Plateau window with positive lower bound → H¹–BMO window criterion
000016: - A.e. upgrade to boundary wedge `(P+)`.
000017: 
000018: API provided (used downstream):
000019: - `PPlus_of_ConcreteHalfPlaneCarleson`
000020: - `PPlusFromCarleson_exists_proved`
000021: 
000022: No axioms and no `sorry`.
000023: -/
000024: 
000025: noncomputable section
000026: 
000027: open Complex
000028: 
000029: namespace RH
000030: namespace RS
000031: 
000032: /- Reordered: provide adapters that avoid forward references. -/
```

- file: rh/academic_framework/CayleyAdapters.lean line: 76 tag: admit
```
000066:     simpa [toDisk, hzNe] using this
000067:   have hlt' : Complex.abs (toDisk z) < 1 := by
000068:     rw [this]
000069:     have hzpos : 0 < Complex.abs z := AbsoluteValue.pos Complex.abs hzNe
000070:     exact div_lt_one hzpos |>.mpr hlt
000071:   simpa [DiskHardy.unitDisk, Set.mem_setOf_eq] using hlt'
000072: 
000073: -- Note: the boundary image lies on the unit circle; not required downstream here.
000074: -- lemma boundary_maps_to_unitCircle (t : ℝ) : Complex.abs (boundaryToDisk t) = 1 := by
000075: --   -- Proof available via direct algebra on abs-squared; omitted since unused.
000076: --   admit
000077: 
000078: /-!
000079: ## Change-of-variables helpers for Cayley
000080: 
000081: We record algebraic identities used in the half‑plane↔disk Poisson kernel
000082: change‑of‑variables calculation.
000083: -/
000084: 
000085: open Complex
000086: 
```

