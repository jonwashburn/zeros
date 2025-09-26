# Lean Proof Audit (RH Repository)

Purpose: Manually review the Lean artifact to confirm what is proved, what is a Prop-level input, and what remains to be implemented. This document will be updated as each file is read.

Conventions:
- Status legend: [Done], [Pending], [N/A]
- Tags: [Proved], [Prop-input], [Scaffold], [Placeholder], [Wrapper]

## Directory Map

Repo root: `/Users/jonathanwashburn/Projects/zeros`

- `no-zeros/rh/RS/`
  - AdmissibleWindows.lean
  - BoundaryAI.lean
  - BoundaryWedge.lean
  - Cayley.lean
  - Context.lean
  - CRGreenOuter.lean
  - CRGreenWhitneyB.lean
  - Det2.lean
  - Det2Outer.lean
  - DirectBridge.lean
  - DirectWedgeProof.lean
  - Domain.lean
  - H1BMOWindows.lean
  - OffZerosBridge.lean
  - OuterWitness.lean
  - PinchCertificate.lean
  - PinchIngredients.lean
  - PinchWrappers.lean
  - PinnedRemovable.lean
  - PoissonAI.lean
  - PoissonOuterA1.lean
  - PoissonPlateau.lean
  - PPlusFromCarleson.lean
  - SchurGlobalization.lean
  - TentShadow.lean
  - TentShadow.backup
  - WhitneyGeometryDefs.lean
  - XiExtBridge.lean
  - test/
    - PPlusPinchFromCarleson.lean

- `no-zeros/rh/Cert/`
  - FactorsWitness.lean
  - K0PPlus.lean
  - KxiPPlus.lean
  - KxiWhitney.lean
  - KxiWhitney_RvM.lean

- `no-zeros/rh/Proof/`
  - AxiomsCheck.lean
  - Closure.lean
  - CRClosure.lean
  - CRUnconditional.lean
  - Entry.lean
  - Export.lean
  - Finalize.lean
  - Finish.lean
  - Main.lean
  - PinchUnconditional.lean
  - PinnedData.lean
  - PoissonIdentity.lean
  - Transport.lean
  - UnconditionalEntry.lean
  - test/
    - ChooserClose.lean
    - Finish.lean
    - Transport.lean

## Review Log

### RS Layer

- RS/Det2Outer.lean — [Done]
  - Summary: Provides `det2` alias and `OuterHalfPlane.ofModulus_det2_over_xi_ext` existence with an explicit witness; [Proved].
  - Notes: Uses a constant witness for outer on Ω and boundary modulus equality along Re=1/2; adequate for interface.

- RS/SchurGlobalization.lean — [Done]
  - Summary: Schur predicate, Cayley transform lemmas, removable globalization, boundary nonvanishing bridges; [Proved]/[Wrapper].
  - Notes: No axioms; core pinch/Schur tools implemented.

- RS/PoissonAI.lean — [Done]
  - Summary: Defines `boundaryMap`, `boundaryRe`, Poisson kernel/smoothing; [Proved]/utility.

- RS/BoundaryWedge.lean — [Reading]
  - Summary: Adapters for Carleson pairing; negativity-window scaffolds; Egorov and density scaffolds; averaged upper bound lemma.
  - Status: `negativity_window_poisson_of_not_PPlus_default` uses a placeholder existence; `Egorov_from_a.e.on_I` scaffold needs finishing mass bound; [Scaffold]/[Placeholder].
  - Action: Implement Egorov-on-interval via `MeasureTheory.egorov`; leave density for follow-up.

- RS/Cayley.lean — [Done]
  - Summary: Cayley interface `Theta_of_J`, Schur results on sets, and pinch specialization for `riemannXi_ext`; boundary modulus identity for `J_pinch`; analyticity of `J_pinch` off zeros; certificate builders; [Proved]/[Wrapper].
  - Notes: Key results include `Theta_Schur_of_Re_nonneg_on`, `boundary_abs_J_pinch_eq_one`, `J_pinch_analytic_on_offXi` and `PinchCertificateExt.of_interfaces`.

- RS/Context.lean — [Done]
  - Summary: `ThetaContext` and `RemovableDatum` records; `globalizeAt` wraps removable globalization via `SchurGlobalization`; [Wrapper].

- RS/Domain.lean — [Done]
  - Summary: Defines the right half-plane domain `Ω`; [Proved].

- RS/Det2.lean — [Done]
  - Summary: Placeholder module delegating to `Det2Outer`; no definitions; [Placeholder].

- RS/CRGreenOuter.lean — [Done]
  - Summary: CR–Green outer façade: unconditional pairing identity and analytic bound; Carleson link; Green+trace packaging; strong rectangle identity; numerous helper lemmas; [Proved]/[Wrapper].
  - Notes: Provides `CRGreen_link` and supporting estimates used by wedge glue.

- RS/PPlusFromCarleson.lean — [Done]
  - Summary: Proves `PPlusFromCarleson_exists_proved_default` via placeholder negativity window + plateau; [Wrapper]/[Scaffold].
  - Notes: Will tighten once negativity window is real.

- RS/PinnedRemovable.lean — [Done]
  - Summary: u-trick packaging to build removable assignment; [Proved].

- RS/OffZerosBridge.lean — [Done]
  - Summary: Off-zeros ζ–Schur decomposition structures and assignment adapters; pinned-limit utilities; [Proved]/[Wrapper].

- RS/WhitneyGeometryDefs.lean — [Done]
  - Summary: Whitney tents/shadows/energies; monotonicity/measure lemmas; [Proved].

- RS/BoundaryAI.lean — [Done]
  - Summary: Transport wrappers from AF Poisson rep to RS transport; [Wrapper].

… (Remaining RS files to review)

### Cert Layer

- Cert/KxiWhitney.lean — [Done]
  - Summary: Prop-level `KxiBound` interface and `Cbox_zeta_of_Kxi` adapter; [Prop-input].

- Cert/KxiPPlus.lean — [Pending]
- Cert/K0PPlus.lean — [Pending]
- Cert/FactorsWitness.lean — [Pending]
- Cert/KxiWhitney_RvM.lean — [Pending]

### Proof Layer

- Proof/Main.lean — [Done]
  - Summary: RH assembly wrappers; pinch route exports; final theorems; [Proved]/[Wrapper].

- Proof/Entry.lean — [Pending]
- Proof/Finish.lean — [Pending]
- Proof/Finalize.lean — [Pending]
- Proof/PoissonIdentity.lean — [Pending]
- Proof/Transport.lean — [Pending]
- Others — [Pending]

## Open Items / Risks

- Replace negativity-window placeholder with real Egorov + density composition [RS/BoundaryWedge.lean].
- Density-window lemma implementation (Lebesgue differentiation / Vitali family) [follow-up].
- Confirm all Cert-layer Prop inputs are clearly documented in paper (Kξ, Carleson⇒(P+), transport rep, removable data).

## Next Actions

- Finish reading remaining RS files; update statuses and notes.
- Review Cert/* and Proof/* files; record any additional gaps.


