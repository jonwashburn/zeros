### Lessons learned: Cayley CoV, BoundaryWedge adapters, and PPlus wiring (2025-09-20)

This note captures what worked, what broke, and how to proceed safely next time when touching the Cayley/Poisson bridge, BoundaryWedge adapters, and the `(P+)` glue.

#### What worked (keep these)
- `rh/academic_framework/CayleyAdapters.lean` algebra refactor:
  - Prefer `simp`, `ring_nf`, and `[pow_two]` over manual rewrites.
  - Use `abs_div` (not `Complex.abs_div`), `Complex.abs_mul`, `Complex.abs_def`, `Real.sqrt_sq_eq_abs`.
  - For field algebra, set up explicit nonzeros: `pow_ne_zero 2 (AbsoluteValue.ne_zero _ …)`.
  - The density identity `density_ratio_boundary` now has a robust statement (good foundation for CoV).
- `rh/RS/BoundaryWedge.lean` minimal adapters aligned with CRGreen exports:
  - Use exactly the CRGreen names: `boxEnergyCRGreen`, `pairing_whitney_analytic_bound`, `CRGreen_pairing_whitney_from_green_trace`, `sqrt_boxEnergy_bound_of_ConcreteHalfPlaneCarleson`.
  - Provide lightweight wiring lemmas: `local_pairing_bound_from_Carleson_budget`, `local_pairing_bound_from_IBP_and_Carleson`, and the `_aeZero_` variant.
  - Keep heavy measure theory out of this façade.

#### What broke (and why)
- `rh/academic_framework/PoissonCayley.lean` introduced a full change-of-variables route but referenced missing calculus pieces and angle parametrization helpers that don’t exist in `CayleyAdapters` yet:
  - Missing: `theta_of`, `hasDerivAt_theta_of`, `boundaryToDisk_eq_boundary_theta0`.
  - Name drift from earlier working version (which assumed an `hReEq` and delegated to the M=2 builder) caused compilation failures.
- `rh/RS/PPlusFromCarleson.lean` rewiring created cyclical dependencies and ordering issues:
  - `ae_of_localWedge_on_Whitney` was made to call `PPlus_of_ConcreteHalfPlaneCarleson`, while the latter relied on the former → recursion.
  - Thin wrappers existed but their order and references drifted, leaving unknown identifiers.

#### Do this next time (safe pattern)
1) BoundaryWedge
- Keep adapters minimal. Only package CRGreen analytics and Carleson/overlap algebra.
- Don’t rename exports; never unify `RS.boxEnergy` with `boxEnergyCRGreen`.

2) CayleyAdapters
- Normalize algebra using `simp`/`ring_nf` and `[pow_two]`.
- Use `abs_div` and avoid fragile `.mp` rewrites.
- For square roots and absolute values, rely on `Complex.abs_def`, `Complex.normSq_mk`, `Real.sqrt_sq_eq_abs`.
- Prepare field-simp with explicit nonzero proofs; avoid ad-hoc case splits.
- Add calculus lemmas (angle map, derivative, boundary angle equality) before wiring kernel CoV into other modules:
  - `theta_of (z : ℂ) (t : ℝ) : ℝ`
  - `hasDerivAt_theta_of : HasDerivAt (theta_of z) (…explicit…) t`
  - `boundaryToDisk_eq_boundary_theta0 : DiskHardy.boundary (theta_of z t) = CayleyAdapters.boundaryToDisk t` (or the correct formulation used in the density proof).

3) PoissonCayley
- If the calculus lemmas aren’t in place, prefer the proven M=2 route:
  - Use `HalfPlaneOuterV2.pinch_representation_on_offXi_M2` with an `hReEq` hypothesis rather than attempting the full kernel CoV path.
- Keep the CoV/transport scaffolding isolated and behind a separate wrapper so it can be toggled without touching `Main`.

4) PPlusFromCarleson
- Avoid cyclic definitions. Use this order and delegation:
  - Define `localWedge_from_CRGreen_and_Poisson` using BoundaryWedge adapters + plateau constant.
  - Define `PPlusFromCarleson_exists_proved (F)` to unpack `hex` and call `PPlus_of_ConcreteHalfPlaneCarleson`.
  - Define `PPlus_of_ConcreteHalfPlaneCarleson (F) (Kξ)` to call the existence-level wrapper.
  - Keep legacy thin wrappers (`localWedge_from_WhitneyCarleson`, `ae_of_localWedge_on_Whitney`) as trivial shims only if downstream expects them; ensure they don’t form cycles.

#### Minimal checklists
- BoundaryWedge
  - [ ] CRGreen names exact; no API drift.
  - [ ] No heavy measure proofs inside; only analytic packaging.

- CayleyAdapters
  - [ ] `abs_div`, `pow_two`, `ring_nf` used; no manual `.mp`.
  - [ ] Nonzero guards present for `field_simp`.
  - [ ] Add calculus lemmas before enabling kernel CoV wiring anywhere else.

- PoissonCayley
  - [ ] If CoV lemmas missing, keep M=2 builder path in use.
  - [ ] Keep any new CoV route behind a feature flag/wrapper so `Main` doesn’t depend on it until ready.

- PPlusFromCarleson
  - [ ] No mutual recursion between upgrade alias and concrete `(P+)` theorem.
  - [ ] Existence-level wrapper is the single source of truth; concrete Kξ theorem delegates to it.
  - [ ] Wiring uses `RS.local_pairing_bound_from_IBP_and_Carleson` and plateau witness.

#### Rollback strategy when a refactor fans out
- Prefer gating new routes (via-Cayley) and keep the known-good path (M=2) in `Main`.
- Land calculus lemmas and their unit tests in `CayleyAdapters` first, then flip `PoissonCayley` to consume them.
- After each edit, run the smallest build that exercises the change:
  - BoundaryWedge small loop
  - CayleyAdapters small loop
  - Full target only after both are green

#### Naming invariants (do not break)
- CRGreen: `RH.RS.boxEnergyCRGreen`, `RH.RS.pairing_whitney_analytic_bound`, `RH.RS.CRGreen_pairing_whitney_from_green_trace`, `RH.RS.sqrt_boxEnergy_bound_of_ConcreteHalfPlaneCarleson`.
- Do not unify `RS.boxEnergy` with `boxEnergyCRGreen`.
- Use `abs_div` (unqualified) and keep `Complex.abs_mul` where needed.

#### What we keep from the last days
- A cleaner `CayleyAdapters` algebra layer (ready for calculus lemmas).
- A stable `BoundaryWedge` façade with the right adapter names.
- A clear picture of how to reintroduce the CoV path without destabilizing the build: land calculus → enable transport → enable via‑cayley packagers → flip `Main`.


