RH formalization progress (auto-maintained)

What changed
- Added minimal disk Poisson scaffolding in `rh/academic_framework/DiskHardy.lean`.
- Added Cayley geometry helpers and a structural bridge in `rh/academic_framework/CayleyAdapters.lean`.

Why
- Prepare to remove the vendor Poisson identity by proving disk → half-plane Poisson for Re via Cayley.

Next steps
- Prove disk→half-plane Poisson re_eq on S and pass as `hReEq` to `pinch_representation_on_offXi_M2`.
- Verify callers compile clean with the new signature; fix any fallout.

---

Build attempt (2025-09-19)

- Current status: build fails in `rh/academic_framework/HalfPlaneOuter.lean` and `rh/RS/PoissonPlateau.lean`.
- HalfPlaneOuter highlights:
  - Duplicate lemma definitions later in file: `poissonKernel_integrable` and `integrable_boundary_kernel_of_bounded` are redeclared; remove or unify one copy.
  - Several inequality proof blocks need normalization (use nonneg versions and align both sides), and deprecated/division lemmas should be replaced with modern variants to match hypotheses.
- PoissonPlateau highlights:
  - Two lower-bound steps compare constants with an interval integral; rewrite both sides to the same `(2*b)` length form before final simplification to avoid shape mismatches.
- No axioms or sorries found; many modules are Prop-level interfaces by design.

Planned fixes
- Deduplicate the two lemmas in HalfPlaneOuter and normalize the inequality block around kernel domination; then re-run `lake build`.
- Align constant shapes in PoissonPlateau’s two set-integral bounds (use consistent `(volume Icc).toReal` or explicit `2*b` everywhere).

