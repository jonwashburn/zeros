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

- Current status: build fails in `rh/academic_framework/HalfPlaneOuter.lean` (37 errors remaining after partial fixes).
- HalfPlaneOuter Lean 4.13.0 migration:
  - Partially fixed: Reverted incorrect automated changes (div_le_div_of_nonneg → div_le_div_of_pos where appropriate)
  - Partially fixed: Updated measurability constructions with hdenom intermediate variables
  - Fixed: Restored poissonKernel_integrable and integrable_boundary_kernel_of_bounded that were mistakenly removed
  - Still needed: Fix remaining pow_le_pow_left argument order issues, application type mismatches, and type synthesis failures
- PoissonPlateau highlights:
  - Two lower-bound steps compare constants with an interval integral; rewrite both sides to the same `(2*b)` length form before final simplification to avoid shape mismatches.
- No axioms or sorries found; many modules are Prop-level interfaces by design.

Planned fixes
- Complete Lean 4.13.0 migration for HalfPlaneOuter: fix remaining 37 errors focusing on pow_le_pow functions and type synthesis
- Align constant shapes in PoissonPlateau's two set-integral bounds (use consistent `(volume Icc).toReal` or explicit `2*b` everywhere).

