RH formalization progress (auto-maintained)

What changed
- Added minimal disk Poisson scaffolding in `rh/academic_framework/DiskHardy.lean`.
- Added Cayley geometry helpers and a structural bridge in `rh/academic_framework/CayleyAdapters.lean`.

Why
- Prepare to remove the vendor Poisson identity by proving disk → half-plane Poisson for Re via Cayley.

Next steps
- Prove disk→half-plane Poisson re_eq on S and pass as `hReEq` to `pinch_representation_on_offXi_M2`.
- Verify callers compile clean with the new signature; fix any fallout.

