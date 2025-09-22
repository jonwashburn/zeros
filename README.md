# zeros — Lean 4 artifact and verification

This repository contains a Lean 4 artifact that, given a single CR‑outer “local removable data” chooser at each ζ‑zero on Ω, produces Mathlib’s `RiemannZeta.RiemannHypothesis` as a formal theorem.

• Entry point (one input → final result)
  - File: `no-zeros/rh/Proof/Entry.lean`
  - Theorem: `RH.Proof.Entry.RiemannHypothesis_from_CR_outer`
  - Input:
    ```lean
    choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ)
    ```
  - Output: `RiemannHypothesis`

## Reproduce (local)

```bash
cd no-zeros
lake update
lake build
```

Conservative build (low memory): set `LEAN_EXTRA_ARGS="-j2 -M 4096"`.

## Axioms check

To build and print axioms for public theorems:

```bash
bash scripts/verify_axioms.sh
```

This invokes `lake build +rh.Proof.AxiomsCheck`, which contains `#print axioms` statements for the final exports and public shims.

## CI

GitHub Actions workflow `.github/workflows/axioms.yml` builds the project and runs the axioms check on pushes to `main` and `pinned-cdc6632`.

## License

See `no-zeros/LICENSE`.
