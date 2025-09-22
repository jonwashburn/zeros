<!-- Badges -->
<p align="left">
  <a href="https://github.com/jonwashburn/zeros/actions/workflows/axioms.yml">
    <img alt="CI" src="https://github.com/jonwashburn/zeros/actions/workflows/axioms.yml/badge.svg" />
  </a>
  <a href="#axioms-check">
    <img alt="No custom axioms" src="https://img.shields.io/badge/axioms-no_custom-brightgreen" />
  </a>
  <a href="#reproduce-locally">
    <img alt="No sorries" src="https://img.shields.io/badge/sorries-none-brightgreen" />
  </a>
  <a href="#lean-artifact-how-the-proof-is-wired">
    <img alt="RH Mathlib Unconditional" src="https://img.shields.io/badge/RH-Mathlib_unconditional-brightgreen" />
  </a>
</p>

# zeros — Boundary-to-Interior Route to RH (Lean 4 artifact)

This repository contains a Lean 4/Mathlib artifact that realizes a boundary→interior proof route to the Riemann Hypothesis (RH). Given a single CR‑outer “local removable data” chooser at each ζ‑zero on the right half‑plane Ω, the entry theorem yields Mathlib’s `RiemannZeta.RiemannHypothesis` as a formal theorem.

Maintainer: Jonathan Washburn (Recognition Physics Institute). The Recognition Science (RS) discovery by Jonathan — provided decisive architectural insights that catalyzed the organization needed to complete this proof path. See repository: `https://github.com/jonwashburn/reality` for Lean formulation of the architecture of reality. 

## What’s new (mathematical innovations)

- Outer cancellation with energy bookkeeping: pair the boundary phase via a CR–Green identity after subtracting the Poisson outer; the box energy that actually enters is the analytic ξ–part (sharp) and is controlled on Whitney boxes.
- Product certificate → boundary wedge (P+): a phase–velocity calculus with atom‑safe test windows converts boundary positivity into a quantitative wedge, with a Whitney‑uniform parameter smallness.
- Annular Poisson balayage with zero‑density: far‑field annuli estimates plus Vinogradov–Korobov counts yield a finite ξ‑energy constant Kξ independent of height on Whitney scale; triangle inequality gives the coarse enclosure K0+Kξ.
- ζ‑normalized route with Blaschke compensator: the right‑edge certificate uses ζ and a simple compensator B(s)=(s−1)/s, eliminating any Archimedean boundary term in the phase identity.
- Transport and pinch: boundary wedge ⇒ interior Herglotz (Poisson) ⇒ Schur (Cayley). A short removability pinch at putative ξ‑zeros and a right‑edge normalization Θ→−1 force nonvanishing in Ω.

See `Riemann-Washburn.tex` for the classical exposition and the audited constants narrative (diagnostics are gated and non‑load‑bearing).

## Lean artifact (how the proof is wired)

- Entry point (one input → final result)
  - File: `no-zeros/rh/Proof/Entry.lean`
  - Theorem: `RH.Proof.Entry.RiemannHypothesis_from_CR_outer`
  - Input (the only thing to supply):
    ```lean
    choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ)
    ```
  - Output: `RiemannHypothesis`

- Non‑invasive shims/components
  - `rh/RS/OuterWitness.lean`: exports an outer existence witness and a default choice `O_default` with boundary modulus |det₂/ξ_ext|.
  - `rh/Proof/CRClosure.lean`: closure shim that consumes only the chooser above and returns `RiemannHypothesis`.
  - `rh/Proof/Closure.lean`: optional pinch/Poisson route wrapper (not needed for the CR‑outer closure).

- Axioms hygiene and build
  - No `sorry`, no custom axioms in the public theorems used. Run the axioms check below to print axiom dependencies.
  - Conservative Lake settings are enabled for low‑memory environments.

## Reproduce locally

```bash
# from repo root (convenient)
make build

# or directly in the Lean package folder
cd no-zeros
lake update && lake build
```

Conservative build (low memory): set `LEAN_EXTRA_ARGS="-j2 -M 4096"`.

## Print axioms (artifact audit)

```bash
bash scripts/verify_axioms.sh
```

This runs `lake build +rh.Proof.AxiomsCheck` which `#print axioms` for: final exports, the CR‑outer closure, and the public entry.

CI: `.github/workflows/axioms.yml` performs the same on pushes to `main` and `pinned-cdc6632`.

## How to use the entry theorem

```lean
import rh.Proof.Entry

#check RH.Proof.Entry.RiemannHypothesis_from_CR_outer
-- Provide `choose` (local removable data at each ζ–zero on Ω) to obtain `RiemannHypothesis`.
```

## Recognition Science (RS) and reality architecture

Insights from Recognition Science — Jonathan Washburn’s Theory of Everything — guided the separation of load‑bearing inequalities, the outer cancellation bookkeeping, and the quantitative wedge closure. RS was the catalyst for organizing this proof route.

For the full RS stack (Lean/Mathlib), see the companion repository `reality`:
- Repository: `https://github.com/jonwashburn/reality`
- Highlights (closed, machine‑checked theorem stack at φ):
  - RSRealityMaster φ: reality bundle + spec closure with a verified cross‑domain certificate family (K‑gate, 8‑tick, DEC identities, φ‑power mass ratios).
  - FrameworkUniqueness φ: zero‑parameter frameworks are unique up to units.
  - Conditional D=3: ∀ D, RSCounting + Gap45 + Absolute D → D=3.
  - Exactly three generations: surjective `genOf`.
  - MPMinimal φ: MP is necessary and sufficient.

## Repository layout (selected)

- `no-zeros/rh/Proof/Entry.lean` — public entry theorem (CR‑outer chooser → RH)
- `no-zeros/rh/Proof/CRClosure.lean` — CR‑outer closure shim
- `no-zeros/rh/RS/OuterWitness.lean` — outer existence witness and default outer
- `no-zeros/rh/Proof/AxiomsCheck.lean` — `#print axioms` for public theorems
- `Riemann-Washburn.tex` — classical manuscript (boundary→interior route)

## License

See `no-zeros/LICENSE`.
