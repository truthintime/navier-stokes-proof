# Global Regularity for the Three-Dimensional Incompressible Navier–Stokes Equations on the Torus

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21959161.svg)](https://doi.org/10.5281/zenodo.21959161)
[![lean-verify](https://github.com/truthintime/navier-stokes-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/truthintime/navier-stokes-proof/actions/workflows/lean.yml)

**Jeffrey S. Cambria** · ORCID [0009-0008-4226-2099](https://orcid.org/0009-0008-4226-2099) · truthintime@tuta.io

This is the verification companion to the paper

> *Global Regularity for the Three-Dimensional Incompressible Navier–Stokes Equations
> on the Torus* — [doi:10.5281/zenodo.21959161](https://doi.org/10.5281/zenodo.21959161)

which proves global regularity for the spatially periodic case — statement (B) of the
official Clay Millennium formulation: every smooth, divergence-free initial velocity
field on the torus T³, with positive viscosity and zero external force, evolves into a
unique global smooth solution.

## Erratum — resolved in v002 (2026-08-17)

The first external review of this repository
([PR #1](https://github.com/truthintime/navier-stokes-proof/pull/1), ember arlynx)
identified a genuine error in the paper as published: the display D_t|ω| = α|ω| in
§3.1 is the *inviscid* identity — for ν > 0 the correct identity is
D_t|ω| = α|ω| + ν ξ·Δω — and the per-trajectory chain (§16.2) and the localization
step (§10, Step 3) rely on the defective shorthand as written. The author has
verified the finding independently (derivation and numerics). The omitted viscous
term has a favorable sign at spatial maximizers, and the repair — recasting the
chain on the maximum envelope ‖ω(t)‖∞, whose analytic skeleton is machine-checked in
the community formalization contributed in the same PR — is being carried out for a
revised version (v002) of the paper.

**v002 is published (2026-08-17, same DOI, new version) and closes this erratum.**
The chain is recast on the maximum envelope exactly as planned — and the revision
went far beyond the single repair: an internal adversarial review produced fifteen
graded findings, all of which are closed in v002 (five structural holes closed by
derivation or principled retirement — the concentration-dichotomy funnel with a
self-similar rigidity endgame, the circulation-floor ledger with derived
Γ_min and c_E, the seeded episode class, the averaging lemma, and the
fixed-dissipation reduction of the linear theory's load — plus ten smaller
findings). The full version note is in the paper; v001 remains available under
the same concept DOI as the superseded version.

**What is claimed, precisely.** The proof in the paper (v002) is a closed analytic
argument. The exact and algebraic core of that argument — every closed-form
identity, sign, coefficient chain, closure inequality, and evaluated integral the
lemmas rest on — is machine-verified here: **89 kernel-checked Lean 4 theorems,
zero unproven placeholders, over a pinned unmodified Mathlib** (the original 54,
the 16 v002 repair certificates, and the 19 closure-wave certificates). A
certified-numerics layer (`code/numerics_*.py`) additionally archives explicit
upper bounds for the named kernel, embedding, and threshold constants — proved
tail majorants, outward rounding; the paper consumes none of these values. The numerical instruments are supporting, not load-bearing: they motivated
and cross-checked the lemmas, but no step of the proof consumes a numerical result.
The analytic layer is rigorous prose in the paper; the machine certificates
strengthen it and do not substitute for any part of it.

**The community formalization layer.** Beginning with PR #1 (ember arlynx), the
repository also hosts an in-progress formalization of the PDE-level argument itself:
**978 additional kernel-checked theorems**, for **1067 theorems total**. This layer is
distinct from the paper's 89 certificates and does **not** prove global regularity.

“Custom formalization” here means new definitions and proofs written in ordinary
Lean. It does not mean a custom verifier: every declaration is checked by the stock
pinned Lean kernel over an unmodified Mathlib, with no project axioms or proof
placeholders.

The development now derives the vector-vorticity equation, periodic integration
identities, kinetic-energy and enstrophy balances, periodic Sobolev estimates, and
conditional continuation bounds directly from concrete classical Navier–Stokes
predicates. It reduces the remaining nonstandard input to a scale-critical dynamic
depletion estimate for a concrete self-transport quotient or its signed production
correlation.

The newest modules test that reduction rather than assuming it away. They prove a
localized-helicity obstruction to saturation, exhibit an explicit smooth periodic
curl field where global helicity cancels but localized helicity detects a strict gap,
and formalize finite vorticity-line averaging and its mean-ergodic limitation. A
strongly continuous Koopman layer now constructs the actual `L²` average without
assuming operator-norm continuity and proves an explicit `2‖h‖₂/L` generator-leakage
bound for the positive Fejér weight. A nontrivial Haar-preserving shear on `T³`,
generated by an explicit nonzero periodic curl, now verifies the construction on
moving torus dynamics and identifies its pointwise generator with `w·∇`. The
resulting retained-amplitude continuation criterion is kernel-checked, but the
Navier–Stokes-specific estimate that would make it unconditional remains open. See
`FORMALIZATION.md`, `RESEARCH.md`, and `DYNAMICS.md` for the dependency map, audit,
and active research targets.

The first `ForTauCeti` extraction module now separates the general one-period
integration-by-parts kernel from the paper-specific dependency graph. It generalizes the smooth
scalar coordinate theorem to normalized `UnitAddTorus (Fin (n + 1))`, proves the constant-mode
gate, and checks the unit-period `2π` Fourier derivative normalization on nonconstant
sine/cosine modes. This is reusable smooth infrastructure, not weak solution theory.

## Contents

| path | contents |
|---|---|
| `paper/v001/` | the published paper v001: source (`main.tex`, `refs.bib`) and the published PDF |
| `paper/v001/zenodo-v001-r4/` | v001's frozen artifacts as published on Zenodo, with SHA-256 manifests and OpenTimestamps `.ots` receipts (paper files carry the `-v001` suffix locally; the Zenodo v1 record predates the naming convention) |
| `paper/v002/` | **the current paper v002**: source (`main.tex`, `refs.bib`) |
| `paper/v002/zenodo-v002-r1/` | v002's frozen artifacts as published on Zenodo (2026-08-17): `global-regularity-navier-stokes-torus-v002.pdf`, the Lean formalization zip, frozen source copies, SHA-256 manifests, and completed Bitcoin-attested `.ots` receipts |
| `lean/NSFormal/` | the Lean 4 + Mathlib development — `lake build` re-verifies all 1067 current theorems |
| `FORMALIZATION.md` | the full-formalization dependency map and current PDE-level proof obligations |
| `RESEARCH.md` | the independent analytic audit, rigorous replacement reduction, and active research program |
| `DYNAMICS.md` | the energy-paid filtered near/far theorem, cubic heat-flux reduction, and dynamic scale-variation target |
| `ForTauCeti/` | extraction queue, portability audit, and provenance dossiers for work intended to mature through Tau Ceti |
| `code/` | the symbolic-adjudication scripts (`sympy_*.py`) and calibrated numerical instruments cited by the paper (see `code/README.md`) |
| `results/` | the archived output log of every script in `code/` |

## Verify the Lean development yourself

The Mathlib dependency is **never modified** — it is pinned by exact version
(`v4.33.0`) in `lean/NSFormal/lakefile.toml` and `lake-manifest.json`; the pinned Lean
toolchain is installed automatically from `lean-toolchain` by
[elan](https://github.com/leanprover/elan). All theorems live in our own files under
`lean/NSFormal/NSFormal/` — the paper's 89 certificates (mapped display-by-display in
Appendix C of the paper) and the community formalization files (inventoried in
`lean/NSFormal/README.md`). To verify:

```
cd lean/NSFormal
lake exe cache get   # one-time: downloads the pinned Mathlib's prebuilt cache
lake build           # kernel-verifies every theorem
```

A successful build with no `sorry` warnings is the verification. Appendix C of the
paper maps the 89 paper certificates display-by-display; the community files are
inventoried in `lean/NSFormal/README.md`. The same build runs in CI on every commit
(`.github/workflows/lean.yml`).

## Reproduce the instruments

Python 3.12 with `numpy` + `scipy` + `sympy` only; every script is self-contained and
deterministic, and prints its registered gates with named outcomes:

```
python3 code/<script>.py        # regenerates its log in results/
```

`code/README.md` is the manifest: what each instrument measures, and which certificate
family each `sympy_*.py` script adjudicates.

## Integrity

`paper/v001/zenodo-v001-r4/MANIFEST.sha256` and
`paper/v002/zenodo-v002-r1/MANIFEST.sha256` fix the exact bytes of the published
artifacts of each version; the accompanying `.ots` files are OpenTimestamps receipts
anchoring those bytes in the Bitcoin blockchain (verify with `ots verify
<file>.ots`; both versions' receipts carry completed block attestations). The
repository state at each publication is permanently addressable at the git tags
[`paper-v001`](https://github.com/truthintime/navier-stokes-proof/tree/paper-v001)
and
[`paper-v002`](https://github.com/truthintime/navier-stokes-proof/tree/paper-v002).

## License and citation

CC BY 4.0 (see `LICENSE`). To cite, use `CITATION.cff` or cite the paper directly via
[doi:10.5281/zenodo.21959161](https://doi.org/10.5281/zenodo.21959161).
