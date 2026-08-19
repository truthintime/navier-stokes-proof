# Candidate inventory

This is a working extraction queue, not a claim that the listed files are already suitable for
Tau Ceti.  Roadmap layers refer to the incompressible-flows roadmap in
[Tau Ceti PR #237](https://github.com/TauCetiProject/TauCetiRoadmap/pull/237).

## Priority candidates

| source seed | roadmap layer | state | likely reusable result | required change |
|---|---:|---|---|---|
| [`MaxEnvelope.lean`](../lean/NSFormal/NSFormal/MaxEnvelope.lean) | supporting analysis | extractable | Lipschitz spatial maximum, compact maximizer set, and a Banach-valued Danskin/envelope theorem | Separate the smallest general API, compare with existing Mathlib extrema results, and avoid fluid-specific naming. |
| [`FlowAveraging.lean`](../lean/NSFormal/NSFormal/FlowAveraging.lean) | 3 | generalize first | Two-sided representation averages and positive Fejér weights | Tau Ceti already proves normalized local orbit-integral and generator-domain results for C0 semigroups. Isolate only genuinely new group/weighted-average content; split finite spectral diagnostics and research-facing corollaries. |
| [`FlowKoopman.lean`](../lean/NSFormal/NSFormal/FlowKoopman.lean) | 3 | generalize first | Strongly continuous `L²` Koopman group for a continuous measure-preserving flow and generator leakage bounds | Generalize the core beyond `Torus3`, use the shared flow/semigroup APIs, and move torus nonvacuity to examples. |
| [`PeriodicIntegration.lean`](../lean/NSFormal/NSFormal/PeriodicIntegration.lean) | 0--1 | extraction started | Periodic coordinate integration by parts and divergence-free transport skew-adjointness | The first smooth unit-torus seed is checked in [`ForTauCeti/PeriodicIntegration.lean`](../lean/NSFormal/NSFormal/ForTauCeti/PeriodicIntegration.lean); see [PERIODIC_INTEGRATION.md](PERIODIC_INTEGRATION.md). Next hide the half-open representative, cover arbitrary finite index types, and later extend by Sobolev density. |
| [`VectorCalculus.lean`](../lean/NSFormal/NSFormal/VectorCalculus.lean) | 1 and 5 | generalize first | Flat Jacobian/divergence/Laplacian algebra, convection-curl and curl-Laplacian identities | Split dimension-free flat operators, oriented three-dimensional identities, time-space calculus, and the Navier--Stokes application into separate modules. |
| [`DivCurl.lean`](../lean/NSFormal/NSFormal/DivCurl.lean) | 1 | generalize first | Pointwise gradient/curl algebra and the periodic integral identity `∫|∇u|² = ∫|curl u|²` for divergence-free fields | Remove its backwards import through `Enstrophy`; state the weak/general identity only after the Layer 0 API exists. |
| [`PeriodicSobolev.lean`](../lean/NSFormal/NSFormal/PeriodicSobolev.lean) and [`PeriodicSobolevEuclidean.lean`](../lean/NSFormal/NSFormal/PeriodicSobolevEuclidean.lean) | 0 | generalize first | Concrete Poincaré and `H¹ → L⁶` proofs on the three-torus | Treat as proof seeds.  Target intrinsic periodic Sobolev spaces, normalized Haar measure, arbitrary finite dimension where valid, and shared scalar/vector bridges. |

The selected pilot is periodic integration by parts.  The representation design risk is the
reason to start with its dossier and a small smooth theorem, rather than postponing the issue
until weak vector calculus depends on it.  Operator averages should wait for a precise
comparison with Tau Ceti's existing C0-semigroup orbit-integral API.

## Later comparison and regression work

| source seed | roadmap layer | state | role in the target development |
|---|---:|---|---|
| [`Domain.lean`](../lean/NSFormal/NSFormal/Domain.lean) | 0 | regression example | Compare the concrete period-`2π` `Torus3` with a rescaled `UnitAddTorus (Fin 3)` specialization; do not port it as a second root domain. |
| [`PeriodicCalculus.lean`](../lean/NSFormal/NSFormal/PeriodicCalculus.lean) | 1 and 6 | regression example | Test transport cancellation and the scalar maximum principle after intrinsic flat calculus exists. |
| [`TorusFlow.lean`](../lean/NSFormal/NSFormal/TorusFlow.lean) | 3 and 13 | regression example | Preserve the explicit nontrivial Haar-preserving shear, its curl generator, and its Koopman action as an exact example. |
| [`NavierStokes.lean`](../lean/NSFormal/NSFormal/NavierStokes.lean) | 5--6 | generalize first | Supply comparison theorems from the concrete classical predicate to the eventual solution dictionary; do not make the concrete predicate the root API. |
| [`KineticEnergy.lean`](../lean/NSFormal/NSFormal/KineticEnergy.lean) | 5 | blocked | Smooth kinetic-energy equality example after the target integration, solution, and differentiation APIs exist. |
| [`Enstrophy.lean`](../lean/NSFormal/NSFormal/Enstrophy.lean) | 1 and 5 | blocked | Smooth enstrophy balance and stretching-density comparison after the same substrate exists. |
| [`LocalizedHelicity.lean`](../lean/NSFormal/NSFormal/LocalizedHelicity.lean) | 1/13 or research | research only | Its explicit cancellation witness may become a Fourier regression example, but the retained-helicity interpretation remains part of the research program. |
| [`SpectralFlux.lean`](../lean/NSFormal/NSFormal/SpectralFlux.lean) and [`LambFlux.lean`](../lean/NSFormal/NSFormal/LambFlux.lean) | 12 or future turbulence work | research only | Retain finite-shell and Lamb-vector cancellation identities locally until a standard coarse-grained-energy API gives them an established library role. |

## No present implementation seed

The fact that the repository has many PDE identities must not hide its largest foundational
gaps.  There is currently no implementation here suitable to port directly for:

* intrinsic vector-valued periodic `W^{k,p}` or real-index `H^s` spaces;
* the Helmholtz--Leray projector, Hodge decomposition, pressure recovery, or Biot--Savart;
* heat and Stokes semigroups;
* mild, strong, distributional, Leray--Hopf, or suitable weak solution structures;
* Galerkin compactness, global weak existence, two-dimensional uniqueness, critical-space
  theory, or partial regularity;
* Littlewood--Paley, Besov, or paraproduct infrastructure.

Those are roadmap construction projects, not missing files to be recovered from this
repository.

## Material that stays local by default

The following families are not upstreaming priorities unless an independently standard lemma
is isolated from them:

* the 54 manuscript algebra certificates;
* `DynamicCriterion`, `ConcreteDynamicCriterion`, and the retained-amplitude continuation
  chain;
* `Anisotropy`, `AnisotropicIntegration`, `AnisotropicCriterion`, `DirectorTensor`, and
  `VortexStretching` depletion quantities;
* `Financing`, `Recurrence`, `FarField`, and the current filtered-flux stopping mechanisms;
* paper-specific episode, campaign, rigidity, and closure algebra.

Kernel checking is evidence that a stated implication was proved.  It does not by itself make
the statement established fluid theory, naturally generalized, or suitable for a shared
library.

## Cross-cutting dependency repairs

Several current imports encode discovery order rather than mathematical order.  Before a port,
at least these knots must be cut:

* `PeriodicSobolev → DivCurl → Enstrophy → NavierStokes`;
* `DivCurl → Enstrophy` for what should be a foundational vector identity;
* `VectorCalculus → NavierStokes` despite much of the file being elementary flat calculus;
* `TorusFlow → LocalizedHelicity` for an example whose basic flow theory is independent of the
  research criterion;
* `PeriodicCalculus → VorticityMaximum` for calculus facts that should not depend on a
  vorticity application.

The target fix is smaller modules with forward dependencies, not aliases around the same
graph.
