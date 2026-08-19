# Preparing work for Tau Ceti

This directory is the promotion boundary between the exploratory development in this
repository and the reusable incompressible-flow library proposed in
[Tau Ceti roadmap PR #237](https://github.com/TauCetiProject/TauCetiRoadmap/pull/237).

The two repositories have different jobs.

* `navier-stokes-proof` may experiment with a concrete period-`2π` three-torus, inspect the
  source paper, test new analytic reductions, and build unusually specialized witnesses.
* Tau Ceti should receive established mathematics stated at its natural generality, against
  shared APIs and conventions, with reviewable dependencies and regression tests.

Code is therefore not copied into this directory merely because it compiles.  A candidate is
first classified in [CANDIDATES.md](CANDIDATES.md), then given a dossier based on
[PORTING_TEMPLATE.md](PORTING_TEMPLATE.md).  The first such audit is
[PERIODIC_INTEGRATION.md](PERIODIC_INTEGRATION.md).  Generalized implementation normally
happens in a Tau Ceti branch, while this repository retains attribution, comparison theorems,
and concrete tests.

The first checked extraction seed lives at
[`NSFormal/ForTauCeti/PeriodicIntegration.lean`](../lean/NSFormal/NSFormal/ForTauCeti/PeriodicIntegration.lean).
It is intentionally limited to smooth scalar calculus and normalization tests.

## What the roadmap changes here

The roadmap separates three work streams which had previously been interleaved.

### 1. Reusable foundations

These are established results which may become Tau Ceti or, eventually, Mathlib material:

* periodic integration by parts, Poincaré, and Sobolev infrastructure;
* flat vector calculus and div--curl identities;
* incompressible flow, Koopman groups, and their generators;
* classical Navier--Stokes/vorticity comparison results and smooth balance laws;
* general analytic tools, such as maximum envelopes, when they have an independent API.

The existing files are proof seeds and regression tests.  They are not yet the target API:
many use `Torus3 = Fin 3 → AddCircle (2 * π)`, continuous representatives, coordinate lifts,
or imports from much later parts of the experimental development.  The Tau Ceti target uses
`UnitAddTorus d`, normalized Haar measure, weak/Sobolev objects, and dimension-independent
operators wherever the mathematics permits.

### 2. Research instruments

The depletion, retained-amplitude, filtered-flux, recurrence, and rigidity investigations stay
here while their mathematical status is being determined.  A lemma discovered in that work
may be promoted if it becomes an independently useful established result, but a research
strategy is not smuggled into Tau Ceti as infrastructure.

### 3. Manuscript verification

The original algebraic certificates and the formal audit of the paper remain part of this
repository's historical and verification record.  They are not a Tau Ceti library lane merely
because they are kernel checked.

## Promotion states

Every candidate has one of the following states.

| state | meaning |
|---|---|
| **extractable** | The mathematical result and proof are reusable; only ordinary API adaptation and review remain. |
| **generalize first** | The proof is useful, but its statement or representation is too specific for the target library. |
| **extraction started** | A checked target-shaped seed exists here, but its public Tau Ceti API and upstream review are incomplete. |
| **regression example** | Keep the concrete theorem as an end-to-end test of the generalized API rather than as its implementation. |
| **blocked** | A named roadmap dependency, such as periodic Sobolev or Leray projection infrastructure, does not yet exist. |
| **research only** | The result belongs to the open analytic investigation and is not currently a public-library claim. |
| **certificate only** | The result verifies manuscript algebra and has no identified independent library role. |

States describe readiness, not mathematical importance.  They may change after dependency and
literature review.

## Promotion gate

A Tau Ceti contribution should satisfy all of the following.

1. **Established scope.** Its statement is known mathematics or honest foundational
   infrastructure.  It does not imply that three-dimensional global regularity has been
   proved.
2. **Natural generality.** Dimension, period, scalar field, measure normalization, and
   regularity are no more specialized than the proof requires.
3. **Shared representation.** It consumes Tau Ceti/Mathlib Sobolev, distribution, flow,
   semigroup, and torus APIs instead of exporting a parallel hierarchy.
4. **Dependency discipline.** General vector calculus cannot import enstrophy, and periodic
   Sobolev theory cannot depend on a Navier--Stokes solution record merely because the original
   experiment developed in that order.
5. **Normalization audit.** Fourier signs, zero modes, Haar mass, Laplacian sign, pressure
   normalization, transport direction, and viscosity assumptions are explicit and tested.
6. **Representative discipline.** Weak `Lp` and Sobolev classes are not evaluated pointwise;
   a representative is selected only through a theorem that justifies it.
7. **Provenance.** The source module, source commit, mathematical references, authorship, and
   the exact generalization from the source theorem are recorded.
8. **Verification.** The focused target and the full affected library build, with no new
   axioms or placeholders.  Exact examples exercise the important signs and edge cases.
9. **Human ownership.** The contributor can explain and maintain the statement, design, and
   proof even when AI assisted with research or implementation.

## Immediate sequence

The first useful work here is not another monolithic Navier--Stokes layer.  It is to make the
existing proof seeds separable.

1. Audit and split general operator/coordinate algebra away from PDE-specific imports.
2. Use the concrete period-`2π` results to specify comparison and regression theorems for
   `UnitAddTorus d`; do not make a second public torus API.
3. Select one small extraction claim and complete its dossier before opening implementation
   work in Tau Ceti.
4. Preserve concrete shear, Fourier-mode, and classical-solution examples as end-to-end tests.
5. Feed any API obstruction found during the port back into the roadmap rather than hiding it
   behind a local alias.

The current best pilot is the smooth periodic integration-by-parts result.  It is central to
the analytic spine, has a concrete nonconstant test, and forces us to settle the
period-`2π`/unit-torus derivative normalization before weak theory builds on it.  It must be
restated intrinsically on `UnitAddTorus d`, not copied under a new namespace.

The generic averaging and Koopman files remain valuable later candidates, but Tau Ceti already
has normalized semigroup-orbit integrals and generator-domain theorems.  Their dossier must
identify the genuinely new two-sided group/Koopman content instead of upstreaming a parallel
average construction.

## Non-goals

This directory is not:

* a claim that the present repository formalizes the Millennium problem;
* a vendored copy of Tau Ceti;
* a second Lake project with drifting Mathlib pins;
* a promise that every existing theorem should be upstreamed;
* a place to rename project-specific definitions while leaving their dependency structure
  unchanged.

The success condition is a small number of well-factored, independently useful contributions,
plus an honest record of which experiments should remain local.
