# Porting dossier: smooth periodic integration by parts

This dossier accompanies the first checked extraction seed in
[`NSFormal/ForTauCeti/PeriodicIntegration.lean`](../lean/NSFormal/NSFormal/ForTauCeti/PeriodicIntegration.lean).
It remains a design audit for the eventual Tau Ceti public API.

## Identification

* **Source file:**
  [`NSFormal/PeriodicIntegration.lean`](../lean/NSFormal/NSFormal/PeriodicIntegration.lean)
* **Principal source declarations:** `addCircle_integral_mul_deriv_eq_neg_deriv_mul_of_periodic`,
  `torus3_integral_mul_coordinateDerivative_eq_neg`,
  `torus3_transport_integration_by_parts`, and
  `torus3_divergenceFree_transport_skew`
* **Audited source commit:** `4daa9649e790893400ebbe6f5b805d13e7a6a6c7`
* **Roadmap layers:** 0 (periodic analytic substrate) and 1 (flat vector calculus)
* **Likely target modules:** `TauCeti/Analysis/Sobolev/Periodic.lean` for the derivative and
  integration substrate, with transport consequences in
  `TauCeti/Analysis/VectorField/Flat/Basic.lean`
* **First claim size:** smooth scalar coordinate integration by parts on `UnitAddTorus d`, plus
  one nonconstant Fourier-mode regression test
* **State:** smooth extraction seed implemented; public-API generalization remains
* **Human owner:** Ember Arlynx

## Mathematical provenance

The result is ordinary integration by parts on a compact flat torus.  The source proof reduces
it to the fundamental theorem of calculus on one period, cancels the periodic endpoint, then
uses Mathlib's volume-preserving product-coordinate equivalence and Fubini.  The proof method is
standard; the repository contribution is the checked assembly against the concrete
`AddCircle` and product-measure APIs.

The source currently credits the repository history rather than a standalone literature
reference.  A contribution should cite a standard Sobolev/PDE reference for the weak extension
and preserve the source commit and authorship in its porting note.

## Source statement

The strongest scalar source theorem fixes

```text
Torus3 = Fin 3 → AddCircle (2π)
```

and a coordinate `i : Fin 3`.  It assumes every one-dimensional coordinate lift of `f` and
`g` is `C¹`, together with integrability of both products needed by Fubini, and proves

```text
∫ x, f x * ∂ᵢ g x = -∫ x, (∂ᵢ f x) * g x.
```

The derivative is defined by choosing the standard half-open representative with
`AddCircle.liftIoc` and differentiating the periodic real lift.  Later source theorems prove the
Leibniz rule, sum over the three coordinates, retain the `f div u` term, and finally specialize
to a pointwise divergence-free field.

This is honest smooth calculus, but it is not a weak/Sobolev theorem and its slice-wise
hypotheses are an implementation presentation rather than the desired public interface.

## Target statement and staging

### Stage A: the one-circle lemma

Audit whether the already general source theorem

```text
addCircle_integral_mul_deriv_eq_neg_deriv_mul_of_periodic
```

belongs in Mathlib's `AddCircle` integration API.  It works for arbitrary positive period `T`
and depends only on Mathlib.  Its current integrands are expressed through `liftIoc`; an
upstream statement should instead use the best existing smooth-circle derivative API if one
exists.  No fluid-specific alias is needed.

### Stage B: smooth unit-torus calculus

For finite `d`, define or consume an intrinsic coordinate derivative on smooth scalar fields on
`UnitAddTorus d` and prove

```text
∫ x, f x * partial i g x = -∫ x, partial i f x * g x.
```

The public hypotheses should be a recognized smoothness class which implies the required
measurability and integrability on the compact torus.  Dimension three is a specialization,
not part of the root declaration.  The transport theorem follows only after a dimension-free
flat gradient/divergence API fixes how a vector field is represented.

### Stage C: weak extension

After periodic Sobolev spaces and density of trigonometric polynomials exist, extend the
identity to conjugate Sobolev exponents and identify weak divergence as the negative adjoint of
gradient.  Stage C is a separate claim; the smooth port must not simulate it with pointwise
representatives of equivalence classes.

### Source specialization

The period-`2π` result should follow from the unit-torus result through the roadmap's rescaling
map.  If `y = x / (2π)`, then the source physical derivative and the unit derivative satisfy

```text
partial_x = (2π)⁻¹ partial_y.
```

The same factor occurs on both sides of integration by parts.  The measure changes from
physical Haar volume to normalized Haar probability; this common volume factor also cancels.
The comparison must be proved rather than treated as definitional equality.

## Representation and normalization audit

- [x] Replace the fixed `Fin 3 → AddCircle (2π)` theorem with a checked
      `UnitAddTorus (Fin (n + 1))` theorem in arbitrary positive finite dimension. General
      finite index types remain a target-API task.
- [x] Use normalized Haar measure of total mass one in the extraction theorem.
- [x] Prove that the constant/zero mode has coordinate derivative zero.
- [x] Verify on the first real sine/cosine mode that the unit-torus derivative carries `2π`;
      the complex statement is multiplication by `2π i kᵢ`, while the
      period-`2π` source derivative has multiplier `i kᵢ`.
- [ ] Avoid exposing the choice of half-open representative in the public derivative API.
- [x] Keep the Fubini integrability obligations explicit in the first extraction theorem.
- [x] Keep the real scalar theorem primary; complex and finite-dimensional vector forms should
      follow through a principled scalar-extension API.
- [ ] Do not evaluate weak equivalence classes pointwise in Stage C.

Pressure, viscosity, the Laplacian sign, and flow-pullback direction do not enter this first
claim.

## Dependency audit

### Existing Mathlib substrate

The checked source already consumes:

* `AddCircle.integral_liftIoc_eq_intervalIntegral`;
* periodic real lifts and `AddCircle.liftIoc`;
* `MeasurableEquiv.piFinSuccAbove` and `volume_preserving_piFinSuccAbove`;
* product-volume Fubini;
* the interval fundamental theorem of calculus;
* `UnitAddTorus.mFourier` and its normalized Haar/Fourier infrastructure for future tests.

The implementation audit must search the target Mathlib pin for a smooth derivative on
`AddCircle` or a torus Lie-group/manifold derivative before introducing one.

### Existing Tau Ceti substrate

Tau Ceti's PDE roadmap owns weak-derivative spaces and the scalar `W^{k,p}` hierarchy.  This
claim should coordinate with those definitions; it must not create a local weak Sobolev space.
No existing Tau Ceti theorem found in the initial audit supplies periodic coordinate
integration by parts.

### Source dependencies to discard

The source imports only `NSFormal.Domain`, but that file fixes `Torus3`, `Vec3`, continuous-map
aliases, and the physical period.  None should become a dependency of the target result.  The
three-factor anisotropic product lemma is a downstream research consumer and is not part of
the first contribution.

## Proof-transfer plan

1. [x] Search the target pins for the derivative and `AddCircle` integration interfaces.
2. [x] Isolate the general one-period interval/circle lemma. Decide during Tau Ceti review
   whether its final natural home is
   Mathlib or Tau Ceti.
3. [x] Define the smallest smooth unit-torus coordinate derivative after finding no shared
   smooth `AddCircle` derivative in the current pins. Its half-open implementation remains
   hidden only by namespace convention, not yet by the final public API.
4. [x] Generalize the coordinate-split/Fubini proof from `Fin 3` to `Fin (n + 1)`.
5. [x] Prove the scalar integration-by-parts identity.
6. [x] Add the constant and first nonzero real Fourier-mode normalization tests.
7. Only then build the transport/divergence corollary in the flat-vector-field module.

The first PR should stop after steps 1--6 unless the transport corollary is genuinely small
under the resulting API.

## Guardrails and negative tests

* A constant mode differentiates to zero.
* The first Fourier mode gets the `2π` factor and the chosen imaginary-unit sign.
* Periodic integration by parts has no boundary term.
* Poincaré is not asserted here, and later requires subtracting the mean.
* Slice-wise classical differentiability is not advertised as a weak derivative theorem.
* A half-open fundamental-domain representative is not presented as a canonical pointwise
  representative of an `Lp` class.

## Exact examples

The source already proves a nonconstant sine/cosine example on the period-`2π` circle.  The
target regression should use the real and imaginary parts of the first unit-torus Fourier mode,
equivalently `sin (2πx)` and `cos (2πx)`, and verify both the derivative normalization and the
integration-by-parts sign.  A second test should use a function independent of coordinate `i`
and obtain derivative zero.

## Verification checklist

- [ ] Focused target module builds on Tau Ceti's committed pins.
- [ ] Full affected Tau Ceti build passes.
- [ ] No new `sorry`, axioms, or alternate verifier assumptions.
- [x] Unit-torus real first-mode normalization tests pass.
- [ ] A proved rescaling/comparison theorem recovers the source convention, or its dependency
      is recorded as a follow-up rather than asserted informally.
- [ ] Module documentation states dimension, measure normalization, scalar field, and
      differentiability class.
- [ ] Porting attribution and AI-assistance disclosure are accurate.

## Local disposition

Keep `NSFormal/PeriodicIntegration.lean` as a period-`2π` comparison and regression source until
its consumers migrate.  Do not delete or mechanically rewrite it as part of the first Tau Ceti
claim.  Once the target API is stable, add explicit comparison theorems here and simplify
downstream imports incrementally.
