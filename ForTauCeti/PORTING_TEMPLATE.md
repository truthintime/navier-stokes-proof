# Porting dossier: `<candidate>`

Copy this file when a candidate is selected.  Complete it before or alongside the first Tau
Ceti implementation PR.  Delete instructions that do not apply, but do not omit a boundary
merely because the source code made it implicit.

## Identification

* **Source file and declarations:**
* **Source commit:**
* **Roadmap layer and target module:**
* **Proposed Tau Ceti claim size:**
* **State:** extractable / generalize first / regression example / blocked
* **Human owner:**

## Mathematical provenance

* Standard name of the result:
* Literature or upstream-library references:
* Original proof authors and contributors:
* What, if anything, was discovered specifically in this repository:

## Statement comparison

### Source statement

Describe the exact types and hypotheses.  Link to the declarations; do not summarize away
regularity, integrability, finiteness, or nonzero assumptions.

### Target statement

State the proposed generalization and why each extra degree of generality is natural.  Record
anything intentionally *not* generalized.

### Specialization theorem

Explain how the target theorem recovers the source result.  If it does not, say which source
hypothesis or convention prevents the comparison.

## Representation and normalization audit

Check every applicable item.

- [ ] `UnitAddTorus d` versus period-`2π` `Torus3`
- [ ] normalized Haar measure versus physical-volume measure
- [ ] real fields versus Fourier complexification and preservation of the real form
- [ ] Fourier exponent and derivative multiplier
- [ ] treatment of the zero/constant mode
- [ ] `Δ = div grad` and the resulting heat/Stokes signs
- [ ] forward versus inverse flow pullback
- [ ] pressure representative or quotient normalization
- [ ] weak equivalence classes versus selected pointwise representatives
- [ ] two-dimensional scalar versus three-dimensional vector vorticity
- [ ] viscosity positivity and the separate Euler case

## Dependency audit

* Existing Mathlib declarations to consume:
* Existing Tau Ceti declarations to consume:
* Source imports that are accidental or too strong:
* Missing upstream dependencies:
* Proposed module split and import direction:

No local alias should conceal a missing shared abstraction.  Record an upstream API gap in the
roadmap or a dedicated issue.

## Proof-transfer plan

Identify which parts of the source proof are reusable, which are coordinate calculations that
should become implementation lemmas, and which must be replaced by a shared theorem.  Keep the
first contribution to one coherent definition family and one or two independently useful
theorems.

## Guardrails and negative tests

List the nearest false statements and how tests exclude them.  Examples include deleting the
constant Leray mode, asserting Poincaré without subtracting the mean, claiming operator-norm
continuity of Koopman evolution, using the wrong pullback sign, or differentiating a weak
energy inequality.

## Exact examples

Name at least one nonzero or nonconstant example and the exact identity it should verify.
Prefer transverse Fourier modes, periodic shears, Taylor--Green vortices, or another example
whose signs and normalization are inspectable.

## Verification

- [ ] Focused Tau Ceti target builds.
- [ ] Full affected Tau Ceti build passes.
- [ ] No new `sorry`, custom axioms, or opaque verifier assumptions.
- [ ] Source specialization/comparison test passes where applicable.
- [ ] Documentation states data, dimension, domain, and uniqueness/regularity class.
- [ ] AI-assistance and human-ownership disclosure is accurate.

## Attribution and disposition

Record commit authorship, co-authorship or `Co-authored-by` trailers where appropriate, license
compatibility, and links back to the source.  Finally state whether the local source should
remain as a regression example, be deprecated after migration, or continue independently as a
research experiment.
