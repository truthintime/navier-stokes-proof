# Formalization status

The checked Lean library in `lean/NSFormal` now includes a concrete period-`2π`
three-torus, continuous scalar and vector fields on it, compact spatial maxima,
measure-theoretic budget estimates, and corrected pointwise and maximum-envelope
vorticity evolution theorems.  It also defines first and second coordinate
derivatives through the canonical periodic lift to `ℝ³`, concrete gradient,
divergence, curl, transport, stretching, and vector-Laplacian operators, and a
pointwise classical Navier--Stokes predicate.  It also constructs the actual Haar-volume
integral on coordinate circles, proves the volume-preserving product split of `T³`, and derives
the full scalar transport integration-by-parts formula and its divergence-free corollary.  It
does **not** yet define velocity or
pressure Sobolev regularity classes, the Leray projection, suitable weak solutions,
vortex tubes, episode boundaries, or a blow-up criterion.

The active mathematical strategy is now the independent audit and replacement program in
`RESEARCH.md` and `DYNAMICS.md`, not completion of the manuscript's tube/episode chain.  The
current target is the positive scale variation of cubic kinetic-energy flux left after a
global filtered estimate pays resolved stretching at the scale
\((1+\Omega)^{-1/3}\), either through the geometric near/far split or the simpler global
integration-by-parts estimate (4.3)--(4.6) of `DYNAMICS.md`.  An increment-only estimate first
leaves a \(1/12\)-exponent gap, but
the exact Lamb-vector formula
\(\Pi_s=-\langle P_{2s}u,u\times\omega\rangle\) pays the flux amplitude at that same geometric
scale.  A viscosity-speed-safe filter cannot reach zero while remaining above the paid scale,
and an explicit planar triad has positive scale variation despite zero active-excursion and
direction costs.  The unresolved obligation is therefore an explicitly debited high-frequency
stopping chain with a separate persistent-line mechanism, rather than an undifferentiated
fourth moment, an exponent mismatch, or an uncharged moving filter.

The formalization must therefore proceed from the PDE layer upward.  The intended
dependency order is:

1. periodic vector fields, derivatives, integration, and the Leray projection
   (the compact domain, continuous fields, periodic lift, and the maximum-principle
   differential operators are complete; concrete smooth coordinate integration and transport
   integration by parts are complete, while general Sobolev function spaces and projection
   infrastructure remain);
2. smooth Navier--Stokes solutions and the vorticity equation (complete for a
   jointly smooth lifted solution and a regular concrete curl field, with all
   pressure, convection, Laplacian, and time commutators derived);
3. the energy/enstrophy and vorticity-magnitude identities (the concrete global
   enstrophy identity is complete; the weak/Sobolev energy infrastructure remains);
4. precise replacements for the paper's geometric notions (structure, tube, active
   scale, episode, event, organization, and tangle);
5. the linear column and episode estimates;
6. classification, strain budget, trajectory/maximal-vorticity estimate, and BKM;
7. suitable weak solutions, rescaling compactness, confinement, quantitative
   rigidity, and the final contradiction.

## First analytic layer

`NSFormal/Budget.lean` proves the actual measure-theoretic Hölder estimate used in
the time-integrated strain budget,

\[
  \int \Omega^{5/6}\,d\mu
  \le
  \left(\int \Omega\,d\mu\right)^{5/6}
  \mu(\mathrm{univ})^{1/6},
\]

for nonnegative integrable `Ω` on a finite measure space.  This replaces the prior
certificate `w10_holder_exponents`, which checked only `5/6 + 1/6 = 1`.

The same file now proves the two flux-measure integration steps used for persistent closed
vortex lines in (9.16)--(9.17) of `DYNAMICS.md`.  A per-curve lower bound
\(c\le\sqrt{e_\gamma d_\gamma}\) implies
\(c\,\Phi\le\sqrt{\int e_\gamma\,d\Phi\int d_\gamma\,d\Phi}\), while a per-curve long-line
energy floor implies \(c\,\Phi\le\int e_\gamma\,d\Phi\).  These theorems quantify over genuine
finite measures and integrable charge functions; the geometric Fenchel and torus-systole inputs
remain explicit analytic obligations rather than assumed Lean structures.

Its finite-time closure proves, from a genuine set-integral enstrophy budget and a
continuous pointwise rate inequality,

\[
  \int_0^T \gamma
  \le C_5 B^{5/6}T^{1/6}+C_1B+C_0T.
\]

`NSFormal/Vorticity.lean` formalizes the derivative of the norm of a nonzero path,
the correct viscous vorticity-magnitude evolution, the favorable-sign inequality,
and its Grönwall closure.  In particular, it proves an exponential bound under the
explicit hypotheses that the viscous pairing is nonpositive and the directional
stretching rate is bounded.  It does not assume that the viscous sign holds along an
arbitrary trajectory.

## Compact-domain maximum-principle layer

`NSFormal/Domain.lean` defines the actual period-`2π` three-torus
`Fin 3 → AddCircle (2π)`, supplies an explicit origin, and verifies nonemptiness and
compactness.  Spatial maximum theorems therefore cannot be discharged through an
empty domain or an assumed inhabitant.

`NSFormal/MaxEnvelope.lean` constructs an attained maximum for every continuous
real field on a nonempty compact space.  It proves that the maximum operator is
`1`-Lipschitz in the sup norm, defines the nonempty compact maximizer set, and proves
a compact-domain Danskin theorem: if a time curve of fields is differentiable in
the sup norm, then the upper right Dini slopes of its maximum envelope are bounded
by the largest time derivative among the current maximizers.  Its Grönwall theorem
requires the production inequality only on that maximizer set; it never differentiates
a chosen maximizing point.
It also proves the variable-coefficient form with exponent `exp (∫ k)`, using an
integrating factor with an actual differentiable primitive.

`NSFormal/VorticityMaximum.lean` uses the smooth scalar `|ω|²/2`, avoiding the
singular direction `ω/|ω|` at zeros.  It proves that sup-norm differentiability of
`ω(t,·)` implies sup-norm differentiability of this energy field with pointwise
derivative `⟪ω, ∂ₜω⟫`.  It then checks the corrected parabolic closure

\[
  \partial_t(|\omega|^2/2)
  = \text{stretching}
    + \nu\bigl(\Delta(|\omega|^2/2)-|\nabla\omega|^2\bigr)
    - \text{transport},
\]

under explicit maximizer facts: transport is zero, the scalar Laplacian is
nonpositive, the gradient-square term is nonnegative, and stretching has the stated
bound.

`NSFormal/PeriodicCalculus.lean` constructs the quotient covering map, a canonical
fundamental-cube representative, and periodic lifts to `ℝ³`.  It proves with Fermat's
and Taylor's theorems that transport vanishes and the scalar Laplacian is nonpositive
at every torus maximizer.  It defines `|∇ω|²`, proves its nonnegativity, and derives
the exact identity

\[
  \langle\omega,\Delta\omega\rangle
  = \Delta(|\omega|^2/2)-|\nabla\omega|^2.
\]

`NSFormal/PeriodicIntegration.lean` supplies the missing concrete volume calculus rather than
postulating a skew-adjoint derivative.  It proves one-period integration by parts on `ℝ`,
transports it to Haar volume on `AddCircle (2π)`, applies it on every coordinate circle of
`Torus3`, and uses Mathlib's volume-preserving `Fin 3` coordinate split plus Fubini to derive

\[
 \int_{\mathbb T^3} f\,\partial_i g
 =-\int_{\mathbb T^3}(\partial_i f)g,
 \qquad
 \int f(u\cdot\nabla g)
 =-\int\bigl((u\cdot\nabla f)+f\,\nabla\cdot u\bigr)g.
\]

The file proves the descended coordinate Leibniz rule before assembling the second identity,
and obtains the divergence-free skew-adjoint formula as a corollary.  Its hypotheses are
coordinate-slice `C¹` regularity and the explicit integrability conditions required by Fubini;
an actual nonconstant sine/cosine mode witnesses nonvacuity.  This closes periodic integration
by parts for smooth scalar transport.  Heat-kernel smoothing, Hodge/Leray projection, and the
vortex-line disintegration remain separate analytic layers.

`NSFormal/ForTauCeti/PeriodicIntegration.lean` now extracts the one-period kernel from that
concrete dependency graph and generalizes the scalar coordinate theorem to normalized
`UnitAddTorus (Fin (n + 1))`.  Its constant-mode and nonconstant unit-period sine/cosine tests
pin the zero-mode and `2π` derivative conventions.  The original period-`2π` module consumes
the extracted circle lemmas through compatibility wrappers.  This is a smooth proof seed for
Tau Ceti; intrinsic weak periodic derivatives and the Sobolev-density extension remain open.

`NSFormal/Enstrophy.lean` now closes the smooth global enstrophy identity on the same
concrete torus.  Haar integration is constructed as a continuous linear map on sup-norm
continuous fields, so the existing time derivative of vorticity differentiates
`E(t) = ∫ |ω(t,x)|²/2 dx` by the chain rule.  The file then proves that the slice derivative
used by `PeriodicIntegration.lean` equals `torusPartial`, including the quotient seam, and
proves the corresponding component, divergence, transport-energy, and second-derivative
compatibility lemmas.  Periodic Haar integration therefore cancels both transport and the
scalar Laplacian, yielding for the concrete classical Navier--Stokes/vorticity predicates

\[
 E'(t)=\int_{\mathbb T^3}\omega\cdot(\omega\cdot\nabla)u
      -\nu\int_{\mathbb T^3}|\nabla\omega|^2.
\]

The final assembly assumes only the coordinate-slice smoothness and integrability conditions
needed by Fubini, not a separate scalar evolution law or either cancellation equality.  It also
identifies this production density with `periodicVortexStretchingDensity`, so the exact
self-transport quotient/optimal weighted-variance estimate now applies to the PDE balance
itself.

`NSFormal/NewProofAlgebra.lean` now assembles the next spatial step without real roots.  From
`N² ≤ QV`, `Q ≤ ΘP`, and the isolated interpolation input `V² ≤ K E³P`, it proves

\[
 N^4\le K\Theta^2E^3P^3,
 \qquad
 N\le\frac\nu2P+\frac{27K\Theta^2E^3}{32\nu^3}.
\]

Thus fractional-power manipulation is no longer part of the gap.  The new
`NSFormal/SpatialInterpolation.lean` goes further on the concrete Haar torus.  With

\[
 V=\int |u|^2|\omega|^2,\quad
 H=\int |u|^4|\omega|^2,\quad
 J=\int |u|^2|\omega|^4,
\]

it proves the ordinary Cauchy links `V² ≤ H W₂`, `H² ≤ U₆ J`, and `J² ≤ H W₆`, hence
`V⁶ ≤ U₆² W₆ W₂³`.  It identifies `W₂=2E`, defines the matching global palinstrophy,
and assembles the signed production estimate, including the harmless negative-production
branch.  `NSFormal/DivCurl.lean` now proves the velocity part of the standard transfer:
the pointwise gradient/curl algebra, periodic integration by parts, derivation of differentiated
incompressibility from ordinary divergence-free plus mixed-partial commutation, and hence

\[
 \int_{\mathbb T^3}|\nabla u|^2=\int_{\mathbb T^3}|\operatorname{curl}u|^2.
\]

`NSFormal/PeriodicSobolev.lean` and `NSFormal/PeriodicSobolevEuclidean.lean` carry out the
Sobolev transfer without introducing an abstract domain axiom.  The first proves from
Cauchy--Schwarz, FTC, and the integral mean-value theorem
the concrete interval estimate

\[
 \int_a^b|f-\bar f|^2\le (b-a)^2\int_a^b|f'|^2,
\]

transports it to the measured circle, and then through the volume-preserving coordinate split
to `T³`.  Its coordinate conditional mean `M_i` satisfies

\[
 \int|f-M_i f|^2\le (2\pi)^2\int|\partial_i f|^2,
 \qquad \int M_i f=\int f,
 \qquad \int|M_i f|^2\le\int|f|^2.
\]

It then proves Fubini commutation for the three coordinate averages, tensors the three
conditional-variance estimates, and obtains a concrete (nonsharp) global mean-zero Poincare
inequality.  The Euclidean-transfer file identifies Haar `T³` measurably with a half-open cube,
constructs one fixed smooth cutoff, invokes Mathlib's proved Euclidean
Gagliardo--Nirenberg--Sobolev theorem at `(p,p')=(2,6)`, and proves that the cutoff support meets
at most `5³=125` translated period cells.  It also descends the Fréchet derivative measurably
to the torus and proves compatibility with the coordinate derivatives already used by the PDE
layer.  Consequently the library now contains periodic `H¹ → L⁶` in extended-norm,
real-norm, and ordinary sixth-moment forms.

The standard spatial assembly is now complete.  The inhomogeneous theorem has been specialized
to the homogeneous mean-zero pair

\[
 U_6\le C_u W_2^3,\qquad W_6\le C_\omega P^3,
\]

The lower-order `L²` term is absorbed with the proved Poincare estimate; the descended
derivative norm is compared with `torusGradientEnergy`; the independent palinstrophy derivative
convention is proved pointwise equal to the Frobenius gradient; and vorticity has zero mean
because it is a periodic curl.  `SpatialInterpolation.lean` now discharges both named Sobolev
premises and proves the production remainder with no Sobolev hypothesis.  It also proves the
unconditional baseline `Q ≤ P` for the integrated self-transport quotient, constructs the
zero-safe concrete fraction `Θ=Q/P` in `[0,1]`, proves `Q=ΘP` including at `P=0`, and states
the final production bound directly with this `Θ`.  The divergence/curl energy identity is no
longer assumed.  The genuinely new input is therefore exactly sufficiently fast dynamical decay
of this concrete fraction, or an equivalent signed-correlation depletion estimate.

`NSFormal/DynamicCriterion.lean` closes the real-variable endgame of the resulting proposed
criterion.  If `E > 0`, `E' ≤ C Θ² E³`, `Θ² E ≤ M`, and `∫ E ≤ B`, it proves

\[
 E(t)\le E(a)\exp(CMB).
\]

The proof uses `(log E)' ≤ CM E`; it does not make the false simplification that `E'`
becomes linear.  Thus the remaining research obligation is spatial/PDE: derive the cubic
rate and a bounded or suitably integrable quotient/correlation factor from every potential
singular solution.  The continuation calculus itself is now kernel-checked.

The dynamic file also defines the zero-safe positive-production correlation and quotient
fraction, proves their `[0,1]` bounds and the correlation's exact numerator identity, and proves
zero-production cancellation.  Two scaling regressions prevent a false closure.  Correlation
is unchanged by fixed-shape amplitude scaling.  More decisively, under the concentration weights
`(N,Q,V,P,E) ↦ (λ³N,λ³Q,λ³V,λ³P,λE)`, both normalized factors are invariant and

\[
 \mathfrak c^2\Theta^2E\mapsto\lambda\mathfrak c^2\Theta^2E.
\]

The file proves that any profile with a positive base factor therefore generates rescalings
exceeding every fixed bound.  Signed correlation can help only through actual dynamical profile
deformation or depletion; normalization alone cannot defeat concentration.

`NSFormal/Recurrence.lean` begins the remaining nonclosed-trajectory geometry without assuming
that recurrence produces a closed loop.  For a `C¹` vector path it proves the exact identity

\[
 \int_0^L\xi(s)\,ds=L\xi(L)-\int_0^L s\,\xi'(s)\,ds.
\]

It then proves weighted Cauchy--Schwarz on the actual interval measure and combines it with
the reverse triangle inequality for a `C¹` unit-tangent path.  Thus the full finite-segment
estimate

\[
 (L-|d|)^2\le \frac{L^3}{3}\int_0^L|\xi'(s)|^2\,ds
\]

is kernel-checked rather than assumed.  Consequently a lifted segment with drift at most `α L` pays
\(L\int|\xi'|^2\ge3(1-\alpha)^2\), this geometric floor converts to the product of weighted
energy and direction charges, and the complementary near-return branch carries quantitative
lattice winding.  The file packages the two branches as a disjunction.  It does not yet prove
the measurable return-time selection needed to assign overlapping returns exactly once to a
normalized elementary solenoid; that is the remaining recurrence ledger obligation.
The ballistic branch is now stronger than a homology count: with
\(d=\int_0^L\xi\) and \(\bar\xi=d/L\), the same file proves

\[
 \int_0^L|\xi-\bar\xi|^2=L-\frac{|d|^2}{L}.
\]

Thus \(|d|\ge\alpha L\) gives tangent variance at most \(L(1-\alpha^2)\).  The checked
alternative is consequently curvature, or quantitative winding together with
constant-direction coherence.  Turning that coherence into a scalar-diffusive estimate for
the signed work is the next analytic obligation.  The file also checks the first reduction:
the normalized displacement direction \(e=d/|d|\) satisfies
\(\int|\xi-e|^2=2(L-|d|)\le2L(1-\alpha)\), and
for every continuous line field `B`, the difference between
\(\int\xi\cdot B\) and the still-signed constant-unit-direction pairing
\(\int e\cdot B\) is at most
\([2L(1-\alpha)]^{1/2}(\int|B|^2)^{1/2}\) on the ballistic branch.  No bound for the
constant-direction term or the transverse integral of this error is assumed.
`NSFormal/Budget.lean` supplies the corresponding family-level statement: integrating such
signed errors over a curve measure costs at most the geometric mean of the total coherence and
field charges.  Under the flow-box identity these become
\(2(1-\alpha)\int\rho\) and \(\int\rho|B|^2\), respectively.  The latter is not asserted to
be energy-paid.
For comparison with anisotropic regularity criteria, the normalized direction also gives the
formal cross-component ledger
\(\|e\times\omega\|_2^4\lesssim[W(1-\alpha)]^2\Omega\).  The scalar implication that a
bounded product `W * deficit` makes this linear in enstrophy is checked in
`NewProofAlgebra.lean`; constructing a global regular direction field `e` from orbitwise
directions is not.
The recurrence file now also checks the balanced adaptive specialization
\(\alpha=1-c/W\) on \(W>c>0\).  Its slow branch gives the amplitude-independent product
floor \(3(\theta c)^2\); its ballistic branch gives normalized-direction error
\(2cL/W\), the corresponding winding lower bound, and hence the scalar input
\(W(1-\alpha)=c\) needed by the cross-component ledger.  These are exact local implications,
not an assumed global disintegration.

`NSFormal/Anisotropy.lean` prevents an invalid shortcut at the next interface.  It defines the
unit field \((\cos Nz,\sin Nz,0)\), proves that it is exactly constant on every line directed
by itself, and proves that it becomes antipodal across the transverse separation \(\pi/N\).
Thus even zero vortex-line curvature does not control the full spatial gradient of an orbitwise
direction.  The corresponding periodic shear is an explicit smooth Navier--Stokes solution,
so an admissible assembly theorem must debit transverse direction variation to viscosity or
spectral transfer; it cannot obtain Lipschitz regularity from recurrence geometry alone.
`NSFormal/NewProofAlgebra.lean` records the corrected variable-direction payoff.  Given the
standard integration-by-parts split for a unit field `e`, it keeps the actual mixed error
\(\mathcal A_e=\int|u||\nabla u||\nabla e|\) visible and proves the exact scalar implication

\[
 \|Se\|_2^4\le \frac18\|e\times\omega\|_2^4
 +C\mathcal A_e^2,
 \qquad
 \mathcal A_e^2\le
 \|u\|_2^2\|\nabla u\|_2^2\|\nabla e\|_\infty^2.
\]

Together with the adaptive cross-component bound, the sharp assembly target is therefore
\(\int\mathcal A_e^2<\infty\); the more transparent condition
\(\int\Omega\|\nabla e\|_\infty^2<\infty\) is sufficient.  The Lean theorems check both
fourth-power algebra steps conditional on the analytic split; they do not assert the existence
or regularity of the assembled field.  `NSFormal/PeriodicIntegration.lean` now additionally
checks the concrete Haar-measure integration by parts and three-factor Leibniz expansion for
each component of that split.  `NSFormal/AnisotropicIntegration.lean` performs the full
finite-index assembly and cancels the middle term under an explicit differentiated-divergence
hypothesis.  It additionally proves the pointwise two-product component bound and the exact
`54` finite-index integral estimate under coordinate majorants, and instantiates those
majorants with the Euclidean velocity norm and coordinate-`ℓ¹` gradients for a unit direction
field.  `NSFormal/AnisotropicCriterion.lean` then instantiates the concrete periodic gradient,
transpose-gradient, strain, curl, and cross actions; proves the exact integrated identity and
the \(5832=2\cdot54^2\) fourth-power estimate; and packages the time-integrability handoff.
Its constant-coordinate-direction/zero-velocity witness establishes that all bundled analytic
hypotheses are jointly satisfiable.  It also proves invariance of the derivative, strain, and
curl actions under subtraction of any spatially constant velocity \(a(t)\), so the mixed debit
may use \(|u-a|\) rather than the noninvariant \(|u|\).

On a selected positive-vorticity region, taking \(e=\xi=\omega/|\omega|\) gives the exact
amplitude--direction identity
\[
 |\nabla\omega|^2=|\nabla|\omega||^2+|\omega|^2|\nabla\xi|^2
\]
and hence the sharper weighted debit
\[
 \mathcal A_{\xi,A,a}^2\le
 \left(\int_A|\nabla\omega|^2\right)
 \left(\int_A\frac{|u-a|^2|\nabla u|^2}{|\omega|^2}\right).
\]
`NSFormal/AnisotropicCriterion.lean` checks the derivative algebra and
`NSFormal/Budget.lean` checks both this abstract \(L^2\) product ledger and the high-set
bound
\[
 \int_A\frac{F}{|\omega|^2}\le(\theta W)^{-2}\int_AF
 \quad\text{when }|\omega|\ge\theta W>0.
\]
No theorem asserts that this quotient is small for Navier--Stokes.  The direction-field
construction, measurable selection and patching, and either a parabolic estimate or an
absorbable bound for this weighted quotient remain separate obligations.  More precisely, the
standard strain interpolation makes \(Q_{A,a}\Omega\), rather than \(Q_{A,a}\) alone, the
scale-invariant absorption parameter.  `NSFormal/NewProofAlgebra.lean` checks the exact
fourth-power implication
\[
 C^4Q_{A,a}\Omega\le\nu^4\quad\Longrightarrow\quad
 \mathcal N_A\le\nu P_A
\]
from the displayed directional-fourth-power and nonlinear-interpolation premises.  Those
premises still need to be derived for a global patched direction in the concrete PDE layer.
For the spatial-mean frame, the standard torus Poincaré--Sobolev and Calderón--Zygmund
estimates formally reduce the critical product further to
\[
 Q_{A,a}\Omega\lesssim
 \theta^{-2}\left(\frac{\Omega^2}{W}\right)^{4/3}.
\]
`weighted_quotient_concentration_exponent_chain` checks this exponent conversion.  The
Poincaré--Sobolev/Calderón--Zygmund estimate itself, the patching, and the complementary
nonconcentrated regime are not yet formalized.
The standard \(L^\infty\) vorticity analyticity scale
\(r_a\asymp\sqrt{\nu/W}\) would conversely force a fixed-fraction core volume
\(\gtrsim\nu^{3/2}W^{-3/2}\), and therefore
\(W/\Omega^2\lesssim\theta^{-4}\nu^{-3}\).
`analytic_volume_forces_critical_concentration_cap` checks the last scalar implication.
The analytic-radius/core-volume premise is not yet in the periodic PDE layer.  Its scaling
matches the sufficient absorption threshold exactly, so this route presently has no exponent
slack; constants or additional anisotropic/signed information must decide it.

`NSFormal/DirectorTensor.lean` introduces a sharper replacement for the oriented selector.
For a symmetric trace-one director tensor \(P\), it checks the pointwise and integrated
identities
\[
 \int\operatorname{tr}(PS^2)
 =\frac14\int\bigl(|\omega|^2-\omega\cdot P\omega\bigr)
 -\sum_{ijk}\int u_j\partial_k u_i\partial_iP_{jk}
\]
and two fourth-power bounds.  The coordinate-\(\ell^1\) bound has coefficient
\(1458=2\cdot27^2\); the stronger proof treats the complete error as one Frobenius inner
product and has coefficient (2), with no dimension-counting loss.  The file proves exact
compatibility with \(P=e\otimes e\), including equality of the single tensor derivative with
the former two direction-error terms, and gives a constant-rank-one/zero-velocity witness for
all bundled hypotheses.  Its convex eigenframe lemma records why positive trace-one weights
retain control of the least squared strain eigenvalue.

The same file defines the explicit regularized tensor
\[
 P_c=\frac{\omega\otimes\omega+(c^2/3)I}{|\omega|^2+c^2},
\]
proves symmetry, trace one, nonnegative strain and cross contractions, and proves the exact
uniform cross density
\[
 |\omega|^2-\omega\cdot P_c\omega
 =\frac{2c^2}{3}\frac{|\omega|^2}{|\omega|^2+c^2}\le\frac{2c^2}{3}.
\]
It also checks the resulting spatial/fourth-power bound and the exact quotient-rule derivative.
The load-bearing refinement is the exact Frobenius identity
\[
 \|dP_c(w)[h]\|_F^2
 =2\frac{|w|^2|h|^2-(w\cdot h)^2}{(|w|^2+c^2)^2}
 +\frac83\frac{c^4(w\cdot h)^2}{(|w|^2+c^2)^4},
\]
which vanishes at (w=0) and is bounded by
\((14/3)|w|^2|h|^2/(|w|^2+c^2)^2\).  With
\[
 P_F=\int|\nabla\omega|_F^2,
 \qquad
 Q_c^F(a)=\int |u-a|^2|\nabla u|_F^2
   \frac{|\omega|^2}{(|\omega|^2+c^2)^2},
\]
the resulting checked one-time ledger is
\[
 \Sigma_{P_c}^2\le c^4|\mathbb T^3|^2/18+\frac{28}{3}P_FQ_c^F(a).
\]
This construction removes orientation, zero-set, and sign-patching assumptions, and its
quotient density is itself zero on the vorticity zero set.  `NSFormal/Budget.lean` checks the
low/high split
\[
 Q_c^F\le\int_{|\omega|^2<c^2}F|\omega|^2/c^4
 +\int_{|\omega|^2\ge c^2}F/|\omega|^2,
 \qquad F=|u-a|^2|\nabla u|_F^2,
\]
as well as the sharp global kernel bound (r/(r+c^2)^2\le1/(4c^2)).  The latter proves that
parameter optimization alone still recovers the critical two-thirds interpolation exponent.
The exact differential additionally separates angular and radial-amplitude terms; the radial
kernel (c^4r/(r+c^2)^4) has checked maximum (27/(256c^2)) and high-amplitude cubic decay.

The vector-valued Haar centering is now fully packaged, not merely componentwise.  The explicit
weight
\(g_c^F=|\nabla u|_F^2|\omega|^2/(|\omega|^2+c^2)^2\) constructs the optimal frame
\(a_c^F=(\int g_c^Fu)/(\int g_c^F)\) and proves
\(Q_c^F(a)=Q_c^F(a_c^F)+(\int g_c^F)|a-a_c^F|^2\), together with the global minimum.
The ordered trace-zero eigenvalue calculation and convex eigenframe weighting are checked as
well; only their matrix spectral-decomposition and continuation-criterion packaging remains.
The main unchecked interface is PDE or signed control of the optimally centered (Q_c^F),
preferably using the exact angular/radial dissipation split.

`NSFormal/VortexStretching.lean` formalizes a sharper production-level alternative.  It proves
the periodic identity
\[
 \int\omega\cdot(\omega\cdot\nabla)u
 =\int\rho^2u\cdot[\xi\,\nabla\cdot\xi-(\xi\cdot\nabla)\xi]
\]
from explicit slice smoothness, integrability, and \(\nabla\cdot(\rho\xi)=0\) hypotheses.  The
proof checks that all amplitude derivatives cancel.  A zero-safe rank-two projection argument
then proves the sharp pointwise inequality
\[
 |(\omega\cdot\nabla)\omega|^2\le
 2|\omega|^2D_\xi(x),
\]
including at `ω = 0`; an explicit equality jet proves that the coefficient `2` is optimal.
More strongly, with
\[
 G_\omega=\int\frac{|(\omega\cdot\nabla)\omega|^2}{|\omega|^2},\qquad
 K_\omega=\int\frac{|P_{\omega^\perp}(\omega\cdot\nabla)\omega|^2}{|\omega|^2},
\]
where both quotients are defined as zero on the zero set, the checked hierarchy is
\[
 N^2\le G_\omega V_\omega
 \le(2D_\xi-K_\omega)V_\omega\le2D_\xi V_\omega,
 \qquad G_\omega\le P,
 \qquad V_\omega=\inf_a\int|\omega|^2|u-a|^2.
\]
The file constructs the minimizing vorticity-weighted frame and packages every displayed
periodic integral inequality.  The accompanying scalar lemmas in
`NSFormal/NewProofAlgebra.lean` prove that
\(G_\omega V_\omega\le\nu^2P^2\) is sufficient for direct absorption and that the unconditional
Young fallback leaves only \(V_\omega/(2\nu)\) against scalar-amplitude diffusion.  No theorem
asserts this critical product bound for arbitrary Navier--Stokes solutions.  A final checked
amplitude-scaling theorem shows why: for a fixed nontrivial shape, `G/P` is unchanged by
`u ↦ A u` while `V/P` gains a factor `A²`.  The exact product cannot obey a data-independent
instantaneous smallness condition; any closure must be dynamical near a putative singular time.
The scalar layer also checks the sharp `P³ᐟ⁴` Young inequality with remainder
`27 A⁴/(32ν³)`.  Combined analytically with the standard torus Sobolev estimate, this yields the
energy-paid continuation target
\(\int^T(G_\omega/P)^2E_\omega^2<\infty\), and in particular the sufficient high-enstrophy
depletion rate \((G_\omega/P)^2E_\omega=O(1)\).  The Sobolev/PDE assembly and, decisively, this
dynamic depletion estimate remain unformalized obligations.
This absolute criterion is deliberately not advertised as necessary: Beltrami/ABC regression
fields have positive line-transport and variance charges but zero signed production.  The
complementary normalized production correlation described in `DYNAMICS.md` is the interface
between this geometric ledger and the signed filtered-flux program; controlling that correlation
is also an open PDE obligation.

`NSFormal/TorusVorticity.lean` instantiates the compact maximum theorem with these
periodic facts.  Its strongest theorem begins from the vector vorticity equation,
derives the corrected scalar energy equation by pairing with `ω`, and discharges
transport, Laplacian, and gradient-dissipation signs.  It now composes that theorem
with the integrated strain budget to give the explicit repaired finite-time maximum
bound.

## Concrete Navier--Stokes layer

`NSFormal/NavierStokes.lean` defines the classical velocity-pressure equation and
incompressibility on the concrete torus using the canonical lifted derivatives.  It
separately defines “vorticity is curl of velocity” and the viscous vector-vorticity
equation.  These are propositions over explicit fields, not an assumed solution
typeclass.  For every positive viscosity, Lean constructs zero velocity, pressure,
and vorticity fields satisfying all three predicates simultaneously.  This witness
rules out proofs that succeed only because a formal solution type is empty.

`NSFormal/VectorCalculus.lean` now discharges the full differential derivation.  It
reconstructs coordinate derivatives from the Fréchet derivative, proves the
incompressible convection-curl identity, proves curl--Laplacian commutation from
third derivatives, proves time--curl commutation from joint time-space smoothness,
eliminates pressure, and derives `IsClassicalVorticityEquationOn` from
`IsSmoothNavierStokesOn` for every regular concrete field equal to curl on the
periodic lift.  Both predicates have explicit zero witnesses.

`NSFormal/Stretching.lean` proves the unconditional elementary bound

\[
  \langle\omega,(\omega\cdot\nabla)u\rangle
  \le 2\|\nabla u\|_{\mathrm{op}}\,\frac{|\omega|^2}{2}.
\]

Thus the remaining stretching obligation is sharply isolated: the paper must derive
an integrable scalar rate dominating the local velocity-gradient norm at current
vorticity maximizers.  The claimed geometric organization/column/episode machinery
is intended to provide that rate, but its load-bearing analytic estimates remain
unformalized (the paper proves them in prose in Part II; none is yet machine-checked).

`NSFormal/FarField.lean` separately verifies the manuscript's finite-shell
Cauchy--Schwarz bookkeeping.  It gives the correct squared-weight series
\(\sum_{k\ge0}2^{-5k}=32/31\), from which the manuscript's weaker \(4/3\) constant
follows.  This repairs one estimate but does not validate the cell localization that
precedes it or create a route to global regularity.

`NSFormal/SpectralFlux.lean` proves the finite-shell Abel identity which rewrites weighted
modal transfer as increasing shell weights paired with cumulative forward kinetic-energy flux.
It also defines finite-mode heat-filtered transfer and proves

\[
 \Pi_s=-A_s,\qquad \partial_s\Pi_s=2B_s,
\]

where \(B_s\) is heat-filtered weighted transfer.  Finally it verifies the moving-scale
algebra: \(\partial_sY_s=-2Z_s\) changes the palinstrophy coefficient from \(2\nu\) to
\(2(\nu+s')\), and \(s'\ge-\nu/2\) retains at least \(\nu Z_s\).  These are the algebraic
cores of the exact spectral and Gaussian-filter statements in `DYNAMICS.md`; they do not
assume that the flux or its scale derivative has a favorable sign.  A further finite-shell
theorem rewrites \(\Pi_s\) as heat-weight differences paired with sharp forward flux and proves
its nonnegativity when those sharp fluxes are nonnegative.  The file now also proves the finite
tail layer-cake identity and its one-sided recurrence corollary: control of every final
high-frequency tail by its initial tail plus a positive-variation charge controls the final
weighted shell mass by the correspondingly weighted charges.  This is the finite algebraic
counterpart of the continuation criterion (10.9) in `DYNAMICS.md`.
It now sharpens that recurrence algebra with an exact selector duality.  For net modal input
`transfer - dissipation`, it constructs the monotone multiplier whose increment is either the
full shell-weight increment or zero according as the corresponding tail is increasing.  The
weighted sum of positive tail inputs equals the signed modal pairing against this multiplier,
and also equals selected forward flux minus the dissipation paid by the same multiplier.
Every other monotone multiplier with increments between zero and the prescribed shell-weight
increments gives a no-larger pairing.  This identifies the exact signed multiplier class that
the remaining PDE/vortex-line estimate must control; it does not bound that pairing.
It also checks the conservative two-shell model used in (8.27): transfers \((-A,A)\) have
zero total, sharp forward flux \(A\), and heat flux
\(A(e^{-2as}-e^{-4as})\).  This certifies the elementary building block of the scale-variation
no-go construction without asserting that arbitrary superpositions are Navier--Stokes flows.
The same file now checks the three-shell signature of the explicit planar field (9.8): weights
\((1,2,5)\), transfers \(A(-3,4,-1)\), heat flux
\(A(3e^{-2s}-4e^{-4s}+e^{-10s})\), and its nonnegativity through the exact factorization
\(q(q-1)^2(q^2+2q+3)\).

`NSFormal/LambFlux.lean` checks the finite-dimensional cancellation behind the improved flux
estimate.  For low-pass velocity \(v\), full velocity \(u\), and vorticity \(\omega\), it proves

\[
 v\cdot(u\times\omega)
 =(v-u)\cdot(u\times\omega)
 =v\cdot((u-v)\times\omega)
 =\omega\cdot(v\times u).
\]

The last form is the integrand in the vortex-line disintegration (8.20) of `DYNAMICS.md`.
The same file proves abstractly, on a nonvacuous real Hilbert space, that a self-adjoint filter
satisfies

\[
 \langle Pu,PN\rangle=\langle P^2u,N\rangle,
\]

and that an orthogonal gradient component of \(N\) drops out, leaving the Lamb pairing.
It further proves the Hilbert-space identities which replace the filtered Lamb vector by the
subgrid vortex force, project that force onto its solenoidal part without changing resolved
work, and move a self-adjoint curl from a potential to the force.  These are the algebraic
cores of the exact energy--circulation duality (8.22)--(8.25) in `DYNAMICS.md`.

`NSFormal/NewProofAlgebra.lean` verifies the scale exponent identities
\((x^{-2/3})^{-3/4}x^{1/2}=x\) for Lamb flux and
\((x^{-2/3})^{-3/2}=x\) for the global filtered-stretching rate.  It also checks the exact Young
coefficient used in (4.4) of `DYNAMICS.md` and proves the adaptive-schedule obstruction.  If a
scale stays above \(x^{-2/3}\), lies below a terminal cone \(a\tau\), and \(a>0\), then
\(x\ge a^{-3/2}\tau^{-3/2}\).  The file proves that every measurable rate with this almost
everywhere lower bound is nonintegrable, and packages the conclusion as
`safe_scale_schedule_not_integrable`.  Thus a heat filter cannot simultaneously remain at an
energy-paid geometric scale, retain viscosity through a parabolic speed limit, reach zero at a
finite terminal time, and coexist with the Leray enstrophy-time budget.

The analytic heat-kernel smoothing, Hodge theory, and vortex-line disintegration themselves are
not yet represented in the Lean PDE layer; concrete periodic scalar integration is now present.
The explicit smooth
torus triad in `DYNAMICS.md` also shows that active excursions can vanish while heat flux is
positive even when direction palinstrophy vanishes; its three-shell flux algebra and positivity
are checked, but the trigonometric torus integral identifying those transfers is not yet
formalized.

Thus the remaining stretching obligation is sharply isolated.  The manuscript's
organization/column/episode machinery does not produce the required rate.  The replacement
target in `RESEARCH.md` is instead an integrable bound on the positive high-frequency axial
strain at current vorticity maximizers after subtracting the full normalized viscous term
\(-\nu\xi\cdot\Delta\omega/|\omega|\); all low modes are paid directly by energy and
enstrophy.  An explicit flat-maximum test field in that note shows that a universal
instantaneous pointwise absorption inequality is false, so any viable closure must exploit
spatial averaging or Navier--Stokes time evolution.

The classical-solution continuation bridge itself is now concrete.  In
`NSFormal/PeriodicRegularity.lean`, smooth periodic lifts automatically provide the
measurability and first/second-derivative integrability needed by the torus identities.
`NSFormal/KineticEnergy.lean` derives directly from `IsClassicalNavierStokesOn` the exact
kinetic-energy law and the finite-time budget
\(\int_a^t E_\omega\le K(a)/(2\nu)\).  Finally,
`NSFormal/ConcreteDynamicCriterion.lean` combines that budget with the actual vorticity
equation, the concrete quotient interpolation estimate, and the logarithmic criterion to prove
an explicit exponential bound for \(E_\omega(t)\).  This theorem is quantified over the actual
velocity, pressure, and vorticity fields; it does not assume an inhabitant of a bundled
"solution with all desired estimates" structure.  Its load-bearing nonstandard premise is
precisely the dynamic critical estimate \(\Theta_G(t)^2E_\omega(t)\le M\).  The formerly
explicit factorization and div--curl energy premises have now been removed from the direct
classical-solution theorem: `C²` velocity regularity, `ω = curl u`, compactness, and
incompressibility derive them internally, including the zero-quotient case.  A separate
zero-enstrophy branch and removal of the mean-zero packaging hypothesis remain useful
formalization cleanup, but they are not substitutes for that dynamic estimate.

The signed channel is sharper and has now been simplified exactly.  If
\(N=\int\omega\cdot(\omega\cdot\nabla)u\),
\(Q=\int|\omega\cdot\nabla\omega|^2/|\omega|^2\),
\(V=\int|\omega|^2|u|^2\), \(P=\int|\nabla\omega|^2\),
\(\mathfrak c=[N]_+^2/(QV)\), and \(\Theta_G=Q/P\), then the new zero-safe Lean identity is
\[
 (\mathfrak c^2\Theta_G^2E_\omega)(PV)^2=[N]_+^4E_\omega,
 \qquad
 \mathfrak c^2\Theta_G^2E_\omega=
 \frac{[N]_+^4E_\omega}{(PV)^2}.
\]
`ConcreteDynamicCriterion.lean` now proves the corresponding direct continuation theorem for
an actual classical solution.  Consequently the auxiliary self-transport quotient is not part
of the signed dynamic obstruction: the most cancellation-sensitive remaining target is a
uniform bound on \([N]_+^4E_\omega/(PV)^2\).

The equality case of the automatic factorization is now concrete rather than only abstract.
`SpatialInterpolation.lean` identifies its defect with an integrated squared residual, and
`ConcreteDynamicCriterion.lean` proves that zero defect is equivalent to the residual vanishing
almost everywhere.  Clearing the zero-safe quotient gives
\[
 |ω|^2(u-a)+\frac{N}{Q}(ω\cdot\nabla)ω=0
 \quad\text{a.e.}
\]
The parallel and orthogonal projections are also kernel-checked.  This does not prove the
dynamic critical estimate; it sharpens the rigidity problem that a near-saturation argument
must solve.  The parallel equation can now be integrated without dividing on the vorticity
zero set: a positive-ε logarithmic regularization and dominated convergence prove zero centered
helicity at exact saturation.  Since a periodic curl has zero mean componentwise, the same Lean
chain proves `∫ u·ω = 0` whenever `ω = curl u`.  The quantitative stability version is now
formalized too: if `D = QV - N²`, then `Q (∫ω·(u-a))² ≤ vol(T³) D`, and for a
genuine curl the centered integral is ordinary helicity.  What remains open is turning this
static defect gap into uniform dynamic depletion during all possible concentration episodes.
The localization extension is now formalized as well.  For every smooth scalar weight `phi`,
the regularized self-transport integral equals the negative pairing of
`torusScalarTransport w phi` with `log(vorticityEnergy + epsilon)`.  The residual estimate
therefore contains an exact, visible approximate-first-integral error.  If
`torusScalarTransport w phi = 0`, Lean proves
`Q (∫ phi * inner w (u-a))² ≤ (∫ phi²) D` and zero weighted centered helicity at exact
saturation.  This blocks cancellation between invariant vortex regions but does not postulate
that a generic vorticity field has a nonconstant global first integral.  The remaining dynamic
problem is to construct exact or approximate tube weights with a scale-uniform signal-to-error
ratio.  The error is now bounded by `∫|w·∇phi|` times the supremum norm of the regularized
logarithmic energy after subtracting an arbitrary constant `k`; this recentering is exact
because divergence-free transport has zero mean.  `ConcreteDynamicCriterion.lean` combines
that estimate with the defect identity to prove a positive-part gap after paying the full
centered leakage budget.  What remains is to keep that positive part nonzero dynamically,
especially through the vorticity zero set.
The corresponding concentration arithmetic is checked: if quotient and defect scale as
`λ³` and `λ⁶`, localized helicity is invariant, and the tube weight has squared mass `λ⁻³`,
then the weighted gap is equivalent before and after rescaling.  This is the first helicity
obstruction in the development that does not lose a spatial-volume factor at the active scale.

`NSFormal/LocalizedHelicity.lean` now supplies a fully explicit nondegenerate regression for
that obstruction.  With torus coordinates `(x,y,z)`, it defines
`phi = cos y`,
`u = (1 - sin y cos y, (sin x)/2, sin y)`, and
`w = (cos y, 0, cos² y - sin² y + (cos x)/2)`.  Lean proves `w = curl u`,
`div w = 0`, `w · ∇phi = 0`, `w ≠ 0` everywhere, and `Q(w) > 0`.  It also proves
that ordinary helicity integrates to zero while `∫ phi (w · u) > 0`; the exact localized
gap then forces the concrete Cauchy defect to be strictly positive.  Thus neither the first
integral, the quotient branch, nor the localized signal in this mechanism is an empty
hypothesis.  This is a static witness, not the missing universal construction of evolving
tube weights along every potential singular solution.

The normalized consequence is now checked in `DynamicCriterion.lean` as well:
\[
 \frac{N^2}{QV}\le 1-\frac{H_\phi^2}{(\int\phi^2)V}.
\]
The subtracted helicity ratio is itself invariant under active-scale concentration because
`H_phi` is invariant while `(∫ phi²)` and `V` scale oppositely.  Therefore a fixed positive
localized signal proves strict nonsaturation but only by a fixed dimensionless margin.  By
itself that does not change the critical `E` growth in the continuation criterion.  A closing
argument must force this loss toward one, force the quotient fraction toward zero, or obtain
an additional time-integrable gain from the evolution of the tube weight.

The exact dynamic handoff is now kernel-checked too, without assuming that production is
positive.  The positive-production correlation is bounded by the same remaining allowance,
and hence
\[
 \left(\mathfrak c\,\Theta\right)^2 E
 \le
 \left(\left(1-\frac{H_\phi^2}{(\int\phi^2)V}\right)\Theta\right)^2E.
\]
Consequently a uniform bound on the right, together with the already proved enstrophy-time
budget and cubic rate, gives the exponential continuation estimate.  This removes an
algebraic ambiguity from WP4b: the open problem is to construct and propagate weights that
control this displayed product for every candidate singular evolution.

`NSFormal/FlowAveraging.lean` now supplies a canonical approximate construction.  For any
continuous real flow `Phi` and continuous seed `psi`, define
\[
 \phi_L(x)=\frac1L\int_0^L\psi(\Phi_s x)\,ds.
\]
The kernel proves the exact identity
\[
 \frac d{d\tau}\phi_L(\Phi_\tau x)
 =\frac{\psi(\Phi_{L+\tau}x)-\psi(\Phi_\tau x)}L,
\]
so a bounded seed has along-flow leakage at most `2 ||psi||_infinity / L`.  This avoids any
global transverse flow-box assumption: only the one-dimensional flow action is used.

There is an equally important limitation.  The checked mean-ergodic diagnostic says that
discrete orbit averages converge in squared norm to the squared norm of the seed's projection
onto the transport-fixed subspace.  The library also contains an explicit isometric sign-flip
whose two-step average annihilates the nonzero seed `1`.  Therefore the missing theorem cannot
be merely “take `L` large.”  It must give a quantitative lower bound on invariant or
low-transport-frequency helicity content, strong enough that the retained amplitude exceeds
the `O(L^-1)` endpoint leakage.

The sign problem for a raw forward average has also been removed at the Hilbert-space level.
For its contraction operator `A_L` and a helicity seed `h`, take the adjoint-averaged weight
`phi_L = A_L* A_L h`.  Lean proves
\[
 \langle\phi_L,h\rangle=\|A_Lh\|_2^2=:r_L^2,
 \qquad \|\phi_L\|_2\le r_L.
\]
After a leakage payment `delta_L`, the defect gap therefore bounds the dangerous correlation by
`1-(r_L-delta_L)^2/V`.  `DynamicCriterion.lean` proves the corresponding complete
continuation theorem under
\[
 \left(\left(1-\frac{(r_L-\delta_L)^2}{V}\right)\Theta\right)^2E\le M.
\]
The operator layer has now been repaired and made genuinely strong-continuity based.
`FlowKoopman.lean` does not integrate the Koopman family in operator norm (translation groups
need not be norm-continuous).  Instead it integrates every `L²` orbit, proves that the result is
a bounded linear contraction, derives strong continuity from a continuous measure-preserving
flow, and proves
\[
 \|U_\tau A_Lh-A_Lh\|_2\le \frac{2|\tau|}{L}\|h\|_2.
\]
It also proves `U_tau* = U_{-tau}`, commutation with `A_L` and `A_L*`, and that the positive
Fejér weight `phi_L=A_L* A_Lh` belongs to the transport-generator domain with generator norm at
most `2||h||_2/L`.  Thus `delta_L` is no longer a free Hilbert-space leakage hypothesis.

`TorusFlow.lean` now checks this bridge on a genuinely moving model rather than only on the
identity flow.  It constructs the Haar-preserving shear
`(x,y,z) ↦ (x+s cos y,y,z)`, proves that its nonzero generator `(cos y,0,0)` is the periodic
curl of `(0,0,sin y)`, and identifies the pointwise flow derivative with
`torusScalarTransport` for every scalar field differentiable along the transported coordinate.
It then instantiates the strong Koopman/Fejér construction and exhibits an explicit nonzero
nonconstant retained first integral with positive signal.

Two bridges remain, of very different character.  The remaining formalization bridge is to
construct this flow and generator identification uniformly for each arbitrary smooth
divergence-free vorticity time slice on Haar `T³`, upgrade the pointwise identity to an `L²`
generator theorem on the required smooth domain, and convert the checked `L²` bound into the
centered-logarithmic `L¹` leakage used by the defect identity.  The mathematical research
obstruction is then a solution-uniform lower bound on the
retained helicity amplitude `r_L`, strong enough that the resulting scale-critical product is
bounded throughout every candidate concentration episode.  Generic averaging cannot supply
that bound, as the checked mean-ergodic and annihilation examples already show.

## Blocking proof obligations found in the paper

These are mathematical obligations, not merely missing Lean library plumbing.

### Viscous vorticity magnitude

Section `subsec:notation` states

\[
  D_t|\omega|=\alpha|\omega|.
\]

For positive viscosity and at points where `ω ≠ 0`, the identity is instead

\[
  D_t|\omega|
  =\alpha|\omega|+\nu\,\xi\mathbin\cdot\Delta\omega
  =\alpha|\omega|+\nu(\Delta|\omega|-|\omega||\nabla\xi|^2).
\]

Consequently `pf:ft` cannot begin with the asserted ordinary differential equation
along an arbitrary flow trajectory.  At a spatial maximum the viscous terms have a
favorable sign, so a maximum-principle argument may support a theorem about
`‖ω(t)‖∞`; it does not by itself support the paper's per-trajectory partition or its
localization step.

The pointwise identity, the regular maximal-vorticity envelope, the upper-Dini
argument, and the conditional squared-vorticity maximum principle are now checked in
`NSFormal/Vorticity.lean`, `NSFormal/MaxEnvelope.lean`, and
`NSFormal/VorticityMaximum.lean`, `NSFormal/PeriodicCalculus.lean`, and
`NSFormal/TorusVorticity.lean`.  The periodic transport, scalar-Laplacian, and
gradient-dissipation facts, and the vector vorticity equation are now derived.  The
remaining obligation is the claimed integrable geometric stretching rate.  None is
inferred from the invalid trajectory equality.

### Undefined geometric predicates

`def:class`, `def:trichotomy`, `lem:dc`, and the event-counting arguments quantify
over “structures,” “coherent tubes,” “mergers,” “re-entry,” and “persistent
pairing” without mathematical definitions of those objects or measurable predicates.
These must be defined before the classification and budget statements have Lean
propositions to express.

### Linear and nonlinear column estimates

The arguments in `pf:band`, `pf:r1b`, and `pfsec:jc1` assert uniform resolvent,
critical-layer, parametrix, smoothing, modulation, and nonlinear bootstrap bounds.
The displayed calculations do not provide the function spaces, operator domains,
boundary conditions, constants, or estimates needed to derive those results.  Each
is a substantial theorem family and is currently an assumption from the perspective
of a formal proof.

### Confinement and quantitative rigidity

`pf:confine` assumes an invariant stable/unstable bundle decomposition and states
that no other neutral directions exist; no preceding theorem constructs that
splitting.  `pf:qt` asserts a quantitative extension of the cited stationary
rigidity theorem, including a ray expansion, perturbed maximum principle, and flux
estimate.  Those quantitative statements are new load-bearing lemmas; the paper proves them
in prose (§§17.2–17.3) and they are not yet formalized; the scalar Lean identities
in `QT1Moment.lean` do not establish them.

### CKN nontriviality floor

`pf:bridge` quotes a lower bound for the scale-invariant quantity containing both
`|u|³` and `|p|^(3/2)`, then states a lower bound for `|V|³` alone.  A pressure
decomposition estimate that justifies removing the pressure term is required and is
not supplied at that step.

Until these obligations are discharged, an honest Lean end theorem can only be
conditional on them.  The project must not introduce them as axioms and then present
the resulting conditional assembly as a formal proof of global regularity.
