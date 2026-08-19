# Research takeover: analytic triage and a viable replacement program

Status: working research note, 2026-08-16.  This is not a proof of global regularity.
Its purpose is to separate the manuscript's useful geometric intuition from statements that
are false or unsupported, and to replace the latter by a small number of exact analytic
obstructions.

## 1. Bottom line

The manuscript does not currently supply a viable proof.  The difficulty is not a missing
technical estimate at the end: several implications that create the tube classification,
episode ledger, and rigidity funnel are invalid.  In particular, the argument removes
viscosity from the evolution of vorticity magnitude and direction, assumes that spatial
incoherence produces temporal recurrence, and applies partial regularity to rule out a
geometric neighborhood rather than a singular set.

There is nevertheless a promising core idea:

1. low-frequency or remote strain should be paid by the energy/enstrophy identity;
2. viscosity damps both direction variation and curvature of the vorticity-magnitude peak;
3. locally parallel vorticity gives an exact geometric cancellation of axial stretching;
4. failure of directional alignment creates vorticity-direction increments, and diffusion
   may pay those increments after spatial or temporal averaging;
5. after these mechanisms, only a scale-transfer/commutator defect should remain.

The right immediate goal is not to prove that every intense structure becomes an Oseen tube.
It is to prove that the positive stretching left after the full pointwise viscous damping is
integrable.  Section 3 gives an exact reduction to that question, and Section 4 gives an
explicit obstruction to trying to prove the needed absorption pointwise for arbitrary fields.
`DYNAMICS.md` advances this to a global filtered balance: at the scale
\((1+\Omega)^{-1/3}\), both singular near-field stretching and far strain are energy-paid,
leaving a precise signed commutator and adaptive-scale jump.

## 2. Load-bearing failures in the manuscript

The line numbers below refer to `paper/main.tex`.

### 2.1 Incorrect evolution equations

At lines 373 and 1786 the manuscript uses

\[
  D_t |\omega|=\alpha|\omega|.
\]

For Navier--Stokes this is false.  Where \(\rho=|\omega|>0\) and
\(\xi=\omega/\rho\), the exact equation is

\[
  (\partial_t+u\cdot\nabla-\nu\Delta)\rho
    =(\alpha-\nu|\nabla\xi|^2)\rho.
  \tag{2.1}
\]

Likewise, the direction equation used at lines 1409--1413 omits

\[
  \frac{\nu}{|\omega|}(I-\xi\otimes\xi)\Delta\omega.
\]

Spatial coherence of the strain and drift of its eigenframe do not bound this term.  Every
trajectory-alignment estimate, transit count, and per-trajectory Gronwall argument in the
paper therefore needs a new proof.  Importantly, the omitted term is not merely an error term:
the contribution \(-\nu|\nabla\xi|^2\) in (2.1) is a potentially useful coercive mechanism.

The use of Kelvin's theorem at line 1473 to obtain a circulation lower bound is also invalid
for viscous Navier--Stokes flow.  Circulation around a material loop is not conserved when
\(\nu>0\).

### 2.2 The classification does not create tubes

The class in lines 404--424 starts with an undefined "structure" and includes conclusions
that must instead be proved: a Burgers balance \(\delta^2=4\nu/\alpha\), a fixed positive
circulation band, a strain band, merger identities, culling, and production-null background.
It is not a decomposition theorem for an arbitrary smooth vorticity field.

The organization proof has four decisive gaps.

- Lines 1398--1402 identify failure of spatial strain coherence on dyadic balls with temporal
  recurrence of rescaled velocity slices near a fixed profile.  These are unrelated
  properties; no implication is proved or generally true.
- Lines 1409--1424 obtain alignment from the inviscid projective ODE after dropping the
  viscous direction term.
- Lines 1477--1484 say a pancake geometry is excluded because the CKN singular set contains
  no surface.  A sequence of smooth pancake-shaped regions can shrink to a single singular
  point.  The geometry of pre-singular neighborhoods does not give the dimension of the
  limiting singular set.
- Coherence and alignment do not imply Gaussian/Oseen proximity in the weighted norm needed
  by the local bootstrap.  The episode proof later assumes this small perturbation as its
  initial hypothesis.

Consequently the manuscript never proves that arbitrary intense vorticity is covered by the
objects to which its column theory applies.

### 2.3 The strain ledger is not closed

Several spatial estimates have promising analogues, but the ledger as written is not valid.

- The cellwise integration by parts at lines 1179--1196 and 1617--1635 omits the cutoff or
  cell-boundary terms created when \(\omega=\nabla\times u\) is localized to a cell.  A global
  smooth frequency or kernel split avoids this problem.
- The displayed shell equality is arithmetically wrong.  The squared shell coefficient is
  \(2^{3k}2^{-8k}=2^{-5k}\), whose sum is \(32/31\), not \(4/3\).  The latter is a permissible
  weaker upper bound, but not the displayed equality.
- Bounded overlap of a Besicovitch cover does not bound the number of unequal-radius neighbors
  of a tube.  Many small disjoint balls can meet a larger neighborhood.
- The asserted minimum enstrophy per tube uses \(\Gamma_{\min}\), \(L_{\min}\), and a core
  ceiling that itself depends on \(\gamma\).  These are not data-only lower bounds obtained
  from the energy identity.
- "Culled" vorticity does not automatically become productionless or decay on an isolated
  viscous core time while it remains in the full advecting and stretching flow.

The background logarithmic estimate is plausible as a localized Calderon--Zygmund/BMO
estimate, but it cannot close the budget until a genuine decomposition and the residual
terms are controlled.

### 2.4 Column stability is conditional local information

The cited spectral stability of monotone columnar vortices is genuine, but it does not imply
the manuscript's full-band limiting absorption, exponential damping, nonlinear modulation,
or three-dimensional transfer statements.

For example, point evaluation (the delta term in a Plemelj boundary value) is not a bounded
functional on a weighted \(L^2\) space without additional regularity.  Absence of unstable
eigenvalues is also not a uniform resolvent or semigroup-decay estimate for a non-normal
operator.  Gallay--Smets prove spectral stability through a detailed critical-layer analysis;
their theorem does not say that arbitrary intense Navier--Stokes vorticity enters a small
Oseen neighborhood.

Column stability remains useful only after an independent theorem constructs and propagates
such a neighborhood.

### 2.5 The funnel does not follow from blow-up compactness

The funnel contains independent, currently unproved theorems.

- Ordinary parabolic blow-up yields an ancient suitable solution of Navier--Stokes.  It does
  not yield a stationary self-similar profile merely from a sequence of scales.
- The classical CKN one-scale floor involves velocity and pressure (or an alternative
  pressure-free criterion with its own hypotheses).  Lines 1897--1902 start from the joint
  velocity--pressure floor and conclude a velocity-only floor without proving the required
  replacement criterion.
- The "two-pin" argument at lines 1912--1939 assumes a complete hyperbolic splitting and no
  additional neutral directions for a tangled recurrent profile.  Results about a modulated
  Oseen column do not provide that splitting for the non-columnar branch.
- Tsai's rigidity theorem is qualitative and applies to exact self-similar solutions under
  specified global bounds.  The claimed estimate
  \(\|V\|\lesssim\|\partial_\tau V\|^{1/2}\) is a new quantitative stability theorem, not a
  cited result.  A local \(H^{-2}\) time defect does not by itself yield the asserted global
  raywise expansion or the perturbed head-pressure maximum principle.

The funnel should therefore be removed from the active strategy unless a genuine rigidity
theorem is first proved independently.

## 3. A rigorous replacement reduction

This section records the first result worth proving fully.  It keeps the manuscript's useful
"far strain is paid" intuition, removes tubes and event counting, and retains the full
favorable viscous pairing that the manuscript lost.

Let

\[
  W(t)=\|\omega(t)\|_{L^\infty},\qquad
  \Omega(t)=\tfrac12\|\omega(t)\|_{L^2}^2,
  \qquad U_0=\|u_0\|_{L^2}.
\]

Use an inhomogeneous smooth Littlewood--Paley decomposition on the fixed, nondimensional
\(2\pi\)-torus, with dyadic wavenumbers \(\lambda_q\simeq2^q\).  Define the energy-paid
wavenumber

\[
  \Lambda_E(t)=(1+\Omega(t))^{2/5},
  \qquad
  2^{Q_E(t)}\le \Lambda_E(t)<2^{Q_E(t)+1}.
  \tag{3.1}
\]

The exponent \(2/5\) is the largest exponent paid directly by the energy identity.  Indeed,
Bernstein and the energy inequality give

\[
\begin{aligned}
  \|S_{\le Q}\|_\infty
  &\le C\sum_{q\le Q}\lambda_q\|u_q\|_\infty\\
  &\le C\sum_{q\le Q}\lambda_q^{5/2}\|u_q\|_2
   \le C\lambda_Q^{5/2}U_0.
\end{aligned}
\tag{3.2}
\]

With (3.1),

\[
  \|S_{\le Q_E(t)}\|_\infty\le C U_0(1+\Omega(t)),
  \tag{3.3}
\]

and this rate is time-integrable on every finite interval because

\[
  \int_0^T\Omega(t)\,dt\le \frac{E_0}{2\nu}.
  \tag{3.4}
\]

For \(W(t)>0\), let \(\mathcal M(t)=\{x:|\omega(x,t)|=W(t)\}\), and define

\[
  \mathcal D_\nu(x,t)
  =-\nu\frac{\xi(x,t)\cdot\Delta\omega(x,t)}{|\omega(x,t)|}
  =\nu\left(|\nabla\xi(x,t)|^2-
       \frac{\Delta|\omega|(x,t)}{|\omega(x,t)|}\right).
  \tag{3.5}
\]

On \(\mathcal M(t)\), \(\Delta|\omega|\le0\), so \(\mathcal D_\nu\ge0\).  This retains
both favorable viscous mechanisms: variation of direction and curvature of the magnitude
peak.  Define the residual

\[
  \mathcal R_E(t)=
  \max_{x\in\mathcal M(t)}
  \left[
    \xi(x,t)\cdot S_{>Q_E(t)}(x,t)\xi(x,t)
    -\mathcal D_\nu(x,t)
  \right]_+.
  \tag{3.6}
\]

### Proposition (energy-paid high-frequency reduction)

For a smooth Navier--Stokes solution on \([0,T)\),

\[
  D^+\log W(t)
  \le C U_0(1+\Omega(t))+\mathcal R_E(t)
  \tag{3.7}
\]

whenever \(W(t)>0\).  Consequently, if

\[
  \int_0^T\mathcal R_E(t)\,dt<\infty,
  \tag{3.8}
\]

then \(W\) stays bounded on \([0,T)\), the BKM integral is finite, and the solution
continues smoothly past \(T\).

#### Proof

At a spatial maximizer of \(\rho=|\omega|\), transport vanishes and \(\Delta\rho\le0\).
The exact equation (2.1), combined with the compact-domain Dini/Danskin formula, gives

\[
  D^+\log W(t)
  \le \max_{x\in\mathcal M(t)}
  \{\xi\cdot S\xi-\mathcal D_\nu\}.
\]

Split \(S=S_{\le Q_E}+S_{>Q_E}\), use (3.3), and take the positive part of the
remaining term to obtain (3.7).  Integrating (3.7) and using (3.4) bounds \(W\).
On a finite interval, bounded \(W\) implies the BKM integral is finite.  QED.

### Why this reduction is useful

- It is unconditional up to the single explicit remainder (3.6).
- It uses no tube count, circulation floor, minimum separation, merger identity, or profile
  recurrence.
- It is exact for two-dimensional/translation-invariant columnar structure: the axial strain
  vanishes and the direction is constant, so the high-frequency remainder is zero.
- Neither amplitude nor directional disorder is simply declared "tangled"; both favorable
  parts of the exact viscous term are retained in \(\mathcal D_\nu\).
- More generally, choosing \(\Lambda=(1+\Omega)^\beta\) makes the low-mode rate proportional
  to \((1+\Omega)^{5\beta/2}\).  The energy identity pays this automatically precisely for
  \(\beta\le2/5\), so (3.1) is the largest automatically paid cutoff obtainable from (3.2).

This proposition is a reduction, not a solution: all supercritical behavior can still hide in
\(\mathcal R_E\).  Its value is that it identifies the obstruction without imposing a
phenomenological decomposition.  The cutoff (3.1) is deliberately not presented as a
scale-invariant quantity: it is an energy-paid split in the fixed torus normalization, and
the supercritical scaling is retained in the high-frequency remainder.

## 4. The research question that replaces "organization"

The central question is now:

> Can positive high-frequency axial stretching at vorticity maximizers be absorbed by
> the full pointwise viscous damping, up to a time-integrable dynamical defect?

The desired estimate is

\[
  \xi\cdot S_{>Q_E}\xi
  \le \mathcal D_\nu + G(t)
  \quad\text{on }\mathcal M(t),
  \qquad G\in L^1_t.
  \tag{4.1}
\]

There are two complementary mechanisms.

1. **Aligned case.**  Constantin's strain representation contains the geometric factor
   \[
     D(\widehat y,\xi(x+y),\xi(x))
       =(\widehat y\cdot\xi(x))
        (\widehat y\cdot(\xi(x+y)\times\xi(x))),
   \]
   so parallel or antiparallel directions cancel exactly.  A rigorous curved-tube statement
   should be derived from this kernel, not from an informal shifted-field ansatz.
2. **Incoherent case.**  Magnitude-weighted direction differences can be bounded by
   first differences of vorticity.  At an integrated or filtered level, those differences are
   candidates for absorption by \(\nu\|\nabla\omega\|_2^2\).  This is the analytic substitute
   for the manuscript's event ledger.

### An exact static obstruction to pointwise absorption

The term \(G\) in (4.1) cannot simply be set to zero for arbitrary smooth divergence-free
fields, even at a global vorticity maximum and even after retaining all of
\(\mathcal D_\nu\).  The following explicit family shows why.

Write \((x,y,z)\) for torus coordinates and set

\[
 f(\theta)=\frac{9\cos\theta-\cos3\theta}{8},
 \qquad f'(\theta)=-\frac32\sin^3\theta.
\]

For \(A>0\), sufficiently small \(\varepsilon>0\), and an integer \(N\), define

\[
\begin{aligned}
 \omega_{A,\varepsilon,N}
  ={}& A\bigl(f(Nx)+f(Ny)\bigr)e_3\\
 &-\varepsilon\bigl(2\cos(2Nx+2Nz)-3\cos(4Nx+2Nz)
                    +\cos(8Nx+2Nz)\bigr)e_2.
\end{aligned}
\tag{4.2}
\]

This field is smooth, mean zero, and divergence free, hence it is the curl of a smooth
mean-zero divergence-free velocity.  The scalar \(f\) decreases from \(1\) to \(-1\) on
\([0,\pi]\) and has quartically flat extrema.  The second line of (4.2) and its first
\(x\)-derivative vanish whenever \(Nx\in\pi\mathbb Z\).  A compactness argument, using the
matching quadratic vanishing of the second line and quartic deficit of
\(|f(Nx)+f(Ny)|^2\), shows that for \(\varepsilon/A\) small enough,
\(x=y=z=0\) is a global maximum of \(|\omega|\).

At that point,

\[
 \omega=2Ae_3,\qquad \nabla\omega=0,\qquad
 e_3\cdot\Delta\omega=0,
 \qquad \mathcal D_\nu=0.
\]

The periodic Biot--Savart multiplier gives, for a mode \(a e_2\cos(k_xx+k_zz)\),
\(S_{33}=-a k_xk_z/(k_x^2+k_z^2)\).  Consequently the three modes in (4.2) give

\[
 e_3\cdot S(0)e_3
 =\varepsilon\left(1-\frac65+\frac4{17}\right)
 =\frac{3\varepsilon}{85}>0.
\tag{4.3}
\]

All Fourier modes have frequency at least \(N\), while \(\Omega\) is independent of \(N\).
Thus, after choosing \(N\) above the paid cutoff, (4.3) lies entirely in
\(S_{>Q_E}\) and \(\mathcal R_E\ge3\varepsilon/85\).

This does not contradict the reduction or disprove an integrable-defect theorem for actual
Navier--Stokes evolution.  It does prove that local alignment, maximality, and instantaneous
viscous curvature alone cannot close the problem.  The missing estimate must use spatial
averaging, time evolution, or another genuinely dynamical constraint.  This is a useful
negative result: it rules out the strongest and most tempting version of WP3.

A June 2026 preprint by Runlong Yu proves a finite-scale version of the second mechanism:
positive filtered near-field stretching is absorbed by filtered diffusion up to an enstrophy
reservoir.  The paper explicitly leaves far-field packing, differentiated filter commutators,
and localization budgets as the remaining obstruction.  Our paid-scale split suggests trying
to discharge the far-field part directly on the torus and then attacking only the commutator
defect.

## 5. Concrete work program

### WP1. Prove the reduction in the analytic library

- State Littlewood--Paley projectors on the torus.
- Prove (3.2)--(3.4) with a fixed normalization.
- Combine them with the already formalized compact-domain maximum/Dini argument and the exact
  full viscous damping \(\mathcal D_\nu\).
- Audit novelty against low-mode regularity criteria before describing the proposition as new.

Success criterion: a conventional proof and Lean theorem whose only analytic hypothesis is
the integrability of (3.6).

### WP2. Replace the paper's far-field cells

- Construct a smooth physical-space cutoff equivalent to the Littlewood--Paley split.
- Track the cutoff-annulus terms omitted by cellwise integration by parts.
- Compare the physical paid length
  \(\ell_E\simeq(1+\Omega)^{-2/5}\) with the manuscript's unproved mean tube spacing.

Success criterion: a global torus far-strain estimate requiring only \(U_0\) and \(\Omega\).

### WP3. Near-field geometric coercivity

- Re-derive Constantin's exact geometric kernel on \(\mathbb T^3\), including the smooth
  periodic remainder.
- Prove the magnitude-weighted direction-increment inequality without dividing by small
  vorticity.
- The global fixed-scale filtered absorption theorem is now derived in `DYNAMICS.md`.
- In view of (4.2)--(4.3), keep the argument averaged or time-integrated; a purely pointwise
  static estimate is impossible.

Success criterion: summability of the positive heat-scale derivative of the signed cubic energy
flux and the equivalent adaptive-filter jumps isolated in `DYNAMICS.md`.  The absolute
fourth-increment estimate is retained only as a no-go comparison.  The Lamb-vector identity now
pays the flux amplitude at the geometric scale; only its positive scale/time variation remains.
A filter which is simultaneously above the paid geometric scale, below a terminal parabolic
cone, and viscosity-speed-safe would force the nonintegrable rate
\((T-t)^{-3/2}\), so the adaptive-schedule branch is now ruled out.  The target is an explicitly
debited stopping chain and weighted positive high-tail recurrence bound.

### WP4. Stress tests and obstruction profiles

Any proposed closure must survive:

- nested unequal-radius filaments (testing unweighted packing and the absence of a circulation
  floor);
- antiparallel close pairs and reconnection-scale direction jumps;
- curved tubes with large circulation Reynolds number, where \(\Gamma\kappa^2\) can dominate
  \(\nu\kappa^2\);
- pancake-shaped intense regions whose lateral diameter also shrinks to a single point;
- a high-frequency tangle with bounded energy but persistent commutator stress.
- persistent high-vorticity lines with no lower-level excursions but nonzero signed transfer.

The flat-maximum family (4.2) rules out (4.1) with \(G=0\) for arbitrary fields.  The explicit
smooth planar torus triad (9.8) in `DYNAMICS.md` adds a dynamically realizable test: every
high-vorticity line is a closed persistent vertical circle, so \(\Phi_{\rm act}=0\) and the
direction-palinstrophy cost is also zero, but its heat-filtered forward flux is strictly
positive.  Any proposed bridge must therefore contain a persistent-line term using scalar
diffusion or time dynamics.  The next task is to construct the nested and
reconnection geometries and evaluate the residual analytically.  Such counterexamples identify
the additional dynamical estimate that Navier--Stokes evolution must supply.

The closed portion of the persistent set now has a geometric ledger: contractible loops pay
Fenchel curvature and hence the same inverse-length direction cost as active excursions, while
noncontractible loops pay the flat-torus systolic length.  The resulting flux-measure estimates
are (9.16)--(9.17) of `DYNAMICS.md`, and their measure-theoretic Cauchy--Schwarz/long-line steps
are formalized in `NSFormal/Budget.lean`.  What remains is signed line work and recurrent
nonclosed trajectories, not an unclassified closed-loop population.

The ambient periodic integration step is also now concrete rather than axiomatic:
`NSFormal/PeriodicIntegration.lean` derives coordinate integration by parts on the actual
period-`2π` measured three-torus, proves the coordinate Leibniz rule, assembles the full
transport formula with its divergence contribution, and specializes it to divergence-free
skew-adjoint transport.  Thus recurrence work may use global torus integration without carrying
an additional boundary-term hypothesis; the unresolved issue is the signed persistent/recurrent
charge itself.

The recurrent nonclosed geometry has also been reduced to a finite-segment dichotomy.  For a
unit-speed lifted segment with displacement \(d\), integration by parts and weighted
Cauchy--Schwarz give

\[
 (L-|d|)^2\le \frac{L^3}{3}\int_0^L|\xi'|^2.
\]

Hence slow lift drift \(|d|\le\alpha L\) forces
\(L\int|\xi'|^2\ge3(1-\alpha)^2\), while a torus near return in the complementary branch
carries lattice winding \(|n|>(\alpha L-\delta)/(2\pi)\).  The exact vector integration by
parts, weighted Cauchy--Schwarz, the full unit-tangent drift/curvature estimate, and the
curvature/charge/winding algebra are checked in `NSFormal/Recurrence.lean`.
Moreover, with \(\bar\xi=d/L\), the exact variance identity
\(\int_0^L|\xi-\bar\xi|^2=L-|d|^2/L\) shows that the ballistic branch is quantitatively
close to a constant-direction flow.  The checked dichotomy is therefore curvature, or winding
plus planar-like tangent coherence.  This makes scalar-vorticity diffusion a concrete target
for the latter branch rather than merely an analogy.
For the normalized direction \(e=d/|d|\), Lean checks the sharper identity
\(\int|\xi-e|^2=2(L-|d|)\le2L(1-\alpha)\).  For a line field \(B\), it also checks that
replacing \(\xi\) by \(e\) in its signed
pairing costs at most
\([2L(1-\alpha)]^{1/2}(\int_0^L|B|^2)^{1/2}\).  The residual is therefore split cleanly into
a coherence error and a constant-direction signed orbit average; only the latter still needs
the scalar-diffusive/transverse argument required by the planar test.
After Cauchy--Schwarz over the curve family, the error is
\(\lesssim[2(1-\alpha)\int\rho]^{1/2}[\int\rho|B|^2]^{1/2}\); that family ledger is also
checked in Lean.  For \(B=P_{2s_G}u\times u\), however, direct heat smoothing and Sobolev
interpolation give only \(C(1-\alpha)^{1/2}(1+\Omega)^{11/8}\).  Since this is not
energy-integrable, fixed ballistic coherence followed by absolute Cauchy--Schwarz is another
dead end.  The leading constant-direction pairing must remain signed, or the drift deficit
must be dynamically small enough to interact with selector dissipation.
The normalized form identifies the sharp useful scale of that smallness.  Formally,
\(\|e\times\omega\|_2^4\lesssim[W(1-\alpha)]^2\Omega\), so a uniform bound on
\(W(1-\alpha)\) would put the transverse vorticity in the critical
\(L_t^4L_x^2\) class.  The scalar charge implication is checked in Lean.  What is not checked
is the decisive geometry: selecting the orbitwise directions without overlap, assembling them
into a global unit field with controlled gradient, and deriving the near-unit drift deficit
from Navier--Stokes dynamics or selector dissipation.
The drift deficit can in fact be balanced locally rather than postulated at a fixed fraction.
On \(W>c>0\), choose \(\alpha=1-c/W\).  Lean then checks both branches: a slow persistent
segment satisfies \(e_\gamma d_\gamma\ge3(\theta c)^2\), independent of \(W\), while a
ballistic segment has normalized-direction error at most \(2cL/W\), and therefore the formal
cross-component ledger becomes
\(\|e\times\omega\|_2^4\lesssim c^2\Omega\).  This resolves the static choice-of-\(\alpha\)
tradeoff and removes an explicit peak-amplitude loss from both branches.  It does not make the
total slow direction charge energy-paid, or supply the return selection
or the global direction field.

There is also a sharp regression test for that last step.  The exact periodic shear
\(u_N=-(e^{-\nu N^2t}/N)(\cos Nz,\sin Nz,0)\) has vorticity direction
\(\xi_N=(\cos Nz,\sin Nz,0)\).  Every vortex line is straight and \(\xi_N\) is constant along
it, yet \(\|\nabla\xi_N\|_\infty=N\).  Thus line curvature gives no transverse regularity,
even inside the class of smooth Navier--Stokes solutions; viscosity pays this example on the
\(N^{-2}\) time scale.  `NSFormal/Anisotropy.lean` checks the unit direction, exact constancy
on self-directed lines, and the antipodal change across distance \(\pi/N\).  A viable assembly
lemma must charge transverse variation to diffusion or spectral transfer rather than silently
replacing directional curvature by a full gradient.
The proof of the variable-direction anisotropic criterion sharpens this into a quantitative
target.  With
\(\mathcal A_e=\int|u||\nabla u||\nabla e|\), its periodic integration-by-parts ledger is
\(\|Se\|_2^4\le\frac18\|e\times\omega\|_2^4+C\mathcal A_e^2\).  Once the adaptive
ballistic term is inserted, the minimal assembly condition is
\(\int_0^T\mathcal A_e^2dt<\infty\).  The stronger condition
\(\int_0^T\Omega\|\nabla e\|_\infty^2dt<\infty\) follows by Hölder and energy monotonicity
and accepts the shear regression because its \(N^2\) direction cost is integrated against an
\(N^{-2}\) diffusive time scale.  Both fourth-power scalar ledgers are checked in
`NSFormal/NewProofAlgebra.lean`, and the coordinatewise periodic three-factor integration by
parts is checked in `NSFormal/PeriodicIntegration.lean`.
`NSFormal/AnisotropicIntegration.lean` now also sums the components and cancels the middle term
under differentiated incompressibility.  It proves the pointwise two-term coordinate envelope
and the exact `54` finite-sum integral bound as well, then instantiates the envelopes with the
Euclidean velocity norm and coordinate-`ℓ¹` gradients.  The latter are fixed-dimension
equivalents of Frobenius norms.
`NSFormal/AnisotropicCriterion.lean` closes the remaining finite-dimensional interface:
for the concrete torus gradient, strain, curl, and cross product it proves the exact integrated
identity, the explicit \(5832=2\cdot54^2\) fourth-power estimate, and the time-integrability
handoff.  Its zero-velocity/constant-coordinate-direction example proves that the combined
smoothness, incompressibility, integrability, and unit-vector hypotheses are nonvacuous.  It
also proves that every derivative, strain, and curl term is unchanged after subtracting an
arbitrary spatially constant velocity \(a(t)\), yielding the sharper Galilean-invariant debit
\(\mathcal A_{e,a}=\int|u-a||\nabla u||\nabla e|\).

Normalizing \(e=\xi=\omega/|\omega|\) on a selected region with
\(\rho=|\omega|>0\) yields a more focused debit.  The exact identity
\(|\nabla\omega|^2=|\nabla\rho|^2+\rho^2|\nabla\xi|^2\) gives
\[
 \mathcal A_{\xi,A,a}^2\le
 \left(\int_A|\nabla\omega|^2\right)
 \left(\int_A\frac{|u-a|^2|\nabla u|^2}{|\omega|^2}\right).
\]
On \(A\subset\{|\omega|\ge\theta W\}\), the second factor is at most
\((\theta W)^{-2}\int_A|u-a|^2|\nabla u|^2\).  The amplitude--direction identity, the weighted
Cauchy ledger, and this high-set inverse-square bound are checked in
`AnisotropicCriterion.lean` and `Budget.lean`.  Direct strain-budget absorption actually
requires the scale-invariant product \(Q_{A,a}\Omega\), not \(Q_{A,a}\) alone: the standard
interpolation gives
\(\mathcal N_A\lesssim\|S\xi\|_2\Omega^{1/4}P_A^{3/4}
\lesssim P_A(Q_{A,a}\Omega)^{1/4}\).
The resulting implication \(C^4Q_{A,a}\Omega\le\nu^4\Rightarrow\mathcal N_A\le\nu P_A\) is
checked algebraically in `NewProofAlgebra.lean`.  Its analytic interpolation and localization
remain to be connected to the concrete PDE.  No present estimate shows \(Q_{A,a}\Omega\) is
small: that is now an explicit dynamical target, along with constructing and patching the
selected direction without creating an uncontrolled interface charge.

There is, however, a concrete high-concentration sub-branch.  Taking \(a\) to be the spatial
mean and applying torus Poincaré--Sobolev, Calderón--Zygmund, and
\(L^2\)-\(L^\infty\) interpolation gives
\[
 Q_{A,a}\Omega\lesssim
 \theta^{-2}W^{-4/3}\Omega^{8/3}
 =\theta^{-2}\left(\frac{\Omega^2}{W}\right)^{4/3}.
\]
Hence sufficiently large scale-invariant concentration \(W/\Omega^2\), with the threshold
depending on \(\nu\) and the analytic constants, is compatible with viscous absorption.
`weighted_quotient_concentration_exponent_chain` checks the fractional-exponent identity
in Lean; the functional estimate is still prose.  The complementary regime
\(W\lesssim\Omega^2\) remains open and must interact with recurrence or signed spectral
transfer rather than being declared harmless.

Spatial analyticity shows why this is exactly critical.  At the escape times used in
[Grujić's geometric measure criterion](https://arxiv.org/abs/1111.0217), the vorticity
analyticity radius is comparable to \(\sqrt{\nu/W}\).  Cauchy control around a maximum then
forces a fixed-fraction core of volume \(\gtrsim\nu^{3/2}W^{-3/2}\), so
\(\Omega^2\gtrsim\theta^4\nu^3W\), equivalently
\(W/\Omega^2\lesssim\theta^{-4}\nu^{-3}\).
`analytic_volume_forces_critical_concentration_cap` checks the scalar volume-to-ratio
implication.  The periodic analytic-radius/core-volume theorem remains to be formalized.
Crucially, this upper cap has the same \(\nu^{-3}\) scaling as the sufficient lower
concentration threshold.  The route has no exponent margin; a proof would have to extract a
constant improvement from directional sparseness, the centered frame, or signed dynamics.

The mathematical gap is therefore no longer the periodic anisotropic algebra.  It is
constructing such an \(e\) and proving its parabolic debit or the critical weighted-quotient
bound \(Q_{A,a}\Omega\lesssim\nu^4\), including the turning population and patch interfaces.
The remaining issue is a measurable, non-overcounting return selection for normalized
elementary solenoids and its relation to signed line work.

An unoriented tensor relaxation removes much of that construction gap.  Writing
\(P=e\otimes e\), the mixed integration error is
\(-\sum_{ijk}\int u_j\partial_k u_i\partial_iP_{jk}\), a single derivative of \(P\).
The identity remains valid for any symmetric trace-one positive director tensor.  Positive
eigenframe weights sum to one, so \(\operatorname{tr}(PS^2)\) still dominates the least squared
strain eigenvalue.  Applying one Frobenius Cauchy--Schwarz estimate to the complete
27-dimensional contraction removes the earlier coordinate-counting loss and gives
\[
 \Sigma_P^2\le X_P^2/8+2(\mathcal A_P^F)^2,
 \qquad
 \mathcal A_P^F=\int|u-a||\nabla u|_F|\nabla P|_F.
\]

This permits the explicit global selector
\[
 P_c=\frac{\omega\otimes\omega+(c^2/3)I}{|\omega|^2+c^2}.
\]
It interpolates smoothly through \(I/3\) at vorticity zeros and forgets every sign choice.
Moreover
\[
 |\omega|^2-\omega\cdot P_c\omega
 =\frac{2c^2}{3}\frac{|\omega|^2}{|\omega|^2+c^2}\le\frac{2c^2}{3},
\]
so its transverse fourth-power charge is uniformly finite on bounded time intervals.  The
new load-bearing derivative calculation is the exact rotationally invariant identity
\[
 \|dP_c(w)[h]\|_F^2
 =2\frac{|w|^2|h|^2-(w\cdot h)^2}{(|w|^2+c^2)^2}
 +\frac83\frac{c^4(w\cdot h)^2}{(|w|^2+c^2)^4}.
\]
It vanishes exactly at \(w=0\) and implies
\[
 \|dP_c(w)[h]\|_F^2\le\frac{14}{3}
 \frac{|w|^2|h|^2}{(|w|^2+c^2)^2}.
\]
Writing
\[
 P_F=\int|\nabla\omega|_F^2,
 \qquad
 Q_c^F(a)=\int |u-a|^2|\nabla u|_F^2
   \frac{|\omega|^2}{(|\omega|^2+c^2)^2},
\]
the complete checked ledger is therefore
\[
 \boxed{\Sigma_{P_c}^2\le
 c^4|\mathbb T^3|^2/18+\frac{28}{3}P_FQ_c^F(a).}
\]
This improves the previous coordinate constant by more than five orders of magnitude and,
more importantly, assigns zero quotient density at a vorticity zero.

The gain does not by itself beat critical scaling.  If \(r=|\omega|^2\), then
\(r/(r+c^2)^2\le1/(4c^2)\), so a global fallback still recreates the
\(Ac^4+D/c^2\) optimization and returns to \(\Omega P\).  The useful new decomposition is
instead
\[
 Q_c^F\le
 \int_{r<c^2}|u-a|^2|\nabla u|_F^2\frac r{c^4}
 +\int_{r\ge c^2}\frac{|u-a|^2|\nabla u|_F^2}{r}.
\]
The low set retains a small-amplitude factor.  Moreover the exact differential separates the
direction charge \(D_\xi=\int r|\nabla\xi|^2\) from the scalar-amplitude charge
\(D_\rho=\int|\nabla\sqrt r|^2\).  The radial quotient kernel
\(c^4r/(r+c^2)^4\) has maximum \(27/(256c^2)\) and decays like \(c^4/r^3\) on the high set.
This is the first director formulation which sees the planar constant-direction test
correctly: its angular charge is zero, leaving a radial debit that scalar-vorticity diffusion
may be able to pay.

A subsequent stress test gives a cleaner production-level reduction.  Periodic integration by
parts and \(\nabla\cdot(\rho\xi)=0\) cancel every scalar-amplitude derivative in the actual
enstrophy production:
\[
 N=\int\rho^2(u-a)\cdot
   [\xi\,\nabla\cdot\xi-(\xi\cdot\nabla)\xi].
\]
The expansion and curvature vectors are orthogonal, so their square is at most
\(2|\nabla\xi|_F^2\).  The factor `2`, rather than the earlier coarse `4`, uses that
direction derivatives lie in the rank-two tangent plane; a checked equality jet shows it is
sharp.  There is a still narrower exact charge
\[
 G_\omega:=\int\frac{|(\omega\cdot\nabla)\omega|^2}{|\omega|^2},
 \qquad
 K_\omega:=\int\frac{|P_{\omega^\perp}(\omega\cdot\nabla)\omega|^2}{|\omega|^2},
\]
with both quotients set to zero where \(\omega=0\).  Away from that set,
\(G_\omega\) is exactly
\(\int\rho^2[(\nabla\cdot\xi)^2+|(\xi\cdot\nabla)\xi|^2]\), while \(K_\omega\) is the
line-curvature term.  With the exact minimizing frame
\(a_\omega=(\int\rho^2u)/(\int\rho^2)\), the checked hierarchy is
\[
 N^2\le G_\omega V_\omega
 \le(2D_\xi-K_\omega)V_\omega
 \le2D_\xi V_\omega,
 \qquad V_\omega=\int\rho^2|u-a_\omega|^2.
\]
Also \(G_\omega\le P\), since it is the palinstrophy carried by differentiation along the
vorticity direction.
Writing total palinstrophy as \(P=D_\rho+D_\xi\), direct viscous absorption is reduced to the
dimensionless condition
\[
 (G_\omega/P)(V_\omega/P)\le\nu^2,
\]
with the weaker sufficient version
\(2(D_\xi/P)(V_\omega/P)\le\nu^2\).  Unlike a bare critical velocity criterion, the exact
condition is automatic for constant-direction planar states because \(G_\omega=0\).  The
unconditional Young fallback leaves
\(E_\omega'+\nu D_\rho\le V_\omega/(2\nu)\), while the standard estimate
\(V_\omega\lesssim\|u-a\|_3^2(D_\rho+\|\rho\|_2^2)\) shows that absolute Sobolev control alone
returns to the critical \(L^3\) obstruction.  This multiplicative direction/velocity-variance
criterion is now the preferred production-level target; the tensor quotient remains useful for
middle-eigenvalue packaging and as an independent route.

The exact product cannot be uniformly small for all initial amplitudes.  The explicit smooth
field
\(u=(\sin z,\sin x,\sin y)\),
\(\omega=(\cos y,\cos z,\cos x)\) is divergence-free with \(\omega=\nabla\times u\), has
positive \(G_\omega,V_\omega\), and has weighted optimal frame zero.  Scaling its amplitude by
\(A\) leaves \(G_\omega/P\) unchanged but multiplies \(V_\omega/P\) by \(A^2\).  The exact
product therefore grows like \(A^2\), an exponent chain checked in
`NSFormal/NewProofAlgebra.lean`.  Any continuation proof based on this ledger must derive
dynamic depletion near a hypothetical singular time or pay the early large-amplitude interval;
it cannot assume pointwise absorption from time zero.

There is nevertheless an energy-paid dynamic criterion.  Standard torus Sobolev estimates
give
\(V_\omega(a_\omega)\lesssim E_\omega^{3/2}P^{1/2}\).  With
\(\Theta_G=G_\omega/P\), the exact quotient ledger and the sharp `3/4` Young inequality imply
\[
 E_\omega'+\frac\nu2P\lesssim_\nu \Theta_G^2E_\omega^3.
\]
Hence \(\int^T\Theta_G^2E_\omega^2<\infty\) is a continuation criterion.  A particularly
concrete sufficient condition is
\(\sup_{t\to T}\Theta_G(t)^2E_\omega(t)<\infty\), because the ordinary kinetic-energy identity
pays \(\int_0^T E_\omega\).  This payment and the complete implication are now concrete Lean
theorems: `NSFormal/KineticEnergy.lean` derives the exact energy identity and time budget from
the actual classical Navier--Stokes predicate, while
`NSFormal/ConcreteDynamicCriterion.lean` derives the enstrophy rate and its exponential bound
for the actual velocity, pressure, and vorticity fields.  The next research problem is therefore
to rule out persistent
alignment of a fixed fraction of palinstrophy with the vorticity direction at a rate worse than
\(E_\omega^{-1/2}\).  This is weaker than instantaneous absorption and compatible with an
arbitrarily large early transient.

The \(\Theta_G\) condition is only one sufficient channel.  Nonconstant Beltrami/ABC fields
have positive \(G_\omega,V_\omega\) but zero total production by periodic integration of
\(u\cdot\nabla(|u|^2/2)\); their arbitrarily large heat-decaying Navier--Stokes solutions are a
regression test against treating the absolute Cauchy bound as necessary.  Define
\(\mathfrak c=[N]_+^2/(G_\omega V_\omega)\in[0,1]\), with value zero when the denominator
vanishes.  The dynamic remainder is then proportional to
\(\mathfrak c^2\Theta_G^2E_\omega^3\).  The active program therefore has two complementary
targets: prove linewise anisotropic depletion of \(\Theta_G\), or use signed recurrence/flux
structure to deplete the correlation \(\mathfrak c\).  This connects the new quotient ledger
back to the signed filtered-flux work without hiding cancellation under an absolute value.

There is an exact simplification which makes the second channel substantially cleaner.  Since
\(\mathfrak c(QV)=[N]_+^2\) and \(\Theta_GP=Q\),
\[
 (\mathfrak c^2\Theta_G^2E_\omega)(PV)^2=[N]_+^4E_\omega,
 \qquad
 \mathfrak c^2\Theta_G^2E_\omega
   =\frac{[N]_+^4E_\omega}{(PV)^2}. \tag{5.1a}
\]
Both identities, including all zero-denominator cases, and the resulting concrete
classical-solution continuation theorem are now checked in Lean.  The quotient \(Q\) therefore
cancels from the signed critical target.  The dynamic problem can be attacked directly as
control of positive total stretching relative to the product of palinstrophy and weighted
velocity variance.  This retains the ABC/Beltrami regression test automatically because
\([N]_+=0\) there.

Near-saturation now has an exact rigidity ledger rather than a slogan.  For Hilbert-valued
fields \(f,g\), with \(Q=\int|f|^2\), \(V=\int|g|^2\), and
\(N=\int\langle f,g\rangle\), Lean checks
\[
 QV-N^2=Q\int\left|g-\frac{N}{Q}f\right|^2. \tag{5.1b}
\]
In the vortex-stretching application, \(f\) is the normalized vorticity self-transport and
\(g\) is the vorticity-weighted velocity (with the sign reversed for positive production).
The abstract identity is now instantiated on the concrete Haar torus, and smoothness discharges
all of its integrability premises.  Moreover, equality is proved equivalent to the almost-
everywhere residual equation.  Clearing the zero-safe normalization gives
\[
 |\omega|^2(u-a)+\frac{N}{Q}(\omega\!\cdot\!\nabla)\omega=0
 \quad\hbox{a.e.} \tag{5.1c}
\]
The component parallel to ω and the orthogonal projection are separately kernel-checked,
isolating scalar-amplitude transport from vortex-line bending.  Thus persistent large signed
correlation forces an approximate nonlinear eigen-relation, not merely a large scalar integral.

The parallel equation has a further global consequence that survives the vorticity zero set.
Divide it by \(|ω|^2+2ε\), use
\(ω·(ω·∇)ω=(ω·∇)(|ω|^2/2)\), and integrate the resulting
logarithmic transport.  Periodicity and `div ω = 0` cancel that term.  Dominated convergence
as \(ε\downarrow0\) then gives

\[
  \int_{\mathbb T^3}\omega\cdot(u-a)=0. \tag{5.1d}
\]

Lean checks the regularized chain rule, transport cancellation, and limit.  A periodic curl has
zero mean, so the constant frame drops and exact saturation forces zero ordinary helicity
\(∫u·ω=0\).  The stable version is now checked too.  Writing
\(H_a=∫ω·(u-a)\), \(D=QV-N^2\), and
\(\operatorname{Vol}=∫_{\mathbb T^3}1\), the residual test
\(ψ_ε=|ω|ω/(|ω|^2+2ε)\) has norm at most one and gives

\[
  Q H_a^2 \le \operatorname{Vol}(\mathbb T^3)D. \tag{5.1e}
\]

For `ω = curl u`, \(H_a=H=∫u·ω\).  Thus any nonzero-helicity slice with
\(Q\ne0\) has the explicit gap \(D\ge QH^2/\operatorname{Vol}\) from exact Cauchy saturation.
The argument now localizes.  For every smooth scalar weight \(\phi\), divergence-free
transport and the logarithmic chain rule give the exact error identity
\[
 \int \phi\,
   \frac{(\omega\cdot\nabla)(|\omega|^2/2)}{|\omega|^2/2+\varepsilon}
 =-\int (\omega\cdot\nabla\phi)
   \log(|\omega|^2/2+\varepsilon). \tag{5.1f}
\]
Let \(H_{a,\phi}^{\varepsilon}\) be the cutoff-weighted centered helicity on the left
of the residual test and let
\(J_{\varepsilon,\phi}=\int(\omega\cdot\nabla\phi)
\log(|\omega|^2/2+\varepsilon)\).  Lean checks the corrected estimate
\[
 Q\left(H_{a,\phi}^{\varepsilon}
       -\frac{N}{2Q}J_{\varepsilon,\phi}\right)^2
 \le \left(\int\phi^2\right)D. \tag{5.1g}
\]
In particular, if \(\omega\cdot\nabla\phi=0\), dominated convergence gives
\[
 Q\left(\int \phi\,\omega\cdot(u-a)\right)^2
 \le \left(\int\phi^2\right)D. \tag{5.1h}
\]
The approximate error has a scale-aware bound.  Since
\(\int(\omega\cdot\nabla)\phi=0\), any constant \(k\) may be subtracted from the
logarithm.  Hence
\[
 |J_{\varepsilon,\phi}|
 \le B_{\varepsilon,\phi}(k):=
 \left(\int|\omega\cdot\nabla\phi|\right)
 \left\|\log(|\omega|^2/2+\varepsilon)-k\right\|_{L^\infty}. \tag{5.1i}
\]
Combining this with (5.1g), Lean checks the robust positive-part gap
\[
 Q\left(
   \max\left\{|H_{a,\phi}^{\varepsilon}|-
     \left|\frac{N}{2Q}\right|B_{\varepsilon,\phi}(k),0\right\}
   \right)^2
 \le \left(\int\phi^2\right)D. \tag{5.1j}
\]
Exact saturation therefore annihilates helicity against every smooth vorticity first
integral.  This removes cancellation between invariant vortex regions whenever they admit
such a weight.  It does **not** assume that a generic vorticity field possesses a nonconstant
global first integral; chaotic line fields may have only constants.  The next dynamic target
is consequently concrete: construct tube-localizing weights for which the signal on the left
of (5.1j) stays positive.  The free center \(k\) removes the additive amplitude logarithm;
what must actually be controlled is along-vorticity leakage times the oscillation of the
logarithmic energy, including its behavior near the vorticity zero set.

This localization passes the concentration scaling audit.  Under the Navier--Stokes profile
scaling, \(Q\mapsto\lambda^3Q\), \(D\mapsto\lambda^6D\), and localized helicity is
invariant; a weight supported at the concentration scale has
\(\int\phi^2\mapsto\lambda^{-3}\int\phi^2\).  Both sides of (5.1h) therefore acquire
exactly \(\lambda^3\).  `DynamicCriterion.lean` checks this equivalence algebraically.  The
constant weight in (5.1e) lacks the compensating \(\lambda^{-3}\), explaining why global
helicity alone is too weak at small scales and why localization is structurally necessary.

The routine Cauchy premise is no longer part of that research target.  For a classical time
slice, `C²` regularity and `ω = curl u` now imply `div ω = 0`; the factorization follows
automatically, including its zero-quotient branch.  The same representative-independent
Fréchet calculus discharges the mixed derivatives and integrability in the periodic div--curl
identity.  Consequently the direct continuation theorem assumes neither factorization nor
`\int|\nabla u|^2=\int|\omega|^2`.

Two exact-flow regressions clarify what a future estimate must preserve.  Planar/shear flows
have \((\omega\cdot\nabla)\omega=0\), hence \(Q=N=0\).  Nonconstant Beltrami/ABC fields can have
nonzero local self-transport and weighted variance while their signed total production is zero
by periodic transport cancellation.  Both therefore satisfy the signed target with zero left
side.  Conversely fixed-shape amplitude scaling sends
\((N,E,P,V)\mapsto(A^3N,A^2E,A^2P,A^4V)\), so
\([N]_+^4E/(PV)^2\mapsto A^2[N]_+^4E/(PV)^2\).  No static homogeneous inequality can supply
the required uniform bound; time evolution, signed cancellation, or recurrence must do real
work.

There is also an exact vector frame improvement.  With
\(g_c^F=|\nabla u|_F^2r/(r+c^2)^2\), the constructed minimizing constant frame is
\(a_c^F=(\int g_c^Fu)/(\int g_c^F)\), and the full Haar identity is
\[
 Q_c^F(a)=Q_c^F(a_c^F)+(\int g_c^F)|a-a_c^F|^2.
\]
`NSFormal/DirectorTensor.lean` checks the exact radial/angular differential, Frobenius
contraction, coefficient \(28/3\), sharp quotient handoff, and this vector-valued optimum.
`NSFormal/Budget.lean` checks the low/high split and both kernel maxima.  What remains is not
selector construction: it is PDE control of the optimally centered \(Q_c^F\), preferably after
separating direction and scalar-amplitude dissipation, plus the matrix
eigendecomposition/continuation packaging.  This tensor route is now preferable to directly
patching an oriented vortex-line field unless recurrence supplies additional signed
information.

`NSFormal/VortexStretching.lean` independently checks the exact direction-only production
identity, the sharp constant-`2` zero-safe vector bound and equality example, the stronger
projected-transport correction, the exact self-transport quotient ledger, its domination by
palinstrophy, and the vorticity-energy-weighted optimal frame.  `NSFormal/NewProofAlgebra.lean`
checks the resulting total-diffusion absorption criteria and the scalar-amplitude Young
fallback.  The remaining research problem is to control the scale-invariant product
\((G_\omega/P)(V_\omega/P)\), not to assume either factor is small.

`NSFormal/Enstrophy.lean` now connects that kinematic ledger to the actual classical PDE.  It
proves compatibility of the quotient-coordinate derivatives with `torusPartial`, the global
time derivative of Haar enstrophy, zero mean of the scalar Laplacian, cancellation of
vorticity transport, and the exact balance (E_\omega'=N-\nu P).  It then proves that this
concrete (N) is the same periodic stretching density bounded by the quotient/optimal-frame
theorem.  `NSFormal/DynamicCriterion.lean` proves the corrected logarithmic continuation step:
(Theta^2E\le M) and the energy-paid bound (int E\le B) imply
(E(t)\le E(0)e^{CMB}) once the cubic rate inequality is available.  Accordingly, the next
load-bearing target is sharply localized.  `NSFormal/NewProofAlgebra.lean` now proves the
root-free bridge from `N² ≤ QV`, `Q ≤ ΘP`, and `V² ≤ K E³P` to
`N ≤ (ν/2)P + 27KΘ²E³/(32ν³)`, so no fractional-power algebra remains conjectural.  What is
more, `NSFormal/SpatialInterpolation.lean` proves all three concrete Haar-measure Cauchy links,
their sixth-power assembly `V⁶ ≤ U₆²W₆W₂³`, the identity `W₂=2E`, and the signed production
remainder.  The parenthetical div--curl obligation has now been discharged:
`NSFormal/DivCurl.lean` derives differentiated incompressibility from ordinary divergence-free
and mixed-partial commutation and proves `∫|∇u|²=∫|curl u|²`.  The bottom-up Sobolev transfer has
now reached the critical theorem.  `NSFormal/PeriodicSobolev.lean` proves full three-coordinate
tensorization and global mean-zero Poincare on the actual Haar torus, while
`NSFormal/PeriodicSobolevEuclidean.lean` proves periodic `H¹ → L⁶` through a measurable cube,
fixed smooth cutoff, Euclidean Gagliardo--Nirenberg--Sobolev, and a `125`-cell multiplicity
bound.  It supplies extended-norm, real-norm, and sixth-moment forms and identifies its descended
Fréchet derivative with the concrete coordinate derivatives.  The standard adapter is now
proved: componentwise Poincare absorbs the lower-order `L²` term; operator/Frobenius comparison
rewrites the derivative norm as gradient energy; the enstrophy definition of palinstrophy is
proved equal to that same energy; and the mean of a periodic curl is proved zero.  Consequently
`SpatialInterpolation.lean` discharges both sixth-moment premises and gives the signed cubic
production remainder directly.  It also proves the unconditional quotient bound `Q ≤ P`,
constructs the actual zero-safe factor `Θ=Q/P` in `[0,1]`, proves the exact reconstruction
`Q=ΘP`, and inserts that concrete factor into the production estimate.  This does not close the
dynamics: the novel research target is to show actual time-dependent decay of `Θ`, or of its
signed correlation, along every potential singular evolution.

There is no longer an abstract-record gap between those spatial theorems and a classical
solution.  `PeriodicRegularity.lean` discharges the routine smoothness-to-integrability side
conditions, `KineticEnergy.lean` supplies the energy-paid time budget, and
`ConcreteDynamicCriterion.lean` assembles the explicit estimate
\[
 E_\omega(t)\le E_\omega(a)
 \exp\!\left(\frac{27C_S}{4\nu^3}M\frac{K(a)}{2\nu}\right)
\]
under the actual Navier--Stokes and vorticity predicates and
\(\Theta_G^2E_\omega\le M\).  Positivity of enstrophy on the interval is presently an explicit
premise; the zero-enstrophy branch is a small formal endgame still to be packaged.  The
millennium-scale content remains the dynamic bound itself.

The signed refinement has also been stress-tested formally.  The zero-safe correlation is in
`[0,1]`, vanishes for zero total production, and is invariant under the positive amplitude
scaling `(N,G,V) ↦ (A³N,A²G,A⁴V)`.  Thus it correctly detects the Beltrami cancellation,
but a generic nonzero correlation leaves the same amplitude-critical growth.  The more relevant
parabolic regression is sharper: `(N,Q,V,P,E) ↦ (λ³N,λ³Q,λ³V,λ³P,λE)` fixes both
`𝔠` and `Θ=Q/P`, so `𝔠²Θ²E` grows exactly by `λ`; a positive fixed profile generates an
unbounded family.  Any successful correlation channel must therefore prove actual profile
deformation or dynamic decay near concentration.  Normalization alone cannot provide it.

### WP4b. Build scale-localized approximate first integrals

The new inequalities (5.1f)--(5.1j) define a separate, scale-critical experiment.  On an
active vortex tube or recurrent line bundle, construct a smooth weight \(\phi\) which is
essentially transverse to the vorticity flow and supported at the active radius.  The target is
not merely small \(\omega\cdot\nabla\phi\); it is the signed dominance
\[
 |H_{a,\phi}^{\varepsilon}|>
 \left|\frac{N}{2Q}\right|B_{\varepsilon,\phi}(k)
\]
on enough high-production times to force a defect through (5.1j).  A finite vortex segment
will necessarily leak at its end caps, so recurrence or a closed-tube geometry must pay those
caps; transverse cutoff leakage is absent only when the tube boundary is genuinely invariant.
The free center \(k\) should track the tube's logarithmic amplitude, leaving only within-tube
energy oscillation.  Required regression tests are zero-helicity symmetric flows, chaotic
vortex-line regions with no global first integral, weights meeting the vorticity zero set, and
parabolically rescaled localized profiles.  Failure of this signal-to-leakage inequality would
rule out the helicity route without affecting the quotient/correlation program.

One decisive nonvacuity regression is now complete in `NSFormal/LocalizedHelicity.lean`.
On the actual measured torus, set
\[
 u=\left(1-\sin y\cos y,\ \tfrac12\sin x,\ \sin y\right),\qquad
 \omega=\left(\cos y,\ 0,\ \cos^2y-\sin^2y+\tfrac12\cos x\right),
 \qquad \phi=\cos y.
\]
The kernel checks that `omega = curl u`, that `omega` is divergence free and nowhere zero,
and that `omega dot grad phi = 0`.  Its self-transport is
\((0,0,-\tfrac12\cos y\sin x)\), so the zero-safe quotient has strictly positive integral.
Translation by a half-period proves that total helicity vanishes, while exact derivative
cancellations reduce weighted helicity to \(\int\cos^2 y>0\).  The first-integral gap therefore
gives a strictly positive Cauchy defect.  This shows that localized helicity can genuinely
recover a signal destroyed by global cancellation, even on a nondegenerate curl field with
`Q > 0`.  It does not yet construct an active-scale weight for an arbitrary evolving solution;
that universal geometric step remains WP4b.

There is also a sharp negative conclusion.  Dividing the gap by `Q V` gives the checked bound
\[
 \frac{N^2}{QV}\le
 1-\frac{H_{a,\phi}^2}{(\int\phi^2)V}.
\]
`DynamicCriterion.lean` proves that the loss on the right is concentration invariant: under
the active scaling, `H` stays fixed, `∫phi²` scales like `lambda^-3`, and `V` like
`lambda^3`.  Thus merely keeping a positive signal-to-leakage margin yields only a fixed
separation from Cauchy saturation.  That is not enough to neutralize the remaining critical
factor proportional to enstrophy.  The dynamic target must be stronger: the normalized
helicity loss must approach one at high enstrophy, the quotient fraction must decay, or the
time evolution of the weights must furnish a separately integrable gain.

The formal dynamic handoff now matches this target exactly.  Negative production is harmless
because the dangerous factor uses its positive part; for either sign, the localized gap bounds
the full critical product by
\[
 \left(\left(1-\frac{H_{a,\phi}^2}{(\int\phi^2)V}\right)\Theta\right)^2E.
\]
`localizedHelicity_refined_cubic_rate_bounded_of_energy_budget` proves that a uniform bound on
this quantity closes the logarithmic, energy-paid continuation argument.  Thus the remaining
WP4b question is no longer which scalar estimate would suffice, but whether evolving
vortex-tube weights can force this product to stay bounded along arbitrary smooth solutions.

A canonical candidate can now be analyzed without postulating transverse tube coordinates.
Average a bounded seed along the vorticity-line flow for length `L`.  The exact checked formula
\[
 (\omega\!\cdot\!\nabla)\phi_L(x)
 =\frac{\psi(\Phi_Lx)-\psi(x)}L
\]
gives leakage at most `2 ||psi||_infinity/L`.  Thus the leakage side of WP4b can always be made
small along a complete flow.  The signal side is the real obstruction.  The mean-ergodic
theorem, now specialized in `FlowAveraging.lean`, says that the norm retained by long discrete
averages is precisely the norm of the projection onto transport-invariant observables.  A
kernel-checked sign-flip isometry annihilates a nonzero seed after two steps, demonstrating
that no seed-independent lower bound is possible from averaging alone.

This reframes WP4b as a low-transport-frequency problem.  For a helicity seed `h`, one needs an
averaging length `L` for which its retained amplitude `r_L` satisfies at least
`r_L > C_log/L`, where `C_log` contains the centered logarithmic oscillation and the coefficient
from the corrected defect identity.  Exact invariants correspond to a nonzero zero-frequency
projection; approximate tubes can also work if spectral mass near zero decays slowly enough.
The next analytic target is therefore a Navier--Stokes-specific lower bound on this low-frequency
helicity mass, not a generic flow-box construction.

There is a clean way to make the averaged signal positive.  Let `A_L` be the forward averaging
operator on spatial `L^2` and use the Fejer-type weight `phi_L=A_L^*A_Lh`.  The formal Hilbert
calculation gives
\[
 H_{\phi_L}=\langle\phi_L,h\rangle=\|A_Lh\|_2^2=r_L^2,
 \qquad \|\phi_L\|_2\le r_L.
\]
Thus, after paying an effective leakage `delta_L`, the normalized correlation allowance is at
most `1-(r_L-delta_L)^2/V`.  The theorem
`retainedAverage_refined_cubic_rate_bounded_of_energy_budget` closes the full dynamic argument
from a uniform bound on
\[
 \left(\left(1-\frac{(r_L-\delta_L)^2}{V}\right)\Theta\right)^2E.
\]
This is stronger than merely asking `r_L>C_log/L`: beating leakage makes the gap nonzero, but
critical closure requires the displayed remaining allowance, together with `Theta`, to decay at
the enstrophy scale.  Any successful continuation proof must quantify both effects.

The functional-analytic realization is now sharper than that preliminary formulation.
`FlowKoopman.lean` identifies an important pitfall: an operator-valued Bochner integral would
require operator-norm continuity, which Koopman translation groups generally do not have.  It
instead constructs `A_L` by integrating each strongly continuous `L²` orbit and proves that this
pointwise integral is a bounded linear contraction.  For a continuous measure-preserving flow it
then proves the group and adjoint laws, the exact endpoint generator of `A_L`, and
\[
 \|U_\tau A_Lh-A_Lh\|_2\le 2|\tau|\|h\|_2/L.
\]
The same bound is propagated through the adjoint sign repair: `phi_L=A_L^*A_Lh` is in the
transport-generator domain and its generator has norm at most `2||h||_2/L`.  Hence the abstract
leakage debit is derived rather than postulated at the Hilbert-space level.

The concrete prototype is now checked as well.  `TorusFlow.lean` constructs the nontrivial
Haar-preserving shear `(x,y,z) ↦ (x+s cos y,y,z)`, proves that its nonzero generator
`(cos y,0,0)` is a genuine periodic curl, and identifies its pointwise generator with
`torusScalarTransport` on every scalar field differentiable along the transported coordinate.
The full strongly continuous Koopman and positive Fejér layers specialize to this moving flow,
including the nonconstant exact first integral `cos y` as an explicit nonzero retained `L²`
seed with positive signal.

The outstanding infrastructure is consequently narrower and better tested: construct the
global smooth Haar-preserving flow of an arbitrary concrete smooth divergence-free torus
vorticity, prove the generator identity in `L²` on the required smooth domain, and transfer its
bound to the centered-log `L¹` pairing.  Once this is built, the genuinely
Navier--Stokes-specific obstacle remains the lower bound on retained
helicity amplitude at the dynamically relevant averaging length—not boundedness of the average
and not generic flow-box existence.

### WP5. Do not return to the funnel prematurely

Blow-up compactness becomes useful only after a scale-critical bound supplies precompactness.
If a nonzero defect survives WP3--WP4, the correct limit object is initially an ancient
suitable Navier--Stokes solution with a defect measure.  Self-similarity, periodicity in
similarity time, or proximity to an Oseen column must be derived, never assumed.

## 6. Relation to rigorous literature

- [Constantin--Fefferman, *Direction of Vorticity and the Problem of Global Regularity for the
  Navier--Stokes Equations* (1993)](https://iumj.org/article/3627/): geometric depletion through
  vorticity-direction coherence.
- [Boutros--Titi, *On the Conservation of Helicity by Weak Solutions of the 3D Euler and
  Inviscid MHD Equations* (2024)](https://arxiv.org/abs/2410.00813): a rigorous local helicity
  balance and helicity-defect framework.  It reinforces that localization should be handled
  through a balance/flux error, not by treating helicity density as a passively conserved sign.
- [Perrella--Duignan--Pfefferlé, *Existence of Global Symmetries of Divergence-Free Fields with
  First Integrals* (2023)](https://arxiv.org/abs/2303.03191): first integrals, global symmetries,
  and flux coordinates on structured toroidal regions.  It supports using exact first-integral
  weights on genuine flux tubes while retaining the approximate-error theorem elsewhere.
- [Lei--Lin--Zhou, *Structure of Helicity and Global Solutions of Incompressible Navier--Stokes
  Equation* (2015)](https://arxiv.org/abs/1505.00142): a critical helicity-based energy structure
  that is conditionally coercive and produces large global solutions; useful evidence that
  helicity becomes effective only after an additional structural decomposition.
- [Miller, *A Locally Anisotropic Regularity Criterion for the Navier--Stokes Equation in Terms
  of Vorticity* (2020)](https://arxiv.org/abs/2002.02152): a unit direction field `v` with
  controlled spatial gradient reduces regularity to the critical condition
  \(v\times\omega\in L_t^4L_x^2\).  This is the closest existing criterion to the normalized
  ballistic direction above, but an orbitwise `e` is not yet a global Lipschitz field and the
  line ledger does not by itself supply the fourth-power time bound.
- [Zadrzyńska--Zajączkowski, *Stability of Two-Dimensional Navier--Stokes Motions in the
  Periodic Case* (2014)](https://arxiv.org/abs/1406.0693): global stability of periodic 2D
  motions for 3D data and forcing sufficiently close in stronger spaces.  It confirms the
  planar branch is stable under quantitative hypotheses, but those hypotheses are much
  stronger than the present flux-weighted tangent variance.
- [Cheskidov--Shvydkoy, *A Unified Approach to Regularity Problems for the 3D Navier--Stokes and
  Euler Equations* (2011)](https://arxiv.org/abs/1102.1944): low-mode/dissipation-wavenumber
  regularity criteria.  Their work is the closest precedent for the frequency reduction in
  Section 3.
- [Constantin--E--Titi, *Onsager's Conjecture on the Energy Conservation for Solutions of
  Euler's Equation* (1994)](https://doi.org/10.1007/BF02099744): the classical coarse-graining
  commutator method behind the cubic energy-flux estimate used in `DYNAMICS.md`.
- [Eyink, *The Cascade of Circulations in Fluid Turbulence*
  (2006)](https://arxiv.org/abs/physics/0606159): the filtered subgrid vortex force and its
  loop-circulation balance.  `DYNAMICS.md` uses the corresponding Hodge identity to show that
  energy flux and circulation flux are dual tests of the same curled force.
- [Gallay--Smets, *Spectral Stability of Inviscid Columnar Vortices*
  (2020)](https://arxiv.org/abs/1805.05064): genuine spectral stability of a class of columnar
  vortices, but not an organization theorem for arbitrary Navier--Stokes flow.
- [Grujic, *A Geometric Measure-Type Regularity Criterion*
  (2013)](https://arxiv.org/abs/1111.0217): regularity from local one-dimensional sparseness of
  intense superlevel sets.
- [Yu, *Filtered Vortex Stretching and Subgrid Defects*
  (2026 preprint)](https://arxiv.org/abs/2606.27560): finite-scale geometric near-field coercivity
  and an explicit identification of far-field, commutator, and localization defects.
- [Tsai, *On Leray's Self-Similar Solutions ... Satisfying Local Energy Estimates*
  (1998)](https://doi.org/10.1007/s002050050099): qualitative nonexistence of exact backward
  self-similar blow-up under its stated global hypotheses; it does not provide the manuscript's
  quantitative defect theorem.

All entries except Yu's are established reference points.  The 2026 Yu paper is a recent
preprint and should be independently checked rather than treated as a black box.

## 7. Current assessment of promise

The Oseen-tube/episode program is not promising as an unconditional route because its hardest
claim is exactly the missing theorem: arbitrary intense vorticity must become a controlled
tube.  The event and funnel machinery currently rename, rather than solve, the alternatives.

The geometric-cancellation plus diffusion program is promising enough to pursue, but only in
an averaged or dynamical form.  It is tied directly to exact Navier--Stokes identities, treats
aligned and incoherent directions by complementary mechanisms, and has a sharply identified
residual.  The flat-maximum example rules out the naive pointwise closure.  The global filtered
calculation in `DYNAMICS.md` now pays both the singular near field and far strain at exponent
\(1/3\).  Heat filtering identifies the exact signed defect as the positive scale derivative of
a cubic kinetic-energy flux.  The increment-only bound pays that flux only at exponent \(1/4\),
but the Lamb-vector representation improves it to exponent \(1/3\), exactly matching the
geometric scale.  It also rewrites flux as a signed integral along the measurable vortex-line
decomposition and, through the subgrid vortex force, as a smooth potential paired with the
circulation defect.  The safe terminal filter is impossible, and the persistent-triad test shows
that active excursions alone do not control even instantaneous flux.  The make-or-break point is
therefore no longer an exponent gap: it is whether signed active and persistent line estimates
can debit every positive high-tail recurrence against viscosity without taking an \(L^4\) norm.

The high-tail functional itself is now exactly characterized in finite shells.  If
\(g_i=T_i-R_i\), \(G_j=\sum_{i>j}g_i\), and
\(\vartheta_j=\mathbf1_{\{G_j>0\}}\), define
\(m_0=0\) and
\(m_i=\sum_{j<i}(\lambda_{j+1}-\lambda_j)\vartheta_j\).  Then

\[
 \sum_j(\lambda_{j+1}-\lambda_j)[G_j]_+
 =\sum_i m_i g_i
 =\sum_j(\lambda_{j+1}-\lambda_j)\vartheta_j\Pi_j-
   \sum_i m_iR_i.
\]

This multiplier realizes the maximum signed pairing among all \(q_0=0\) with
\(0\le q_{j+1}-q_j\le\lambda_{j+1}-\lambda_j\); these claims are kernel-checked in
`NSFormal/SpectralFlux.lean`.  The frontier can therefore be stated without positive parts:
bound the signed nonlinear work uniformly for this solution-dependent monotone
sub-Laplacian multiplier, while exploiting its accompanying dissipation and the coherent
ballistic branch.

That is the research frontier this repository should now attack.
