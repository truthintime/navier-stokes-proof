# Dynamic-scale reduction: what energy pays and what it cannot pay

Status: working research note, 2026-08-16.  This is not a proof of global regularity.
It develops the next step after `RESEARCH.md`: an exact fixed-scale filtered balance on the
torus, the largest dynamically affordable geometric filter scale, and the remaining
scale-transfer obstruction.

## 1. Result of this research step

There is a natural filtered scale at which both geometric near-field stretching and far-field
strain are paid by the ordinary energy identity:

\[
  \ell_G(t)=(1+\Omega(t))^{-1/3},
  \qquad \Omega(t)=\tfrac12\|\omega(t)\|_2^2.
  \tag{1.1}
\]

For a fixed filter length \(\ell\), the positive singular near-field stretching of the filtered
vorticity can be absorbed by filtered diffusion, with lower-order rate

\[
  C\nu^{-1}\|u_0\|_2^2\ell^{-3}.
  \tag{1.2}
\]

The far-field strain has rate

\[
  C\|u_0\|_2(1+\ell^{-5/2}).
  \tag{1.3}
\]

At (1.1), these become respectively

\[
 C\nu^{-1}\|u_0\|_2^2(1+\Omega),
 \qquad
 C\|u_0\|_2\bigl(1+(1+\Omega)^{5/6}\bigr),
 \tag{1.4}
\]

and both are time-integrable on finite intervals.  Thus the singular geometry and the remote
strain are not the remaining supercritical terms at this scale.  For heat filtering,
the global integration-by-parts estimate (4.3)--(4.6) pays the entire resolved stretching term
at the same exponent without even requiring the near/far decomposition.

The obstruction is the differentiated subfilter stress, together with the jump or derivative
created when the filter follows \(\ell_G(t)\).  Taking its absolute value produces a
scale-critical fourth power of velocity increments.  The Leray energy class supplies only the
parabolic \(L^{10/3}\) exponent and cannot control that fourth power; Section 5 gives an explicit
concentration family demonstrating the gap.  Keeping the sign reveals a better exact quantity:
for a heat filter, total filtered nonlinear enstrophy production is one half of the scale
derivative of a *cubic* kinetic-energy flux.  Section 8 then uses the Lamb-vector form of the
nonlinearity to pay the flux amplitude at the geometric scale itself.  The remaining defect is
pure positive scale/time variation, not an exponent mismatch.  Two further exact tests sharpen
that conclusion.  First, an adaptive heat scale which is both geometric-energy-paid and
viscosity-speed-safe cannot reach zero at a finite terminal time without forcing the
nonintegrable rate \((T-t)^{-3/2}\).  Second, energy and circulation transfer are dual pairings
of the same subgrid vorticity defect, but a smooth explicit torus triad has positive heat flux
and no active vorticity excursions.  Thus the remaining proof must debit persistent vortex
lines and recurrent high-tail transfer; neither a safe moving filter nor the active-excursion
measure alone can close it.

## 2. Exact fixed-scale filtered equation

Let \(P_\ell f=\phi_\ell*f\) be a smooth periodic convolution on \(\mathbb T^3\), where
\(\phi\) is nonnegative, smooth, and has unit mass.  For a fixed \(\ell>0\), define

\[
 U_\ell=P_\ell u,\qquad
 \Omega_\ell=\nabla\times U_\ell,\qquad
 S_\ell=\tfrac12(\nabla U_\ell+\nabla U_\ell^T),
\]

and the subfilter stress

\[
 R_\ell=P_\ell(u\otimes u)-U_\ell\otimes U_\ell.
\]

Filtering Navier--Stokes and taking curl gives the exact identity

\[
 \partial_t\Omega_\ell+(U_\ell\cdot\nabla)\Omega_\ell
 = (\Omega_\ell\cdot\nabla)U_\ell+\nu\Delta\Omega_\ell+F_\ell,
 \qquad F_\ell=-\nabla\times\nabla\cdot R_\ell.
 \tag{2.1}
\]

Consequently,

\[
 \frac12\frac d{dt}\|\Omega_\ell\|_2^2
 +\nu\|\nabla\Omega_\ell\|_2^2
 =\int_{\mathbb T^3}S_\ell\Omega_\ell\cdot\Omega_\ell
  +\int_{\mathbb T^3}F_\ell\cdot\Omega_\ell.
 \tag{2.2}
\]

No tube decomposition or phenomenological closure has entered.

## 3. The near field is absorbed by diffusion

Split the periodic strain kernel at radius \(R=\kappa\ell\), with \(\kappa>1\) fixed and
\(R\) below the torus injectivity radius.  Write \(S_\ell=S_\ell^{\rm near}+S_\ell^{\rm far}\).

Let \(\rho_\ell=|\Omega_\ell|\), and put
\(\xi_\ell=\Omega_\ell/|\Omega_\ell|\) away from the zero set.  The exact strain
representation contains the direction factor

\[
 (\widehat z\cdot\xi_\ell(x))
 \bigl(\widehat z\cdot(\xi_\ell(x-z)\times\xi_\ell(x))\bigr).
\]

Parallel and antiparallel directions therefore cancel.  The elementary inequality

\[
 \min(|a|,|b|)\left|\frac a{|a|}-\frac b{|b|}\right|\le2|a-b|
 \tag{3.1}
\]

handles the zero set through the magnitude weights.  If
\(\Lambda_\ell=\|\Omega_\ell\|_\infty\), the positive near-field work satisfies

\[
 \begin{aligned}
 \int (S_\ell^{\rm near}\Omega_\ell\cdot\Omega_\ell)_+
 &\le C\Lambda_\ell\int \rho_\ell(x)
      \int_{|z|<R}\frac{|\Omega_\ell(x)-\Omega_\ell(x-z)|}{|z|^3}\,dz\,dx\\
 &\le CR\Lambda_\ell\|\Omega_\ell\|_2\|\nabla\Omega_\ell\|_2.
 \end{aligned}
 \tag{3.2}
\]

The second line follows from Minkowski and
\(\|f(\cdot)-f(\cdot-z)\|_2\le|z|\|\nabla f\|_2\).  Young's inequality then gives

\[
 \int (S_\ell^{\rm near}\Omega_\ell\cdot\Omega_\ell)_+
 \le \frac\nu4\|\nabla\Omega_\ell\|_2^2
 +\frac{C R^2\Lambda_\ell^2}{\nu}\|\Omega_\ell\|_2^2.
 \tag{3.3}
\]

Filter smoothing and the energy inequality give

\[
 \Lambda_\ell
 \le \|\nabla\phi_\ell\|_2\|u(t)\|_2
 \le C\ell^{-5/2}\|u_0\|_2.
 \tag{3.4}
\]

Since \(R=\kappa\ell\), (3.3) becomes

\[
 \int (S_\ell^{\rm near}\Omega_\ell\cdot\Omega_\ell)_+
 \le \frac\nu4\|\nabla\Omega_\ell\|_2^2
 +\frac{C\|u_0\|_2^2}{\nu\ell^3}\|\Omega_\ell\|_2^2.
 \tag{3.5}
\]

This is a global torus version of filtered near-field coercivity.  It is kinematic except for
the energy bound in (3.4).

## 4. The far field is energy-paid

Outside radius \(R\), integrate \(\Omega_\ell=\nabla\times U_\ell\) by parts against the
cut-off periodic strain kernel.  The differentiated kernel is of size \(|z|^{-4}\), and

\[
 \left(\int_{R<|z|<1}|z|^{-8}\,dz\right)^{1/2}\le CR^{-5/2}.
\]

The smooth periodic remainder contributes only a constant.  Hence

\[
 \|S_\ell^{\rm far}\|_\infty
 \le C(1+R^{-5/2})\|U_\ell\|_2
 \le C(1+\ell^{-5/2})\|u_0\|_2,
 \tag{4.1}
\]

and

\[
 \int S_\ell^{\rm far}\Omega_\ell\cdot\Omega_\ell
 \le C\|u_0\|_2(1+\ell^{-5/2})\|\Omega_\ell\|_2^2.
 \tag{4.2}
\]

The shell calculation underlying the exponent \(5/2\) is the one formalized in
`NSFormal/FarField.lean`; its squared geometric constant is \(32/31\).

### A simpler global bound for resolved stretching

For a heat filter, the near/far split is not actually needed to pay the *resolved* stretching
term.  Since \(\nabla\cdot\Omega_s=0\), periodic integration by parts gives

\[
 \int\Omega_s\cdot(\Omega_s\cdot\nabla)U_s\,dx
 =-\int U_s\cdot(\Omega_s\cdot\nabla)\Omega_s\,dx.
 \tag{4.3}
\]

The periodic calculus used here is no longer only a prose convention:
`NSFormal/PeriodicIntegration.lean` proves the coordinate Leibniz rule, splits the actual
Haar-volume measure on `Torus3` by a volume-preserving equivalence, applies Fubini, and derives
the full scalar formula
\(\int f(u\cdot\nabla g)=-\int((u\cdot\nabla f)+f\nabla\cdot u)g\), together with its
divergence-free corollary.  Extending this checked scalar layer componentwise to (4.3) is now
bookkeeping rather than a missing boundary-cancellation principle.

Consequently,

\[
 \begin{aligned}
 \left|\int\Omega_s\cdot(\Omega_s\cdot\nabla)U_s\right|
 &\le \|U_s\|_\infty\|\Omega_s\|_2\|\nabla\Omega_s\|_2\\
 &\le \frac\nu4\|\nabla\Omega_s\|_2^2
   +\frac C\nu\|U_s\|_\infty^2\|\Omega_s\|_2^2.
 \end{aligned}
 \tag{4.4}
\]

Heat-kernel smoothing supplies

\[
 \|U_s\|_\infty^2\le C(1+s^{-3/2})\|u_0\|_2^2.
 \tag{4.5}
\]

At \(s_G=(1+\Omega)^{-2/3}\), the rate in (4.4) is therefore

\[
 \frac C\nu\|u_0\|_2^2(1+\Omega),
 \tag{4.6}
\]

which is time-integrable.  This recovers the same critical exponent \(1/3\) as the geometric
near-field calculation, but globally and with less structure.  Sections 3--4 remain useful
because they display the direction cancellation and give a filter-independent physical-space
decomposition.  For the heat-filter recurrence argument, however, (4.3)--(4.6) show that all
resolved stretching is already paid.  The only nonlinear obstruction is subfilter transfer and
the cost of revealing progressively finer scales.

## 5. The exact commutator defect

For \(\delta_z u(x)=u(x-z)-u(x)\), the stress has the exact cumulant form

\[
 R_\ell
 =\langle\delta u\otimes\delta u\rangle_{\phi_\ell}
  -\langle\delta u\rangle_{\phi_\ell}
   \otimes\langle\delta u\rangle_{\phi_\ell}.
 \tag{5.1}
\]

Differentiating the stress differentiates the filter.  Let \(M_{\ell,4}(x,t)\) denote the
sum of the fourth-moment increment averages against both probability kernels
\(\phi_\ell(z)\,dz\) and
\(\ell|\nabla\phi_\ell(z)|\,dz/\|\nabla\phi\|_1\).  Direct differentiation of (5.1) gives

\[
 \|\nabla\cdot R_\ell\|_2^2
 \le \frac C{\ell^2}\int_{\mathbb T^3}M_{\ell,4}(x,t)^4\,dx.
 \tag{5.2}
\]

Periodic integration by parts and Young's inequality yield

\[
 \begin{aligned}
 \left|\int F_\ell\cdot\Omega_\ell\right|
 &\le C\|\nabla\cdot R_\ell\|_2\|\nabla\Omega_\ell\|_2\\
 &\le\frac\nu4\|\nabla\Omega_\ell\|_2^2
  +\frac C{\nu\ell^2}\int M_{\ell,4}^4.
 \end{aligned}
 \tag{5.3}
\]

Combining (2.2), (3.5), (4.2), and (5.3) proves the fixed-scale inequality

\[
 \boxed{
 \begin{aligned}
 \frac12\frac d{dt}\|\Omega_\ell\|_2^2
 +\frac\nu2\|\nabla\Omega_\ell\|_2^2
 \le{}& C\left[
   \frac{\|u_0\|_2^2}{\nu\ell^3}
   +\|u_0\|_2(1+\ell^{-5/2})
 \right]\|\Omega_\ell\|_2^2\\
 &+\frac C{\nu\ell^2}\int M_{\ell,4}^4.
 \end{aligned}}
 \tag{5.4}
\]

Equation (5.4) is the main unconditional estimate of this note.

### Why energy does not control the last term

The Leray energy class gives the parabolic interpolation exponent

\[
 u\in L^{10/3}_{x,t,\mathrm{loc}},
\]

whereas (5.2)--(5.4) require fourth moments of increments.  This is a genuine gap, not a
poor choice of constants.

For example, let \(v\) be a fixed smooth divergence-free bump and set, schematically on a
unit cylinder,

\[
 u_\delta(x,t)=\delta^{-3/2}v(x/\delta)
 \quad\text{for a time interval of length }\delta^2.
 \tag{5.5}
\]

Then

\[
 \sup_t\|u_\delta(t)\|_2^2\simeq1,
 \qquad
 \int\|\nabla u_\delta\|_2^2dt\simeq1,
\]

but

\[
 \iint|u_\delta|^4\,dxdt\simeq\delta^{-1}\longrightarrow\infty.
 \tag{5.6}
\]

Thus no functional inequality from the energy class alone can sum the commutator defect.
Navier--Stokes evolution or a geometric cancellation of its *signed work* must be used.

## 6. Why the exponent \(1/3\) is forced

Set \(\ell=(1+\Omega)^{-\beta}\).  The near-field reservoir in (3.5) behaves like
\((1+\Omega)^{3\beta}\), so the energy identity pays it automatically only for
\(\beta\le1/3\).  The far-field rate behaves like
\((1+\Omega)^{5\beta/2}\), which permits \(\beta\le2/5\).  Therefore the geometric
near-field estimate, not the far field, fixes the common affordable exponent:

\[
 \boxed{\beta_G=\frac13.}
 \tag{6.1}
\]

At \(\beta=1/3\), finite-time integrability follows from

\[
 \int_0^T\Omega\,dt\le\frac{E_0}{2\nu},
 \qquad
 \int_0^T(1+\Omega)^{5/6}dt
 \le T^{1/6}\left(T+\frac{E_0}{2\nu}\right)^{5/6}.
 \tag{6.2}
\]

The earlier maximum-principle cutoff \((1+\Omega)^{-2/5}\) remains the finest scale whose
*linear strain* is paid directly.  The coarser \((1+\Omega)^{-1/3}\) is the finest scale at
which the quadratic filtered-enstrophy geometry is paid.  The band between them belongs to
the subfilter-transfer problem rather than to the far field.

## 7. The adaptive-scale defect

One cannot substitute \(\ell_G(t)\) directly into (5.4) without a new term.  A variable
convolution produces

\[
 \ell_G'(t)\,\partial_\ell(P_\ell\omega)|_{\ell=\ell_G(t)}.
 \tag{7.1}
\]

For a heat filter \(P_\ell=e^{\ell^2\Delta}\), this is

\[
 2\ell_G\ell_G'\Delta\Omega_{\ell_G}.
 \tag{7.2}
\]

When the scale shrinks, (7.2) is anti-diffusive.  A dyadic stopping-time construction avoids
the derivative but creates endpoint jumps

\[
 \|\Omega_{\ell/2}\|_2^2-\|\Omega_\ell\|_2^2,
\]

which measure enstrophy entering the newly resolved band.  These are two representations of
the same cascade defect.  Treating the filter as adaptive without paying (7.1), or changing
dyadic scales without paying the jumps, would hide the open problem in the definition.

## 8. Heat filtering exposes the signed cubic defect

The fourth moment in (5.2) is the price of estimating the differentiated stress in absolute
value.  There is an exact signed formulation with one less power of the velocity increment.
Put \(s=\ell^2\), use the heat filter \(P_s=e^{s\Delta}\), and define

\[
 E_s=\frac12\|P_su\|_2^2,\qquad
 Y_s=\frac12\|\nabla\times P_su\|_2^2,\qquad
 Z_s=\frac12\|\nabla(\nabla\times P_su)\|_2^2.
 \tag{8.1}
\]

If \(T_k\) is the nonlinear modal kinetic-energy transfer, define the forward heat-filtered
energy flux by

\[
 \Pi_s=-\sum_k e^{-2s|k|^2}T_k.
 \tag{8.2}
\]

For a smooth solution, differentiation of the Fourier series gives

\[
 \partial_sE_s=-2Y_s,
 \qquad
 \partial_tE_s+2\nu Y_s=-\Pi_s,
 \tag{8.3}
\]

and therefore

\[
 \boxed{
 \partial_tY_s+2\nu Z_s=\frac12\partial_s\Pi_s.}
 \tag{8.4}
\]

The right-hand side of (8.4) is exactly the sum of resolved vortex stretching and signed
subfilter work in (2.2).  Thus it is the *positive scale slope* of cubic energy flux, not the
absolute fourth-increment observable, which must be controlled.  The finite-mode derivative
identity \(\partial_s\Pi_s=2B_s\) is kernel-checked in
`NSFormal/SpectralFlux.lean`.

Equation (8.4) also makes the adaptive defect exact.  Along a differentiable scale \(s(t)\),

\[
 \frac d{dt}Y_{s(t)}+2(\nu+s'(t))Z_{s(t)}
 =\frac12\partial_s\Pi_s\big|_{s=s(t)}.
 \tag{8.5}
\]

Hence a scale schedule satisfying \(s'\ge-\nu/2\) retains at least \(\nu Z_s\) of
dissipation.  Faster shrinking is precisely anti-diffusion.  A useful stopping-time
construction must either respect this parabolic speed limit or debit the equivalent dyadic
band jump.

### A viscosity-safe terminal schedule is impossible

There is a decisive limitation on the first alternative.  Suppose a putative singular time is
\(T\), write \(X(t)=1+\Omega(t)\), and ask for an absolutely continuous scale \(s(t)\) which

1. stays coarse enough to pay the geometric estimates, so
   \(s(t)\ge s_G(t)=X(t)^{-2/3}\);
2. retains viscosity, so \(s'(t)\ge-\nu/2\); and
3. resolves the unfiltered field at the terminal time, so \(s(T)=0\).

Integrating the speed constraint backward from \(T\) gives

\[
 s(t)\le \frac\nu2(T-t).
 \tag{8.6}
\]

Combining the two bounds on \(s\) and raising to the negative power \(-3/2\) yields

\[
 X(t)\ge \left[\frac\nu2(T-t)\right]^{-3/2}.
 \tag{8.7}
\]

But \((T-t)^{-3/2}\) is not integrable at \(T\), whereas the kinetic-energy identity gives
\(\int_0^T\Omega(t)\,dt<\infty\).  Therefore no schedule can satisfy all three requirements.
The pointwise power implication and its measure-theoretic nonintegrability consequence are
kernel-checked in `NSFormal/NewProofAlgebra.lean` as
`safe_scale_schedule_not_integrable`.

This does not rule out blow-up.  It rules out closing the proof merely by following a
geometric-energy-paid filter while preserving a positive fraction of the filtered
palinstrophy.  A successful argument must sometimes shrink faster than the parabolic speed and
pay the resulting anti-diffusion, or equivalently use a stopping chain and debit every newly
resolved high-frequency band.  The high-tail recurrence problem is therefore unavoidable.

### An increment-only estimate appears to leave a \(1/12\) gap

The usual symmetrization of subfilter energy flux gives, for a compact smooth filter (and
with a Gaussian probability weight for the heat filter), the absolute estimate

\[
 |\Pi_\ell|
 \le \frac C\ell\int \psi_\ell(z)\|\delta_zu\|_3^3\,dz,
 \tag{8.8}
\]

where \(\psi_\ell\) has unit mass and finite scale-normalized moments.

For a divergence-free periodic field, Sobolev interpolation and the increment bounds give

\[
 \begin{aligned}
 \|\delta_zu\|_3^3
 &\le \|\delta_zu\|_2^{3/2}\|\delta_zu\|_6^{3/2},\\
 \|\delta_zu\|_2&\le \min(2\|u_0\|_2,|z|\|\nabla u\|_2),\\
 \|\delta_zu\|_6&\le C\|\nabla u\|_2.
 \end{aligned}
 \tag{8.9}
\]

Since \(\|\nabla u\|_2^2=2\Omega\), (8.8)--(8.9) imply

\[
 |\Pi_\ell|
 \le C\min\left(
   \ell^{1/2}\Omega^{3/2},
   \|u_0\|_2^{3/2}\ell^{-1}\Omega^{3/4}
 \right).
 \tag{8.10}
\]

At the geometric scale \(\ell_G=(1+\Omega)^{-1/3}\), the better of these elementary
bounds is

\[
 |\Pi_{\ell_G}|\le
 C\|u_0\|_2^{3/2}(1+\Omega)^{13/12}.
 \tag{8.11}
\]

This misses the energy-paid exponent by only \(1/12\).  At the coarser flux scale

\[
 \ell_\Pi=(1+\Omega)^{-1/4},
 \tag{8.12}
\]

the same bound is \(C\|u_0\|_2^{3/2}(1+\Omega)\), which is time-integrable.  Both
near- and far-field geometric rates remain energy-paid throughout the band

\[
 \ell_G\le\ell\le\ell_\Pi.
 \tag{8.13}
\]

Endpoint bounds do not control \(\partial_s\Pi_s\): the flux may oscillate in scale.  The
surviving object is its one-sided scale variation

\[
 \operatorname{Var}^{+}_{[s_G,s_\Pi]}\Pi
 =\sup_{s_G=s_0<\cdots<s_m=s_\Pi}
   \sum_{j=0}^{m-1}[\Pi_{s_{j+1}}-\Pi_{s_j}]_+.
 \tag{8.14}
\]

This already sharpens the fourth-moment defect, but it still takes absolute values before using
the algebraic form of the Navier--Stokes nonlinearity.  The \(1/12\) loss is therefore not
intrinsic.

### Lamb-vector cancellation removes the exponent gap

For a divergence-free velocity field,

\[
 -(u\cdot\nabla)u=-\nabla\frac{|u|^2}{2}+u\times\omega,
 \qquad
 N=\mathbb P(u\times\omega).
 \tag{8.15}
\]

The heat multiplier in filtered kinetic energy is \(e^{-2s|k|^2}\).  Self-adjointness of the
heat semigroup and orthogonality to gradients therefore give the exact identity

\[
 \boxed{
 \Pi_s=-\langle P_{2s}u,u\times\omega\rangle.}
 \tag{8.16}
\]

This uses a cancellation hidden by (8.8): since \(u\cdot(u\times\omega)=0\), only the
difference \(P_{2s}u-u\) contributes.  For the global estimate it is enough to use heat-kernel
smoothing and Cauchy--Schwarz,

\[
 \begin{aligned}
 |\Pi_s|
 &\le \|P_{2s}u\|_\infty\|u\|_2\|\omega\|_2\\
 &\le C(1+s^{-3/4})\|u_0\|_2^2\Omega^{1/2}.
 \end{aligned}
 \tag{8.17}
\]

At the geometric heat scale

\[
 s_G=\ell_G^2=(1+\Omega)^{-2/3},
\]

(8.17) becomes

\[
 \boxed{
 |\Pi_{s_G}(t)|\le C\|u_0\|_2^2(1+\Omega(t)),}
 \tag{8.18}
\]

which is time-integrable by the energy identity.  The analogous sharp-cutoff estimate is

\[
 |\Pi(K,t)|
 =\left|\int P_{\le K}u\cdot(u\times\omega)\,dx\right|
 \le CK^{3/2}\|u_0\|_2^2\Omega^{1/2}.
 \tag{8.19}
\]

Thus \(K_G=(1+\Omega)^{1/3}\) is simultaneously the finest energy-paid geometric wavenumber
and the finest wavenumber at which the absolute flux amplitude is paid.  The coarse scale
\(\ell_\Pi\) in (8.12) remains a valid increment-only estimate, but it is no longer the active
boundary of the argument.

The Lamb form also supplies the missing exact connection to vortex lines.  Disintegrating
\(\omega=\rho\xi\) by its flux measure as in Section 9 gives

\[
 \Pi_s=-\int d\Phi(\gamma)
   \int_{I_\gamma}\xi\cdot(P_{2s}u\times u)\,ds.
 \tag{8.20}
\]

This turns one prospective bridge into a one-dimensional line-integral estimate.  Formula
(9.7) controls the measure of active excursions; what is still missing is a bound for the
signed line integrals in (8.20), including the closed or recurrent vortex lines.  Neither
(8.18) nor a bound on one filtered enstrophy controls the unresolved high-frequency tail.

### Exact energy--circulation duality

There is a second, more intrinsic bridge.  Put

\[
 U_s=P_su,\qquad \Omega_s=\nabla\times U_s,\qquad
 f_s^*=P_s(u\times\omega)-U_s\times\Omega_s.
 \tag{8.21}
\]

The last field is the subgrid vortex force.  Self-adjointness of the heat filter and the
pointwise orthogonality \(U_s\cdot(U_s\times\Omega_s)=0\) give

\[
 \boxed{\Pi_s=-\langle U_s,f_s^*\rangle.}
 \tag{8.22}
\]

If \(\mathbb P\) is the Leray projection, then
\(\langle U_s,f_s^*\rangle=\langle U_s,\mathbb P f_s^*\rangle\): energy sees only the
solenoidal part of the vortex force.  On the mean-zero torus set
\(A_s=(-\Delta)^{-1}\Omega_s\), so \(\nabla\times A_s=U_s\).  Periodic curl integration by
parts and self-adjointness of \((-\Delta)^{-1}\) then yield

\[
 \boxed{
 \Pi_s
 =-\langle A_s,\nabla\times f_s^*\rangle
 =-\langle\Omega_s,(-\Delta)^{-1}\nabla\times f_s^*\rangle.}
 \tag{8.23}
\]

For an oriented loop \(C=\partial\Sigma\), the corresponding circulation cascade is

\[
 K_s(C)=-\oint_C f_s^*\cdot dx
       =-\int_\Sigma(\nabla\times f_s^*)\cdot n\,dA.
 \tag{8.24}
\]

Thus energy flux and circulation flux are not merely analogous: they are different dual probes
of the same subgrid vorticity defect \(c_s=\nabla\times f_s^*\).  Disintegrating the *filtered*
vorticity in (8.23) gives the alternative exact line formula

\[
 \Pi_s=-\int d\Phi_s(\gamma)\int_{I_\gamma}
   \xi_s\cdot(-\Delta)^{-1}c_s\,d\ell.
 \tag{8.25}
\]

This identifies the precise missing analytic bridge: a signed potential-theoretic estimate for
the line integrals of \((-\Delta)^{-1}c_s\), including persistent curves.  Taking norms too
early gives only

\[
 |\Pi_s|\le\|\Omega_s\|_2\|\mathbb P f_s^*\|_{\dot H^{-1}},
 \tag{8.26}
\]

and the stress representation bounds the last norm by an \(L^2\) subgrid stress, returning to
the uncontrolled fourth increment moment.  Therefore the bridge must retain the signed
pairing.  The Hilbert-space cores of (8.22), Leray invisibility, and curl integration by parts
are checked in `NSFormal/LambFlux.lean`.

### Paid amplitude does not control positive scale variation

There is a simple finite-shell obstruction to stopping at (8.18).  For one pair of shell
weights \(a,2a\), take transfers \(-A,+A\).  Total nonlinear energy transfer is zero, the
sharp forward flux equals \(A\ge0\) between the two shells, and the heat-filtered flux is

\[
 \Pi_s^{(a)}=A\left(e^{-2as}-e^{-4as}\right).
 \tag{8.27}
\]

This is a positive bump centered at scale \(s\simeq a^{-1}\), with value \(A/4\) at
\(s=(\log2)/(2a)\).  Superpose \(N\) such pairs with
\(a_{j+1}=Ra_j\), where \(R\) is large.  The sharp forward flux remains nonnegative.  The heat
flux is

\[
 \Pi_s=A\sum_{j=1}^N\left(e^{-2a_js}-e^{-4a_js}\right).
 \tag{8.28}
\]

The bumps are separated on the logarithmic scale.  For fixed sufficiently large \(R\), their
geometric tails give a bound \(\sup_s\Pi_s\le C_RA\) independent of \(N\), while each bump
contributes a fixed positive rise, so

\[
 \operatorname{Var}_s^+\Pi\ge c_RNA.
\]

Thus neither an amplitude estimate nor nonnegativity of every sharp forward flux can bound
positive scale variation.  A successful argument must couple successive scale bumps to
physical time and debit them against viscosity, direction dissipation, or the high-tail
positive variation in (10.7).  This finite-shell model is not a Navier--Stokes counterexample;
it proves that the remaining dynamical information cannot be replaced by static transfer
algebra.

## 9. Critical episode scaling and vortex-line geometry

The energy ledger alone cannot exclude an infinite critical cascade.  Suppose a high-vorticity
region has transverse radius \(\delta\), axial length \(L\), amplitude
\(W\simeq\nu/\delta^2\), volume \(\simeq\delta^2L\), and lasts for a viscous time
\(\delta^2/\nu\).  Its enstrophy-time cost is only

\[
 \int_{\rm episode}\Omega(t)\,dt\gtrsim \nu L.
 \tag{9.1}
\]

Hence a sequence with summable lengths can have finite energy cost while producing infinitely
many order-one stretching impulses.  For a blob \(L\simeq\delta\), the cost is
\(O(\nu\delta)\), summable on geometric scales.  A data-independent lower bound on \(L\),
as assumed in the manuscript, is therefore precisely a missing theorem.

There is, however, an exact geometric constraint on a collapsing high-vorticity segment.  Since
\(\nabla\cdot\omega=0\) and \(\omega=\rho\xi\),

\[
 \xi\cdot\nabla\log\rho=-\nabla\cdot\xi.
 \tag{9.2}
\]

Along a vortex line \(\gamma'(s)=\xi(\gamma(s))\), if
\(\rho(\gamma(0))/\rho(\gamma(L))\ge1/\theta\), then

\[
 \int_0^L|\nabla\xi(\gamma(s))|^2ds
 \ge\frac{\log^2(1/\theta)}{3L}.
 \tag{9.3}
\]

Indeed, integrate (9.2), use \(|\nabla\cdot\xi|\le\sqrt3|\nabla\xi|\), and apply
Cauchy--Schwarz.  Thus an aligned vorticity field cannot simply terminate as a compact blob:
short axial decay forces direction dissipation.  Long segments are charged by (9.1); short
segments are charged by (9.3).  Turning this complementary pair into a spacetime estimate for
the signed commutator work is the most concrete geometric route now available.

### A measurable replacement for assumed tubes

The preceding argument does not require a phenomenological tube class.  On a superlevel region
where \(\rho=|\omega|>0\), the unit field \(\xi\) is smooth and

\[
 \nabla\cdot(\rho\xi)=0.
\]

Consequently the flow of \(\xi\) preserves the measure \(\rho\,dx\).  In local flow-box
coordinates, with \(d\Phi\) denoting the vorticity-flux measure labeling integral curves,

\[
 \int_A \rho g\,dx
 =\int d\Phi(\gamma)\int_{I_\gamma}g(\gamma(s))\,ds,
 \qquad
 \int_A \rho^2 g\,dx
 =\int d\Phi(\gamma)\int_{I_\gamma}\rho(\gamma(s))g(\gamma(s))\,ds
 \tag{9.4}
\]

for every nonnegative measurable \(g\).  The same global representation can be phrased using
Smirnov's decomposition of a solenoidal vector measure into elementary solenoids; importantly,
the decomposition preserves the total variation measure and hence the weights in (9.4).

Fix regular levels \(0<\theta<\lambda<1\).  Consider excursion segments of vortex lines on
which \(\rho\ge\theta W\), which reach \(\lambda W\), and whose two endpoints lie on the
level \(\theta W\).  If \(L_\gamma\) is the total segment length, applying (9.3) from a peak
to each endpoint gives

\[
 \int_{I_\gamma}\rho|\nabla\xi|^2ds
 \ge \frac{4\theta W\log^2(\lambda/\theta)}{3L_\gamma}.
 \tag{9.5}
\]

Let \(\Phi_{\rm act}\) be the total flux measure of these active excursions, and set

\[
 E_{\rm high}=\int_A\rho^2dx,
 \qquad
 D_{\xi,\rm high}=\int_A\rho^2|\nabla\xi|^2dx.
\]

For any length \(L_0>0\), (9.4)--(9.5) give

\[
 \Phi_{\rm short}\le
   C_{\theta,\lambda}\frac{D_{\xi,\rm high}L_0}{W},
 \qquad
 \Phi_{\rm long}\le
   \frac{E_{\rm high}}{\theta W L_0}.
 \tag{9.6}
\]

Optimizing in \(L_0\) yields the flux inequality

\[
 \boxed{
 \Phi_{\rm act}
 \le C_{\theta,\lambda}
      \frac{\sqrt{E_{\rm high}D_{\xi,\rm high}}}{W}.}
 \tag{9.7}
\]

Closed or recurrent curves which never cross the lower level form the complementary persistent
high-vorticity set; they are long by construction and should be treated through near-field
direction cancellation and far-field strain rather than (9.5).

Two cautions are essential.  First, \(D_{\xi,\rm high}\) is part of palinstrophy, not the
kinetic-energy dissipation \(\int|\omega|^2\).  It has no unconditional finite-time budget at
the Leray energy level; it must be absorbed inside a filtered enstrophy balance or otherwise
debited dynamically.  Second, the persistent complement is genuinely capable of carrying
energy flux, as the following exact test shows.

### A Navier--Stokes-realizable persistent-line test

Use normalized spatial average on \(\mathbb T^3=[0,2\pi]^3\).  Let

\[
 \psi_\varepsilon(x,y)
 =\cos x+\varepsilon\cos(x+y)+\varepsilon\cos(2x+y),
 \qquad
 u_\varepsilon=(\partial_y\psi_\varepsilon,-\partial_x\psi_\varepsilon,0).
 \tag{9.8}
\]

This is a smooth mean-zero divergence-free three-torus field, independent of \(z\).  Its
vorticity is

\[
 \omega_\varepsilon
 =\left(0,0,-\Delta\psi_\varepsilon\right)
 =\left(0,0,
   \cos x+2\varepsilon\cos(x+y)+5\varepsilon\cos(2x+y)\right).
 \tag{9.9}
\]

Every nonzero vortex line is a vertical closed circle.  Its vorticity magnitude is constant
along the line and its direction is exactly \(e_3\) or \(-e_3\).  Consequently every line which
reaches \(\lambda W\) is persistent: it never crosses the lower level \(\theta W\).
The active excursion measure in (9.7) is zero for every
\(0<\theta<\lambda<1\), and \(D_{\xi,\rm high}=0\) on the high set.

Nevertheless this field has positive heat-filtered forward energy flux.  Its three Fourier
shells have squared wavenumbers \(1,2,5\).  Direct trigonometric averaging gives their nonlinear
kinetic-energy transfers

\[
 (T_1,T_2,T_5)
 =\frac{\varepsilon^2}{4}(-3,4,-1),
 \qquad T_1+T_2+T_5=0.
 \tag{9.10}
\]

Therefore

\[
 \boxed{
 \Pi_s=\frac{\varepsilon^2}{4}
       \left(3e^{-2s}-4e^{-4s}+e^{-10s}\right)>0
       \quad(s>0).}
 \tag{9.11}
\]

Positivity is elementary.  With \(q=e^{-2s}\in(0,1)\),

\[
 3e^{-2s}-4e^{-4s}+e^{-10s}
 =q(q-1)^2(q^2+2q+3)>0.
 \tag{9.12}
\]

The transfer conservation, heat-flux formula, factorization, and nonnegativity are
kernel-checked in `NSFormal/SpectralFlux.lean`.  The trigonometric calculation identifying
(9.10) with the concrete field (9.8) remains a short prose calculation rather than part of the
current Lean integration layer.

This field is admissible smooth initial data for the local Navier--Stokes evolution, so the
obstruction occurs at an actual instantaneous Navier--Stokes state.  It does not exhibit
singular behavior or recurrent transfer—in fact its two-dimensional evolution is regular.  It
proves the narrower but load-bearing fact that no instantaneous inequality depending only on
\(\Phi_{\rm act}\) and direction palinstrophy can control even the sign or amplitude of
\(\Pi_s\).  Since \(\Pi_0=0<\Pi_s\), it cannot control positive heat-scale variation either.
A persistent-line term using different information—scalar-vorticity gradients and diffusion,
or time dynamics in this test—is mandatory.

The same example also reveals the cancellation that a successful persistent estimate should
preserve.  For any smooth divergence-free vorticity \(\omega=\rho\xi\), periodic integration by
parts and \(\nabla\cdot(\rho\xi)=0\) give the exact total-stretching identity

\[
 \begin{aligned}
 \int\omega\cdot(\omega\cdot\nabla)u\,dx
 &=-\int u\cdot(\omega\cdot\nabla)\omega\,dx\\
 &=\int\rho^2\left[
     (\nabla\cdot\xi)(u\cdot\xi)
     -u\cdot(\xi\cdot\nabla)\xi\right]dx.
 \end{aligned}
 \tag{9.13}
\]

Thus

\[
 \left|\int\omega\cdot(\omega\cdot\nabla)u\right|
 \le (1+\sqrt3)
   \left(\int\rho^2|\nabla\xi|^2\right)^{1/2}
   \left(\int\rho^2|u|^2\right)^{1/2}.
 \tag{9.14}
\]

The weighted derivatives \(\rho\nabla\xi\) extend harmlessly through the zero set because they
are components of \(\nabla\omega\).  Identity (9.13) makes the two-dimensional cancellation
exact: if the vorticity direction is constant, total vortex stretching is zero even though
filtered kinetic-energy flux can have positive scale variation.  Its filtered version is the
directional form of the simpler global estimate (4.3)--(4.4).

The remaining difficulty is visible in (9.14): taking an absolute value leaves
\(\int\rho^2|u|^2\), whose energy-class estimate returns the standard supercritical enstrophy
ODE.  A useful persistent-line estimate must keep more of the signed orbit average in (9.13), or
couple it to the scalar-vorticity diffusion which controls the planar test, rather than apply
Cauchy--Schwarz globally.

### Closed persistent lines obey the same long/short ledger

There is nevertheless a rigorous extension of (9.7) to closed persistent curves.  Let
\(\gamma\) be a contractible \(C^2\) closed vortex line of length \(L_\gamma\), parametrized by
arc length.  Fenchel's theorem and Cauchy--Schwarz give

\[
 \int_\gamma |(\xi\cdot\nabla)\xi|\,ds\ge2\pi,
 \qquad
 \int_\gamma|\nabla\xi|^2ds\ge\frac{4\pi^2}{L_\gamma}.
 \tag{9.15}
\]

If \(\rho\ge\theta W\) on the line, define its line charges

\[
 e_\gamma=\int_\gamma\rho\,ds,\qquad
 d_\gamma=\int_\gamma\rho|\nabla\xi|^2ds.
\]

Then \(e_\gamma d_\gamma\ge(2\pi\theta W)^2\).  Integrating over the flux measure and applying
Cauchy--Schwarz proves

\[
 \boxed{
 \Phi_{\rm pers,ctr}
 \le\frac{\sqrt{E_{\rm pers,ctr}D_{\xi,\rm pers,ctr}}}
          {2\pi\theta W}.}
 \tag{9.16}
\]

A noncontractible closed curve on the period-\(2\pi\) flat torus has
\(L_\gamma\ge L_{\rm sys}=2\pi\).  It therefore obeys the purely long-line estimate

\[
 \boxed{
 \Phi_{\rm pers,nctr}
 \le\frac{E_{\rm pers,nctr}}{\theta W L_{\rm sys}}.}
 \tag{9.17}
\]

The vertical circles in the planar test (9.8) lie in this noncontractible class, so (9.17)
accounts for them without inventing a direction cost.  Equations (9.16)--(9.17) close the
*geometric measure* ledger for active excursions and closed persistent lines.  They still do not
control the signed line integrands in (8.20) or (8.25), and recurrent nonclosed trajectories
require an ergodic or long-segment version of the same dichotomy.  Those are now the two precise
persistent obligations.

### A finite-segment recurrence dichotomy

The elementary geometry of the recurrent nonclosed class can be pushed one step further.  Let
\(\gamma:[0,L]\to\mathbb T^3\) be parametrized by arc length, let
\(\widetilde\gamma\) be a lift to \(\mathbb R^3\), write
\(\xi=\widetilde\gamma'\), and set
\(d=\widetilde\gamma(L)-\widetilde\gamma(0)=\int_0^L\xi(s)\,ds\).  Vector-valued
integration by parts gives the exact identity

\[
 d=L\xi(L)-\int_0^L s\,\xi'(s)\,ds.
 \tag{9.18}
\]

Since \(|\xi(L)|=1\), the reverse triangle inequality and weighted Cauchy--Schwarz imply

\[
 (L-|d|)^2
 \le \left|\int_0^L s\,\xi'(s)\,ds\right|^2
 \le \frac{L^3}{3}\int_0^L|\xi'(s)|^2\,ds.
 \tag{9.19}
\]

Fix \(0\le\alpha<1\).  If the universal-cover drift is slow, \(|d|\le\alpha L\), then

\[
 \boxed{L\int_0^L|\xi'|^2\,ds\ge3(1-\alpha)^2.}
 \tag{9.20}
\]

On a persistent high segment, \(\rho\ge\theta W\), this yields

\[
 e_\gamma d_\gamma
 \ge3(1-\alpha)^2(\theta W)^2,
 \tag{9.21}
\]

so the turning branch has the same square-root flux ledger as (9.16), with
\(2\pi\) replaced by \(\sqrt3(1-\alpha)\).

The complementary branch has quantitative topology.  If the endpoints are within torus
distance \(\delta\), then for some \(n\in\mathbb Z^3\),
\(d=2\pi n+r\) with \(|r|\le\delta\).  If \(|d|>\alpha L\), then

\[
 \boxed{|n|>\frac{\alpha L-\delta}{2\pi}.}
 \tag{9.22}
\]

The ballistic branch also has quantitative analytic structure.  With
\(\bar\xi=d/L\), direct expansion gives the exact variance identity

\[
 \boxed{
 \int_0^L|\xi(s)-\bar\xi|^2\,ds
 =L-\frac{|d|^2}{L}.}
 \tag{9.23}
\]

Hence \(|d|\ge\alpha L\) implies
\(\int_0^L|\xi-\bar\xi|^2\le L(1-\alpha^2)\).  More directly useful for
anisotropic regularity, the normalized displacement direction \(e=d/|d|\) obeys

\[
 \boxed{
 \int_0^L|\xi-e|^2\,ds=2(L-|d|)
 \le2L(1-\alpha).}
 \tag{9.24}
\]

Consequently, for any vector field \(B\) sampled along the segment,

\[
 \boxed{
 \left|\int_0^L\xi\cdot B\,ds-
             \int_0^L e\cdot B\,ds\right|
 \le [2L(1-\alpha)]^{1/2}
      \left(\int_0^L|B|^2\,ds\right)^{1/2}.}
 \tag{9.25}
\]

For (8.20), one may take \(B=P_{2s}u\times u\).  The error is now explicitly tied to
tangent incoherence, while the constant-unit-direction orbit average remains signed and includes
the exactly planar case.  A successful persistent estimate must pay that leading term by
scalar-vorticity diffusion or transverse cancellation; applying an absolute bound to it would
discard the planar cancellation again.

For a measurable family of such segments, Cauchy--Schwarz over the flux measure gives the
global error ledger

\[
 \boxed{
 \left|\int d\Phi(\gamma)\,\mathrm{Err}_\gamma\right|
 \le
 \left(2(1-\alpha)\int_A\rho\,dx\right)^{1/2}
 \left(\int_A\rho|B|^2\,dx\right)^{1/2}.}
 \tag{9.26}
\]

The measure-theoretic Cauchy step in (9.26) is kernel-checked as
`norm_integral_signedError_le_sqrt_charges` in `NSFormal/Budget.lean`.  This also exposes why
coherence alone does not close the estimate.  For \(B=P_{2s}u\times u\), the direct bounds

\[
 \int\rho\lesssim\Omega^{1/2},\qquad
 \int\rho|B|^2
 \le\|P_{2s}u\|_\infty^2\|\rho\|_2\|u\|_4^2
 \lesssim \|u_0\|_2^{5/2}s^{-3/2}\Omega^{5/4}
\]

give, at \(s=s_G=(1+\Omega)^{-2/3}\), only

\[
 |\mathrm{Err}_{\rm family}|
 \lesssim (1-\alpha)^{1/2}\|u_0\|_2^{5/4}(1+\Omega)^{11/8}.
 \tag{9.27}
\]

The exponent \(11/8>1\) is not energy-paid.  Thus a fixed amount of ballistic coherence,
followed by absolute Cauchy--Schwarz, is still insufficient.  One must exploit the signed
constant-direction term, obtain additional smallness from a dynamically near-unit drift, or
couple the error to the selector dissipation in (10.12)--(10.13).  This is a new no-go check on
the coherence route, not a closure theorem.

There is nevertheless a scale-critical threshold at which normalized ballistic coherence
would become useful.  Since \(e\) and \(\xi\) are unit vectors,
\(|e\times\xi|\le|e-\xi|\).  On a persistent family, \(\rho\le W\), so (9.24), the two
flow-box identities in (9.4), and Cauchy--Schwarz give formally

\[
 \|e\times\omega\|_{L^2(A)}^2
 \le \int_A\rho^2|e-\xi|^2\,dx
 \le 2W(1-\alpha)\int_A\rho\,dx.
 \tag{9.28}
\]

Consequently

\[
 \boxed{
 \|e\times\omega\|_{L^2(A)}^4
 \le C_{\mathbb T^3}[W(1-\alpha)]^2\Omega.}
 \tag{9.29}
\]

Thus the dynamic near-unit-drift threshold

\[
 \boxed{W(t)(1-\alpha(t))\le C}
 \tag{9.30}
\]

would make the critical fourth-power cross component time-integrable by the energy identity.
The scalar charge algebra in (9.28)--(9.29) is kernel-checked as
`ballistic_cross_component_fourth_paid` in `NSFormal/NewProofAlgebra.lean`.  The geometric
disintegration, construction of a single global unit field from the orbitwise directions, its
spatial regularity, and the threshold (9.30) are not proved.  This isolates a concrete possible
payoff for coupling drift deficit to the selected viscous dissipation in (10.12).

There is a useful adaptive choice which removes the apparent conflict between the turning and
ballistic branches.  Fix an amplitude \(c>0\).  On the genuinely high-vorticity regime \(W>c\),
take

\[
 \boxed{\alpha(t)=1-\frac{c}{W(t)}.}
 \tag{9.31}
\]

Then the slow-drift charge (9.21) loses all dependence on the peak amplitude:

\[
 \boxed{e_\gamma d_\gamma\ge 3(\theta c)^2.}
 \tag{9.32}
\]

In the ballistic branch, (9.24) instead gives

\[
 \int_0^L|\xi-e|^2\,ds\le \frac{2cL}{W},
 \qquad
 \boxed{\|e\times\omega\|_{L^2(A)}^4
       \le C_{\mathbb T^3}c^2\Omega.}
 \tag{9.33}
\]

Thus neither local outcome carries a superlinear peak-amplitude penalty: slow recurrent lines
pay a fixed geometric charge, while ballistic lines pay a critical fourth-power
transverse-vorticity charge.  The total slow-branch direction charge is not yet known to be
energy-paid.  The regime
\(W\le c\) is already a bounded-vorticity regime.  The cancellation in (9.32) and the complete
adaptive curvature/coherence/winding disjunction are kernel-checked as
`adaptive_slow_recurrent_turning_charge_product` and
`adaptive_recurrent_turning_or_unit_coherent_winding` in `NSFormal/Recurrence.lean`.
This is a local ledger, not a regularity proof: it still requires a measurable nonoverlapping
return selection, and the orbitwise directions in (9.33) have not been assembled into the one
spatially regular unit field required by an anisotropic regularity criterion.

That regularity qualification is essential.  For every positive integer \(N\), the exact
periodic shear solution

\[
 u_N(t,z)=-\frac{e^{-\nu N^2t}}{N}(\cos Nz,\sin Nz,0),
 \qquad
 \omega_N(t,z)=e^{-\nu N^2t}(\cos Nz,\sin Nz,0)
 \tag{9.34}
\]

has \(u_N\cdot\nabla u_N=0\), \(\Delta u_N=-N^2u_N\), and zero pressure.  Its unit vorticity
direction is constant along each of its own straight horizontal integral lines, so all line
curvatures vanish, but it reverses across transverse distance \(\pi/N\):

\[
 \xi_N(z+\pi/N)=-\xi_N(z),
 \qquad \|\nabla\xi_N\|_\infty=N.
 \tag{9.35}
\]

Hence linewise turning cannot control the full spatial gradient of the assembled direction,
even for genuine smooth Navier--Stokes solutions.  In this family viscosity pays the rapid
transverse rotation on the time scale \(N^{-2}\).  Any global assembly theorem must likewise
debit transverse direction changes to diffusion or to the spectral selector; it may not infer
them from vortex-line curvature.  `NSFormal/Anisotropy.lean` kernel-checks the unit-length,
self-line constancy, and arbitrary-frequency antipodal identities behind this regression test.

The integration-by-parts proof of the variable-direction anisotropic criterion gives a more
useful target than a time-uniform Lipschitz bound.  Retain its actual spatial error

\[
 \mathcal A_e(t):=\int_{\mathbb T^3}|u|\,|\nabla u|\,|\nabla e|\,dx.
\]

On the torus the pointwise ledger then has the form

\[
 \boxed{
 \|Se\|_2^4
 \le \frac18\|e\times\omega\|_2^4+C\mathcal A_e(t)^2,}
 \qquad
 \mathcal A_e(t)^2
 \le \|u\|_2^2\|\nabla u\|_2^2\|\nabla e\|_\infty^2.
 \tag{9.36}
\]

The identity is Galilean invariant.  For any spatially constant frame velocity \(a(t)\), the
same proof replaces the mixed debit by
\[
 \mathcal A_{e,a}(t):=
 \int_{\mathbb T^3}|u-a|\,|\nabla u|\,|\nabla e|\,dx.
\]
This is strictly preferable on a localized coherent region: a large harmless mean or local
transport velocity should not be charged as direction deformation.

Combining (9.33) with the anisotropic strain criterion reduces the ballistic assembly problem
to the minimal parabolic condition

\[
 \boxed{\int_0^T\mathcal A_e(t)^2\,dt<\infty.}
 \tag{9.37}
\]

Energy monotonicity and \(\|\nabla u\|_2^2=\Omega\) show that the stronger condition

\[
 \int_0^T\Omega(t)\|\nabla e(t)\|_\infty^2\,dt<\infty
 \tag{9.38}
\]

is sufficient, but it is not built into the target.

There is a sharper candidate on a selected high-vorticity region \(A\).  Put
\(\rho=|\omega|\) and \(\xi=\omega/\rho\), only where \(\rho>0\).  Orthogonality of a unit
direction to each of its derivatives gives the exact amplitude--direction split

\[
 |\nabla\omega|^2=|\nabla\rho|^2+\rho^2|\nabla\xi|^2,
 \qquad \rho^2|\nabla\xi|^2\le |\nabla\omega|^2.
 \tag{9.39}
\]

Consequently the centered mixed error for \(e=\xi\) has the weighted Cauchy ledger

\[
 \boxed{\mathcal A_{\xi,A,a}^2\le P_AQ_{A,a}},\qquad
 P_A:=\int_A|\nabla\omega|^2\,dx,\qquad
 Q_{A,a}:=\int_A\frac{|u-a|^2|\nabla u|^2}{\rho^2}\,dx.
 \tag{9.40}
\]

If \(A\subset\{\rho\ge\theta W\}\), then, without any regularity inference,

\[
 \boxed{Q_{A,a}\le (\theta W)^{-2}
   \int_A|u-a|^2|\nabla u|^2\,dx.}
 \tag{9.41}
\]

The absorption threshold is subtler than smallness of \(Q_{A,a}\) alone.  In the standard
strain/enstrophy interpolation the nonlinear production is bounded schematically by
\[
 \mathcal N_A\le C\|S\xi\|_2\,\Omega^{1/4}P_A^{3/4}.
\]
Combining \(\|S\xi\|_2^4\lesssim P_AQ_{A,a}\) with this display gives
\[
 \mathcal N_A\lesssim P_A(Q_{A,a}\Omega)^{1/4}.
\]
Thus the dimensionless critical condition for direct viscous absorption is
\[
 \boxed{C^4Q_{A,a}\Omega\le\nu^4,}
 \tag{9.42}
\]
not merely \(Q_{A,a}\ll1\).  The scalar fourth-power implication from these premises to
\(\mathcal N_A\le\nu P_A\) is kernel-checked as
`critical_weighted_direction_debit_absorbed` in
`NSFormal/NewProofAlgebra.lean`.  The spatial strain interpolation and its localization
to a patched selected region are still analytic obligations.

One elementary estimate now identifies a regime where (9.42) has a chance to hold.  Choose
\(a=\fint_{\mathbb T^3}u\).  Poincaré--Sobolev, the periodic Calderón--Zygmund estimate, and
\(\|\omega\|_3\le\|\omega\|_2^{2/3}\|\omega\|_\infty^{1/3}\) give
\[
\begin{aligned}
 Q_{A,a}
 &\le(\theta W)^{-2}\|u-a\|_6^2\|\nabla u\|_3^2\\
 &\le C_{\mathbb T^3}\theta^{-2}
      W^{-4/3}\Omega^{5/3}.
\end{aligned}
\tag{9.43}
\]
Therefore
\[
 \boxed{Q_{A,a}\Omega
 \le C_{\mathbb T^3}\theta^{-2}
       \left(\frac{\Omega^2}{W}\right)^{4/3}.}
\tag{9.44}
\]
The exponent identity in (9.44) is kernel-checked as
`weighted_quotient_concentration_exponent_chain`.  The functional inequalities in
(9.43) are standard but not yet represented in the Lean library.

Thus the sufficiently concentrated branch
\[
 \frac{W}{\Omega^2}\ge
 C_{\mathbb T^3}\theta^{-3/2}\nu^{-3}
\]
would satisfy the critical absorption threshold, up to the constants in the strain
interpolation and the unresolved patching.  The ratio \(W/\Omega^2\) is scale invariant.

This branch sits at a critical boundary rather than providing an automatic concentration gain.
The \(L^\infty\) spatial-analyticity estimate used in
[Grujić's geometric criterion](https://arxiv.org/abs/1111.0217) has vorticity analyticity
radius \(r_a\asymp\sqrt{\nu/W}\) at the relevant escape times.  Combining its complex
supremum bound with Cauchy's estimate forces a fixed-fraction core
\(A_\theta=\{\rho\ge\theta W\}\) of radius comparable to \(r_a\).  Consequently
\[
 |A_\theta|\gtrsim\nu^{3/2}W^{-3/2},\qquad
 \Omega\ge\theta^2W^2|A_\theta|
 \gtrsim\theta^2\nu^{3/2}W^{1/2},
\]
and hence
\[
 \boxed{\frac{W}{\Omega^2}\lesssim\theta^{-4}\nu^{-3}.}
\tag{9.45}
\]
The polynomial implication from a critical core-volume floor to (9.45) is kernel-checked as
`analytic_volume_forces_critical_concentration_cap`.  Deriving the volume premise from
the periodic Navier--Stokes analyticity theorem is not yet formalized.

Thus the sufficient lower threshold from (9.42)--(9.44) and the analytic upper cap (9.45)
have the same \(\nu^{-3}\) scaling.  There is no exponent slack: any closure must win in the
constants, exploit anisotropic one-dimensional sparseness/harmonic measure, or retain signed
transfer.  The complementary diffuse-amplitude branch is not closed by this estimate; neither
high vorticity nor the energy identity alone makes (9.44) small there.  Moreover \(\xi\) must
still be patched across the complement and across selector interfaces without losing the debit.

There is a way to remove that last orientation/patching obligation entirely.  Replace the unit
vector by a positive trace-one director tensor.  For a symmetric tensor field \(P\), set
\[
 \Sigma_P:=\int_{\mathbb T^3}\operatorname{tr}(PS^2)\,dx,\qquad
 X_P:=\int_{\mathbb T^3}\bigl(|\omega|^2-\omega\cdot P\omega\bigr)\,dx.
\]
In a strain eigenframe, positivity and \(\operatorname{tr}P=1\) imply
\(\operatorname{tr}(PS^2)\ge\min_i\lambda_i^2=\lambda_2^2\).  Thus the middle-eigenvalue
criterion extends from a rank-one \(P=e\otimes e\) to convex director tensors.  The periodic
integration by parts is cleaner:
\[
 \Sigma_P=\frac14X_P-
 \sum_{i,j,k}\int_{\mathbb T^3}u_j\,\partial_k u_i\,\partial_iP_{jk}\,dx,
\]
and hence, with the coordinate-\(\ell^1\) envelope
\(\mathcal A_P=\int|u|\,|\nabla u|_1|\nabla P|_1\),
\[
 \boxed{\Sigma_P^2\le\frac18X_P^2+1458\,\mathcal A_P^2.}
\tag{9.46}
\]
The coefficient is \(2\cdot27^2\), half the oriented expansion count in (9.36).

The most useful choice is the explicit nonsingular tensor
\[
 \boxed{
 P_c:=\frac{\omega\otimes\omega+(c^2/3)I}{|\omega|^2+c^2}},
 \qquad c>0.
\tag{9.47}
\]
It is smooth wherever \(\omega\) is, symmetric, positive, and trace one; at a vorticity zero it
is exactly \(I/3\), while for \(|\omega|\gg c\) it approaches
\(\xi\otimes\xi\).  Its transverse density is exactly
\[
 |\omega|^2-\omega\cdot P_c\omega
 =\frac{2c^2}{3}\frac{|\omega|^2}{|\omega|^2+c^2}
 \le\frac{2c^2}{3}.
\tag{9.48}
\]
Therefore \(X_{P_c}^2\) is uniformly bounded on the torus and automatically time-integrable
on every finite interval.  No vortex-line orientation, sign choice, zero-set extension, or
return-cell patch is required.

The derivative debit can be computed without choosing an orientation.  The useful identity is
not the first coordinatewise quotient bound, but the cancellation-preserving rewrite
\[
 P_c=\frac13I+
 \frac{\omega\otimes\omega-(|\omega|^2/3)I}{|\omega|^2+c^2}.
\]
If \(w,h\in\mathbb R^3\), \(D=|w|^2+c^2\), and \(dP_c(w)[h]\) denotes its differential, direct
algebra gives the exact rotationally invariant formula
\[
 \boxed{
 \|dP_c(w)[h]\|_F^2
 =2\frac{|w|^2|h|^2-(w\cdot h)^2}{D^2}
 +\frac83\frac{c^4(w\cdot h)^2}{D^4}.}
\tag{9.49}
\]
Thus \(dP_c(0)[h]=0\) exactly.  The first term is angular; the second is the radial-amplitude
derivative and decays three additional powers of \(|w|^2\) above the regularization scale.
In particular,
\[
 \|dP_c(w)[h]\|_F^2
 \le \frac{14}{3}\frac{|w|^2|h|^2}{D^2}.
\tag{9.50}
\]

There is a second, independent improvement.  The 27-coordinate tensor error is one Frobenius
inner product, not 27 unrelated errors.  Integrating the sum before applying Cauchy--Schwarz
gives
\[
 \left|\sum_{i,j,k}\int u_j\partial_k u_i\partial_iP_{jk}\right|
 \le \int |u-a|\,|\nabla u|_F|\nabla P|_F,
\]
and therefore
\[
 \Sigma_P^2\le\frac18X_P^2+2(\mathcal A_P^F)^2.
\tag{9.51}
\]
This removes the artificial factor \(27^2\) from (9.46).  Combining (9.48)--(9.51), put
\[
 P_F=\int|\nabla\omega|_F^2,\qquad
 Q_c^F(a)=\int |u-a|^2|\nabla u|_F^2
     \frac{|\omega|^2}{(|\omega|^2+c^2)^2}\,dx.
\]
The complete checked one-time ledger is
\[
 \boxed{
 \Sigma_{P_c}^2\le \frac{c^4|\mathbb T^3|^2}{18}
 +\frac{28}{3}P_FQ_c^F(a).}
\tag{9.52}
\]
The earlier coordinate-\(\ell^1\) estimates remain valid, but (9.52) supersedes their constants
\(1{,}889{,}568\) and \(26{,}572{,}050\).  More importantly, \(Q_c^F\) vanishes on the vorticity
zero set.

The cancellation gain is real but does not alone solve the exponent problem.  With
\(F=|u-a|^2|\nabla u|_F^2\), \(r=|\omega|^2\), and
\(L_c=\{r<c^2\}\), the exact low/high split is
\[
 \boxed{
 Q_c^F(a)\le
 \int_{L_c}F\frac{r}{c^4}\,dx
 +\int_{L_c^c}\frac{F}{r}\,dx.}
\tag{9.53}
\]
The low charge now remembers that vorticity is small instead of assigning the worst weight at
every zero.  Nevertheless
\[
 \frac{r}{(r+c^2)^2}\le\frac1{4c^2},
\tag{9.54}
\]
with equality at \(r=c^2\).  Hence a global absolute-value fallback still reproduces the
same \(Ac^4+D/c^2\) optimization and the critical \(\Omega P\) scaling.  Closure requires
information that distinguishes the two pieces in (9.53), not merely a different choice of
\(c(t)\).

Formula (9.49) suggests that distinction.  Away from \(\omega=0\), write
\[
 D_\xi=\int |\omega|^2|\nabla\xi|^2,\qquad
 D_\rho=\int|\nabla|\omega||^2,
\]
and define
\[
 Q_\xi=\int F\frac{|\omega|^2}{D^2},\qquad
 Q_\rho=\int F\frac{c^4|\omega|^2}{D^4}.
\]
The zero-set values are assigned by continuity.  Applying spatial Cauchy--Schwarz separately
to the two exact terms in (9.49) gives the sharper research target
\[
 (\mathcal A_{P_c}^F)^2
 \le 4D_\xi Q_\xi+\frac{16}{3}D_\rho Q_\rho,
\qquad
 \Sigma_{P_c}^2
 \le\frac18X_{P_c}^2+8D_\xi Q_\xi+\frac{32}{3}D_\rho Q_\rho.
\tag{9.55}
\]
The radial kernel has the strictly smaller global maximum
\[
 \frac{c^4r}{(r+c^2)^4}\le\frac{27}{256c^2},
\tag{9.56}
\]
attained at \(r=c^2/3\), and decays like \(c^4/r^3\) on the high set.  This is the first version
of the director route that treats constant-direction planar states correctly: their angular
charge \(D_\xi\) vanishes, leaving only the radial piece which scalar-vorticity diffusion can
potentially pay.  The full one-time form of (9.55), including the constants \(8\) and \(32/3\),
is now kernel-checked.  Coupling its radial term to scalar-vorticity diffusion remains an
analytic option, but the production identity below gives a cleaner route in which the radial
derivative cancels before estimation.

The Galilean frame in the primary quotient also has an explicit optimum.  Put
\[
 g_c^F=|\nabla u|_F^2\frac{|\omega|^2}{(|\omega|^2+c^2)^2},\qquad
 m_c^F=\int g_c^F,\qquad
 a_c^F=\frac{\int g_c^F u}{m_c^F}
\]
when \(m_c^F>0\).  Then the full vector-valued Haar identity is
\[
 \boxed{Q_c^F(a)=Q_c^F(a_c^F)+m_c^F|a-a_c^F|^2.}
\tag{9.57}
\]
Thus every continuation should use \(a_c^F(t)\), not the unweighted mean.

`NSFormal/DirectorTensor.lean` now kernel-checks (9.49)--(9.52), including the exact
radial/angular differential, one-shot 27-dimensional Frobenius contraction, coefficient
\(28/3\), and the explicitly constructed vector optimal frame and its global minimum.
`NSFormal/Budget.lean` checks (9.53), both kernel maxima (9.54) and (9.56), and the older coarse
fallback.  `NSFormal/NewProofAlgebra.lean` checks why the coarse global optimization returns
exactly to \(\Omega P\).  The spectral-coordinate step also includes the checked ordered
trace-zero fact that \(|\lambda_2|\) is the smallest eigenvalue magnitude.  The remaining
matrix eigendecomposition/continuation interface and, decisively, PDE control of the optimally
centered \(Q_c^F\) or the separated charges in (9.55) remain analytic obligations.

There is a stronger takeover route for the *actual enstrophy production*.  Returning to the
exact signed identity (9.13), set
\[
 B_\xi:=\xi\,\nabla\!\cdot\xi-(\xi\!\cdot\nabla)\xi.
\]
The two terms are orthogonal: the first is parallel to \(\xi\), while
\(\xi\cdot(\xi\cdot\nabla)\xi=0\).  Therefore the earlier triangle bound can be sharpened to
\[
 \boxed{|B_\xi|^2=(\nabla\!\cdot\xi)^2+|(\xi\!\cdot\nabla)\xi|^2
 \le 2|\nabla\xi|_F^2.}
 \tag{9.58}
\]
The factor `2` uses that every derivative of a unit direction lies in its rank-two tangent
plane; it is sharp, as witnessed by a checked equality jet.  No radial derivative of
\(\rho=|\omega|\) occurs.
Moreover \(\rho^2B_\xi=-\nabla\!\cdot(\rho^2\xi\otimes\xi)\), so its spatial mean is zero.
Consequently the identity is valid in every constant Galilean frame,
\[
 N:=\int\omega\cdot(\omega\cdot\nabla)u
   =\int\rho^2(u-a)\cdot B_\xi.
 \tag{9.59}
\]

Put
\[
 D_\xi=\int\rho^2|\nabla\xi|_F^2,
 \qquad V_\omega(a)=\int\rho^2|u-a|^2.
\]
The optimal frame is explicit:
\[
 a_\omega=\frac{\int\rho^2u}{\int\rho^2},\qquad
 V_\omega(a)=V_\omega(a_\omega)+\left(\int\rho^2\right)|a-a_\omega|^2.
\]
The zero-safe exact line-transport and curvature charges are
\[
 G_\omega=\int\frac{|(\omega\cdot\nabla)\omega|^2}{|\omega|^2},
 \qquad
 K_\omega=\int\frac{|P_{\omega^\perp}(\omega\cdot\nabla)\omega|^2}{|\omega|^2},
\]
where each quotient is defined as zero at \(\omega=0\).  Away from the zero set,
\[
 G_\omega=\int\rho^2\big[(\nabla\cdot\xi)^2+|(\xi\cdot\nabla)\xi|^2\big],
 \qquad K_\omega=\int\rho^2|(\xi\cdot\nabla)\xi|^2.
\]
Retaining the full pointwise projection calculation before Cauchy--Schwarz gives the checked
hierarchy
\[
 \boxed{N^2\le G_\omega V_\omega(a_\omega)
 \le(2D_\xi-K_\omega)V_\omega(a_\omega)
 \le2D_\xi V_\omega(a_\omega).}
 \tag{9.60}
\]
Moreover \(G_\omega\le P\), because it is exactly the part of the vorticity derivative taken
along the vorticity direction.  This is sharper in mechanism than (9.55): scalar-amplitude
variation is absent rather than estimated by a radial quotient, and transverse direction
derivatives which do not drive self-transport are not charged in \(G_\omega\).

Let \(P=D_\rho+D_\xi=\int|\nabla\omega|^2\), away from the harmless zero-set convention.  The
enstrophy equality is \(E_\omega'+\nu P=N\).  Hence the exact scale-critical absorption target is
\[
 \boxed{G_\omega V_\omega(a_\omega)\le\nu^2P^2.}
 \tag{9.61}
\]
Equivalently, with
\(\Theta_G=G_\omega/P\) and \(\mathcal R_v=V_\omega(a_\omega)/P\), it is
\(\Theta_G\mathcal R_v\le\nu^2\).  Both factors are scale invariant and
\(0\le\Theta_G\le1\).  Most importantly, the planar constant-direction branch has
\(\Theta_G=0\), so (9.61) closes automatically without requiring \(V_\omega\) to be small.
The weaker sufficient target \(2(D_\xi/P)\mathcal R_v\le\nu^2\) remains available.

The unconditional Young fallback is
\[
 N\le\nu D_\xi+\frac{V_\omega(a_\omega)}{2\nu},
 \qquad
 \boxed{E_\omega'+\nu D_\rho\le\frac{V_\omega(a_\omega)}{2\nu}.}
 \tag{9.62}
\]
It shows exactly what scalar diffusion would have to dominate.  Standard Sobolev estimates give
only
\[
 V_\omega(a)\le\|u-a\|_3^2\|\rho\|_6^2
 \lesssim\|u-a\|_3^2(D_\rho+\|\rho\|_2^2),
 \tag{9.63}
\]
which returns to the scale-critical \(L^3\) velocity threshold and is not an a priori closure.
Thus the new obligation is concrete: prove (9.61), or an integrated variant, using the
vorticity-weighted optimal frame, signed vortex-line transport, or a complementary estimate on
\(\Theta_G\) and \(\mathcal R_v\).  A global absolute Sobolev bound alone cannot do it.

There is a decisive static-scaling obstruction to demanding (9.61) at every time for arbitrary
data.  For the smooth divergence-free torus field
\[
 u=(\sin z,\sin x,\sin y),\qquad
 \omega=\nabla\times u=(\cos y,\cos z,\cos x),
\]
both \(G_\omega\) and \(V_\omega\) are positive and the weighted optimal frame is zero by
symmetry.  Under the fixed-shape amplitude scaling \(u\mapsto A u\),
\[
 G_\omega\mapsto A^2G_\omega,\qquad P\mapsto A^2P,
 \qquad V_\omega\mapsto A^4V_\omega,
\]
so
\[
 (G_\omega/P)(V_\omega/P)\mapsto
 A^2(G_\omega/P)(V_\omega/P). \tag{9.64}
\]
`NSFormal/NewProofAlgebra.lean` checks this exact exponent chain.  Therefore a global argument
must pay a possibly large early transient and derive depletion near a putative singular time;
instantaneous data-independent absorption would merely be a hidden small-data assumption.

The same hierarchy gives a more flexible energy-paid target.  On the mean-zero torus, standard
Sobolev and interpolation estimates give
\[
 V_\omega(a_\omega)\le V_\omega(0)
 \le \|u\|_6^2\|\omega\|_3^2
 \le C E_\omega^{3/2}P^{1/2}. \tag{9.65}
\]
Writing \(G_\omega=\Theta_G P\), (9.60) therefore implies
\[
 N\le C^{1/2}\Theta_G^{1/2}E_\omega^{3/4}P^{3/4}.
\]
The complete implication has now also been checked in a root-free form in
`NSFormal/NewProofAlgebra.lean`: `N² ≤ QV`, `Q ≤ Θ_G P`, and the squared form of (9.65),
`V² ≤ K E_ω³P`, imply `N⁴ ≤ K Θ_G²E_ω³P³`.  This isolates the analytic interpolation
input and avoids making any formal choice of fourth roots.
`NSFormal/SpatialInterpolation.lean` now proves the concrete measure-theoretic part of that
input as well.  Three `L²` Cauchy estimates for the mixed moments give
`V⁶ ≤ U₆²W₆W₂³`, with `W₂=2E_ω`; the file then derives (9.66), including signed negative
production, from the velocity and vorticity periodic Sobolev estimates
`U₆ ≤ C_uW₂³` and `W₆ ≤ C_ωP³`.  Thus no Hölder exponent arithmetic remains informal.
The velocity transfer is now concrete too: `NSFormal/DivCurl.lean` derives differentiated
incompressibility from divergence-free plus commuting mixed derivatives and proves
`∫|∇u|²=∫|curl u|²`.  `NSFormal/PeriodicSobolev.lean` now tensors the three coordinate
conditional-variance estimates and proves global mean-zero Poincare on Haar `T³`.
`NSFormal/PeriodicSobolevEuclidean.lean` proves the critical periodic `H¹ → L⁶` theorem through
an explicit fundamental cube, fixed smooth cutoff, Mathlib's Euclidean theorem, and a proved
`125`-period-cell multiplicity bound.  The final homogeneous adapter is now proved: it absorbs
the lower-order `L²` term for mean-zero velocity/vorticity, compares the descended derivative
with gradient energy, identifies the independently defined palinstrophy density pointwise, and
derives zero mean of vorticity from its curl representation.  `SpatialInterpolation.lean` now
uses these results to discharge both Sobolev premises and prove the production remainder
directly.  It also proves the unconditional baseline `G_ω ≤ P`, constructs the zero-safe
concrete ratio `Θ_G=G_ω/P`, proves `G_ω=Θ_GP` even at zero palinstrophy, and states the
production estimate with this ratio.  Any useful decay is therefore genuine dynamical depletion
rather than a missing functional inequality.
The sharp polynomial Young inequality
\[
 A z^3\le\frac\nu2z^4+\frac{27A^4}{32\nu^3}
\]
(now checked in `NSFormal/NewProofAlgebra.lean`) yields
\[
 E_\omega'+\frac\nu2P
 \le C_\nu\Theta_G^2E_\omega^3. \tag{9.66}
\]
Consequently either of the conditions
\[
 \int^{T}\Theta_G(t)^2E_\omega(t)^2\,dt<\infty,
 \qquad\text{or more concretely}\qquad
 \sup_{t\text{ near }T}\Theta_G(t)^2E_\omega(t)<\infty \tag{9.67}
\]
precludes blowup: divide (9.66) by \(E_\omega\), and use the kinetic-energy identity, which
already gives \(\int_0^T E_\omega(t)\,dt<\infty\).  Thus a putative singularity must keep a
large fraction of palinstrophy aligned with vortex-line differentiation at least at the rate
\(\Theta_G\gg E_\omega^{-1/2}\).  Proving that this cannot persist is now the most concrete
dynamic geometric target produced by the takeover route.

This geometric condition is sufficient, not necessary.  A nonconstant Beltrami/ABC field has
\(\omega=\lambda u\) and positive \(G_\omega,V_\omega\), but
\[
 N=\int u\cdot(u\cdot\nabla)u
   =\int u\cdot\nabla\frac{|u|^2}{2}=0.
\]
Its arbitrarily large amplitude heat-decaying Navier--Stokes solution is therefore harmless
despite the absolute Cauchy ledger being large.  To retain this cancellation, define the
zero-safe positive-production correlation
\[
 \mathfrak c(t)=
 \frac{[N(t)]_+^2}{G_\omega(t)V_\omega(a_\omega(t))}\in[0,1]. \tag{9.68}
\]
Repeating (9.65)--(9.66) replaces \(\Theta_G^2\) by
\(\mathfrak c^2\Theta_G^2\).  Thus there are two genuine closure channels:
vortex-line anisotropy makes \(\Theta_G\) small, while signed spatial or spectral cancellation
makes \(\mathfrak c\) small.  The filtered signed-flux program in Sections 6--9 is naturally a
route to the second channel; an absolute-value argument cannot see it.

`NSFormal/VortexStretching.lean` now checks the two periodic integration-by-parts identities,
the complete cancellation of amplitude derivatives under
\(\nabla\!\cdot(\rho\xi)=0\), the sharp constant and equality model in (9.58), the stronger
projected-curvature credit, the exact self-transport quotient, all three integrated estimates
in (9.60), its domination by total palinstrophy, and the explicit weighted frame and its
minimum.  `NSFormal/NewProofAlgebra.lean` checks both (9.61) and the Young/enstrophy reduction
(9.62).  These are conditional analytic reductions, not a proof that (9.61) holds for every
Navier--Stokes solution.

`NSFormal/Enstrophy.lean` supplies the concrete enstrophy PDE bridge.  It
constructs torus integration as a continuous linear functional, differentiates global
half-enstrophy, proves that the descended Haar-coordinate derivatives are the same first and
second derivatives used by the classical Navier--Stokes predicate, and derives both periodic
cancellations.  Hence the exact balance

\[
 E_\omega'(t)=N(t)-\nu P(t)
\]

is kernel-checked for the concrete smooth torus solution interface, and `N` is proved equal to
the production density controlled by the self-transport quotient and optimal weighted
variance.  `NSFormal/DynamicCriterion.lean` checks the scalar endgame of (9.66)--(9.67): from
`E' ≤ C Θ² E³`, `Θ²E ≤ M`, and `∫E ≤ B`, it derives
`E(t) ≤ E(0) exp(CMB)` through the logarithmic derivative.  The remaining assembly has now
also been kernel-checked.  `NSFormal/PeriodicRegularity.lean` derives the needed spatial
measurability and integrability from smooth periodic lifts;
`NSFormal/KineticEnergy.lean` derives the exact kinetic-energy law and pays
`∫E_ω ≤ K(0)/(2ν)` from the actual classical Navier--Stokes predicate; and
`NSFormal/ConcreteDynamicCriterion.lean` combines those facts with the proved spatial
interpolation theorem to give the explicit exponential enstrophy bound for the actual velocity,
pressure, and vorticity fields.  Thus the open content is the depletion/correlation control in
(9.67), not the spatial estimate (9.66), the kinetic-energy budget, differentiation under the
integral, periodic cancellation, or scalar continuation calculus.  The direct theorem still
states positivity of enstrophy and the mean-zero normalization explicitly; these are formal
packaging obligations, not the dynamic regularity mechanism.  Its Cauchy factorization and
div--curl energy equality are now derived internally from smoothness, incompressibility, and
`ω = curl u`, including the zero-quotient branch.  The same dynamic file
formalizes the zero-safe correlation in (9.68), proves it lies
in `[0,1]`, and proves its exact invariance under positive fixed-shape amplitude scaling
`(N,G,V) ↦ (A³N,A²G,A⁴V)`.  Correlation therefore preserves genuine signed cancellation but
does not by definition remove the amplitude obstruction; it must itself be dynamically
depleted.  The stronger concentration regression is now checked too.  With the Navier--Stokes
weights
\[
 (N,Q,V,P,E_\omega)\mapsto
 (\lambda^3N,\lambda^3Q,\lambda^3V,\lambda^3P,\lambda E_\omega),
\]
both \(\mathfrak c\) and \(\Theta_G=Q/P\) are invariant, while
\(\mathfrak c^2\Theta_G^2E_\omega\) grows by \(\lambda\).  The formal theorem also shows
that a fixed profile with positive base factor has an unbounded concentration family.  Hence
(9.67) must come from genuine deformation of the concentrating profile, not dimensional
normalization.

The signed coefficient admits a further exact cancellation.  Writing
\(Q=G_\omega\), \(V=V_\omega(0)\), and \(P\) for palinstrophy, the two reconstruction
identities \(\mathfrak c(QV)=[N]_+^2\) and \(\Theta_GP=Q\) give
\[
 (\mathfrak c^2\Theta_G^2E_\omega)(PV)^2=[N]_+^4E_\omega,
 \qquad
 \mathfrak c^2\Theta_G^2E_\omega
   =\frac{[N]_+^4E_\omega}{(PV)^2}. \tag{9.69}
\]
`DynamicCriterion.lean` checks this zero-safely, `SpatialInterpolation.lean` carries the
correlation through the root-free Young remainder, and `ConcreteDynamicCriterion.lean` proves
the resulting quotient-free continuation theorem for the actual classical PDE predicates.
Thus the signed research target no longer asks separately for decay of \(Q/P\): it asks whether
Navier--Stokes evolution can keep positive global stretching from saturating both palinstrophy
and weighted velocity variance at the concentration rate encoded by (9.69).

The equality case is quantitative.  The new abstract Cauchy residual theorem in
`DynamicCriterion.lean` gives
\[
 QV-N^2=Q\int\left|g-\frac{N}{Q}f\right|^2, \tag{9.70}
\]
where, in this application, \(f\) is normalized vorticity self-transport and \(g\) is
vorticity-weighted velocity.  Hence a concentrating sequence which keeps the signed factor
large must approach a constant-multiple relation between these two vector fields.  This is the
rigidity statement to test against curl compatibility and recurrent vortex lines; it is more
specific than asking for generic direction coherence.  The concrete torus instantiation and
its equality case are now kernel-checked as well.  After clearing the zero-safe normalization,
saturation forces
\[
 |ω|^2(u-a)+\frac{N}{Q}(ω\cdot\nabla)ω=0
 \quad\hbox{a.e.}, \tag{9.71}
\]
and the components parallel and perpendicular to ω are separately checked.  The parallel
equation is the scalar-amplitude transport constraint; the perpendicular equation is the
vortex-line bending constraint.  Regularizing its apparent division by \(|ω|^2\) with
\(|ω|^2+2ε\), integrating the resulting logarithmic self-transport, and sending
\(ε\downarrow0\) now yields the checked saturation obstruction
\[
 \int_{\mathbb T^3}\omega\cdot(u-a)=0,
 \qquad \int_{\mathbb T^3}u\cdot\omega=0
 \quad\text{when }\omega=\operatorname{curl}u. \tag{9.72}
\]
The stable version is now kernel-checked as well.  If \(D=QV-N^2\) is the Cauchy defect and
\(H_a=∫ω·(u-a)\), then
\[
 QH_a^2\le \operatorname{Vol}(\mathbb T^3)D, \qquad
 QH^2\le \operatorname{Vol}(\mathbb T^3)D
 \quad\text{for }\omega=\operatorname{curl}u. \tag{9.73}
\]
Near-saturation should therefore be attacked through (9.71)--(9.73), especially the question
whether helicity can be dynamically small throughout every concentration episode, not by
another absolute Cauchy estimate.  A first-integral localization now removes one source of
false smallness.  For a smooth scalar weight \(\phi\), the exact transport identity is
\[
 \int \phi\,
   \frac{(\omega\cdot\nabla)(|\omega|^2/2)}{|\omega|^2/2+\varepsilon}
 =-\int (\omega\cdot\nabla\phi)
   \log(|\omega|^2/2+\varepsilon), \tag{9.74}
\]
and the regularized residual test gives
\[
 Q\left(H_{a,\phi}^{\varepsilon}
       -\frac{N}{2Q}J_{\varepsilon,\phi}\right)^2
 \le \left(\int\phi^2\right)D, \qquad
 J_{\varepsilon,\phi}:=\int(\omega\cdot\nabla\phi)
       \log(|\omega|^2/2+\varepsilon). \tag{9.75}
\]
If \(\omega\cdot\nabla\phi=0\), then
\[
 Q\left(\int\phi\,\omega\cdot(u-a)\right)^2
 \le \left(\int\phi^2\right)D. \tag{9.76}
\]
Moreover, \(\int(\omega\cdot\nabla)\phi=0\) permits an arbitrary logarithmic center
\(k\), giving
\[
 |J_{\varepsilon,\phi}|
 \le B_{\varepsilon,\phi}(k):=
 \left(\int|\omega\cdot\nabla\phi|\right)
 \left\|\log(|\omega|^2/2+\varepsilon)-k\right\|_\infty. \tag{9.77}
\]
The fully concrete robust form is
\[
 Q\left(
   \max\left\{|H_{a,\phi}^{\varepsilon}|-
     \left|\frac{N}{2Q}\right|B_{\varepsilon,\phi}(k),0\right\}
   \right)^2
 \le \left(\int\phi^2\right)D. \tag{9.78}
\]
Hence opposite helicity signs on distinct invariant vortex regions cannot cancel out of the
defect obstruction.  This is not yet a universal closure: generic vortex-line flows need not
admit nonconstant global smooth first integrals.  Equation (9.75) identifies the viable
approximate route precisely--build evolving tube weights whose along-vorticity transport is
small enough that the positive part in (9.78) survives, with special care near
\(|\omega|=0\).  The free center in (9.77) removes any spatially constant amplitude logarithm.
Unlike the constant-weight gap, (9.76) is exactly concentration-critical when `phi` is
localized at the active scale: \(Q,D,H_{a,\phi},\int\phi^2\) scale as
\(\lambda^3,\lambda^6,1,\lambda^{-3}\), respectively.  The resulting equivalence of the
rescaled and base inequalities is kernel-checked in `DynamicCriterion.lean`.

The exact mechanism is also known to be nonvacuous on a nondegenerate periodic curl field.
`NSFormal/LocalizedHelicity.lean` constructs explicit smooth `u`, `omega`, and nonconstant
`phi` with `omega = curl u`, `omega dot grad phi = 0`, no vorticity zeros, and positive
self-transport quotient.  Lean proves that the unweighted helicity integral cancels but the
`phi`-weighted helicity integral is positive, hence the defect in (9.78) is strictly positive.
This static example validates the separation-of-signs idea; it does not supply the evolving,
active-scale tube weights required for a universal continuation theorem.

Normalizing (9.78) yields another kernel-checked diagnostic,
\[
 \frac{N^2}{QV}\le 1-\frac{H_{a,\phi}^2}{(\int\phi^2)V}.
\]
The subtracted ratio is exactly invariant under the concentration scaling above.  Hence a
uniformly positive localized-helicity signal creates a genuine but fixed correlation gap; it
does not by itself remove the factor of enstrophy in the critical continuation coefficient.
A successful dynamic use of (9.78) must make this normalized loss approach one, combine it
with decay of `Q/P`, or gain time integrability from the evolving cutoff.

This is now an exact continuation interface rather than only a diagnostic.  The kernel proves
the sign-free pointwise estimate
\[
 (\mathfrak c\Theta)^2E
 \le
 \left(\left(1-\frac{H_{a,\phi}^2}{(\int\phi^2)V}\right)\Theta\right)^2E,
\]
where `mathfrak c` is the zero-safe positive-production correlation.  It also proves that a
uniform bound on the right, combined with the cubic enstrophy rate and the kinetic-energy-paid
time integral, yields the exponential enstrophy bound.  The remaining geometric task is
precisely to construct evolving exact or approximate tube weights that control this product.

Finite vorticity-line averaging gives a concrete way to attack the approximate case.  For a
continuous flow `Phi` and seed `psi`, `FlowAveraging.lean` proves
\[
 \phi_L=\frac1L\int_0^L\psi\circ\Phi_s\,ds,
 \qquad
 \frac d{d\tau}\phi_L(\Phi_\tau x)
 =\frac{\psi(\Phi_{L+\tau}x)-\psi(\Phi_\tau x)}L.
\]
Thus bounded seeds give `O(L^-1)` tube leakage without a transverse flow box.  However, the
checked mean-ergodic endpoint shows that long averages retain only the transport-fixed component
of the seed; an explicit sign-flip isometry kills a nonzero seed in two steps.  The usable
dynamic condition is consequently a spectral one: the helicity seed must retain low
vorticity-transport frequency mass larger than the centered-logarithmic endpoint penalty.

To force a positive signal, use the adjoint-averaged weight `phi_L=A_L^*A_Lh`.  The checked
Hilbert identities give `H_phi=r_L^2` and `||phi_L||_2<=r_L`, where
`r_L=||A_Lh||_2`.  If `delta_L` denotes the paid transport leakage, the entire dynamic endgame is
now kernel-checked under the single critical estimate
\[
 \left(\left(1-\frac{(r_L-\delta_L)^2}{V}\right)\Theta\right)^2E\le M.
\]
This separates the remaining analysis into two quantitative questions: how much low transport
frequency helicity survives in `r_L`, and how small the centered-log endpoint error can be made
at the same averaging length.

At the operator level, the construction is no longer hypothetical and no longer assumes
operator-norm continuity.  `FlowKoopman.lean` constructs the normalized average by integrating
each strongly continuous `L²` orbit, proves it is a bounded linear contraction, and derives
strong continuity of Koopman transport from a continuous measure-preserving flow.  The group
law gives the exact endpoint formula
\[
 \|U_\tau A_Lh-A_Lh\|_2\le 2|\tau|\|h\|_2/L.
\]
Backward transport is the Hilbert adjoint, so the positive Fejér weight
`phi_L=A_L^*A_Lh` inherits the same finite transport defect and belongs to the generator domain
with generator norm at most `2||h||_2/L`.  Thus the Hilbert-space portion of `delta_L` is now an
output.  `TorusFlow.lean` tests the geometric bridge on the nontrivial Haar-preserving shear
`(x,y,z) ↦ (x+s cos y,y,z)`: its nonzero generator is proved to be a genuine periodic curl,
its pointwise action is identified with `w·nabla`, and its strong Koopman/Fejér average has an
explicit nonzero nonconstant retained first integral and positive signal.  The remaining formal
bridge is to carry that construction out for arbitrary smooth torus vorticity, prove the generator identity in
`L²`, and pass from the checked `L²` bound to the centered-logarithmic spatial leakage.  The
non-generic obstruction after that is a Navier--Stokes lower bound on retained
low-transport-frequency helicity.

The two scalar fourth-power steps in (9.36) are kernel-checked as
`variable_direction_strain_fourth_split` and `variable_direction_strain_fourth_paid` in
`NSFormal/NewProofAlgebra.lean`.
`NSFormal/PeriodicIntegration.lean` also checks the concrete Haar-measure integration by parts
and full three-factor Leibniz expansion for each coordinate term;
`NSFormal/AnisotropicIntegration.lean` sums those terms and checks cancellation of the middle
term under an explicit differentiated-incompressibility hypothesis.  It also checks the
pointwise two-product envelope and the exact `3³ × 2 = 54` integral bound, conditional on
coordinate majorants for \(u\), \(\nabla u\), and \(\nabla e\).  The same file now supplies
those majorants concretely using the Euclidean velocity norm and the coordinate-`ℓ¹` gradient,
which is equivalent to the Frobenius norm in dimension three.  The construction and parabolic
estimate of \(e\) are therefore the substantive unchecked steps.
`NSFormal/AnisotropicCriterion.lean` now instantiates the actual periodic gradient, transpose,
strain, curl, and cross-product actions.  It proves the integrated identity and the explicit
fourth-power bound with coefficient \(2\cdot54^2=5832\), then proves the time-integrability
handoff from the cross and mixed charges.  Its constant-coordinate-direction/zero-velocity
witness shows that the bundled smoothness, incompressibility, integrability, and unit-field
hypotheses are jointly satisfiable rather than vacuous.  The amplitude--direction algebra in
(9.39) is checked there; the weighted Cauchy and high-set steps in (9.40)--(9.41) are checked in
`NSFormal/Budget.lean`.  The same criterion file checks invariance of every derivative,
strain, and curl term under \(u\mapsto u-a\), and proves the centered fourth-power estimate.
What Lean does not assert is that a Navier--Stokes solution supplies
an adaptive field and selected region satisfying the required time budget.

Both (9.37) and (9.38) correctly accept the
shear test: \(\Omega_N\sim e^{-2\nu N^2t}\),
\(\|\nabla e_N\|_\infty^2=N^2\), and the rapid rotation is offset by its diffusive time scale.
The sharper debit (9.37) also retains the small velocity factor which a bare direction-gradient
estimate discards.

Thus a long near return either pays curvature or is simultaneously ballistic in homology and
close in mean square to a constant-direction flow; an irrational straight line is correctly
placed in the latter branch rather than falsely charged curvature.
`NSFormal/Recurrence.lean` kernel-checks (9.18), weighted Cauchy--Schwarz and the reverse-triangle
assembly in (9.19), the implication (9.19)--(9.20), the weighted charge implication (9.21), the
winding implication (9.22), the exact identity (9.23), the bound (9.24), and the strengthened
disjunction, including the balanced adaptive specialization (9.31)--(9.33).  It also
kernel-checks the interval `L²` pairing estimate (9.25); the ordinary
Sobolev/heat-smoothing calculation leading to (9.27) is analytic prose.

What is not yet closed is the global measure step.  An elementary solenoid is a normalized
long-time current, so arbitrarily many overlapping return segments cannot simply be charged as
distinct curves.  One needs a measurable return-time selection or an ergodic-current theorem
which assigns each solenoid once, sends its slow-drift returns to (9.21), and sends its ballistic
rotation vector to a stable-norm/homology charge.  This is now the precise recurrent nonclosed
obligation; the finite-segment geometry itself no longer requires an assumed closed curve.

Formula (9.7) is therefore a decomposition-free version of the manuscript's intended
long/short tube dichotomy, but only for the active component.  The remaining bridge must
combine its signed line-integral control with a separate persistent-set estimate.  Direction
palinstrophy may debit active axial decay, but (9.8)--(9.12) show that it cannot be the only
persistent debit; scalar-vorticity diffusion or genuinely time-dependent recurrence information
must also enter.  Converting these terms to absolute increment norms would simply restore the
\(L^4\) obstruction.

## 10. Exact spectral meaning of the signed defect

The signed commutator has a simpler interpretation for sharp Fourier cutoffs.  Write the
projected velocity equation as

\[
 \partial_tu=\nu\Delta u+N(u),
\]

where \(N=-\mathbb P(u\cdot\nabla u)\), and define the modal energy transfer

\[
 T_k(t)=\operatorname{Re}\bigl(\overline{\widehat u_k}\cdot\widehat N_k\bigr).
\]

Both \(\widehat u_k\) and \(\widehat N_k\) are perpendicular to \(k\).  Since
\(\widehat\omega_k=ik\times\widehat u_k\), the vector identity for two vectors orthogonal
to \(k\) gives

\[
 \operatorname{Re}\left(\overline{\widehat\omega_k}\cdot
       ik\times\widehat N_k\right)=|k|^2T_k.
 \tag{10.1}
\]

The nonlinearity conserves kinetic energy, so \(\sum_kT_k=0\).  Define the forward energy
flux through wavenumber \(K\) by

\[
 \Pi(K,t)=-\sum_{|k|\le K}T_k(t)=\sum_{|k|>K}T_k(t).
 \tag{10.2}
\]

Using \(|k|^2=\int_0^{|k|}2K\,dK\) and (10.2), the total nonlinear enstrophy production is

\[
 \sum_k|k|^2T_k
 =\int_0^\infty2K\,\Pi(K,t)\,dK.
 \tag{10.3}
\]

This is an exact layer-cake/Abel identity, not a turbulence model.  Similarly, if

\[
 E_{>K}=\frac12\sum_{|k|>K}|\widehat u_k|^2,
 \qquad
 D_{>K}=\sum_{|k|>K}|k|^2|\widehat u_k|^2,
\]

then the high-mode energy balance is

\[
 \frac d{dt}E_{>K}+\nu D_{>K}=\Pi(K,t).
 \tag{10.4}
\]

Consequently,

\[
 [\Pi(K,t)-\nu D_{>K}(t)]_+
 =\left[\frac d{dt}E_{>K}(t)\right]_+.
 \tag{10.5}
\]

The heat-filtered flux in Section 8 is itself a positive average of these sharp fluxes.  Abel
summation with the decreasing weight \(e^{-2sK^2}\) gives, for \(s>0\),

\[
 \boxed{
 \Pi_s(t)=\int_0^\infty 4sK e^{-2sK^2}\Pi(K,t)\,dK,}
 \qquad
 \int_0^\infty4sK e^{-2sK^2}\,dK=1.
 \tag{10.6}
\]

Thus positive variation of \(\Pi_s\) is not an artifact of Gaussian smoothing: it is positive
variation, as the averaging window moves through wavenumber, of a probability average of the
sharp forward flux.  `NSFormal/SpectralFlux.lean` checks the finite-shell analogue and proves
that nonnegative sharp forward flux gives nonnegative heat-filtered flux.

There is also an exact time-recurrence criterion.  Define the cumulative positive variation of
high-frequency kinetic energy by

\[
 V_K^+(T)=\int_0^T[\Pi(K,t)-\nu D_{>K}(t)]_+\,dt
 =\int_0^T\left[\frac d{dt}E_{>K}(t)\right]_+dt.
 \tag{10.7}
\]

Then for every \(t\le T\),

\[
 E_{>K}(t)\le E_{>K}(0)+V_K^+(T).
 \tag{10.8}
\]

The layer-cake identity for enstrophy is

\[
 \Omega(t)=\int_0^\infty2K E_{>K}(t)\,dK.
\]

Consequently,

\[
 \boxed{
 \sup_{0\le t\le T}\Omega(t)
 \le \Omega(0)+\int_0^\infty2K V_K^+(T)\,dK.}
 \tag{10.9}
\]

The positive part in (10.9) has an exact signed dual form.  In a finite shell truncation let
\(\lambda_i\) be increasing squared-wavenumber weights, let \(T_i\) be conservative nonlinear
transfer, let \(R_i\ge0\) be modal viscous loss, and put

\[
 g_i=T_i-R_i,
 \qquad G_j=\sum_{i>j}g_i=\Pi_j-R_{>j},
 \qquad \vartheta_j=\mathbf1_{\{G_j>0\}}.
 \tag{10.10}
\]

Define the monotone bang--bang multiplier

\[
 m_0=0,
 \qquad
 m_i=\sum_{j<i}(\lambda_{j+1}-\lambda_j)\vartheta_j.
 \tag{10.11}
\]

Then \(0\le m_{j+1}-m_j\le\lambda_{j+1}-\lambda_j\), and finite Abel summation gives

\[
 \boxed{
 \sum_j(\lambda_{j+1}-\lambda_j)[G_j]_+
 =\sum_i m_i g_i
 =\sum_j(\lambda_{j+1}-\lambda_j)\vartheta_j\Pi_j
   -\sum_i m_iR_i.}
 \tag{10.12}
\]

Moreover, the left side is the maximum of \(\sum_iq_i g_i\) over all multipliers with
\(q_0=0\) and
\(0\le q_{j+1}-q_j\le\lambda_{j+1}-\lambda_j\).  The selector identity, the
selected-flux-minus-dissipation equality, and this maximality statement are kernel-checked in
`NSFormal/SpectralFlux.lean`.

Formally passing from shells to wavenumber, set

\[
 a_t(K)=\mathbf1_{\{\Pi(K,t)>\nu D_{>K}(t)\}},
 \qquad m_t(r)=\int_0^r2K a_t(K)\,dK.
\]

Then \(0\le m_t(r)\le r^2\), and the instantaneous integrand required by (10.9) becomes

\[
 \boxed{
 H(t):=\int_0^\infty2K[\Pi(K,t)-\nu D_{>K}(t)]_+\,dK
 =\langle m_t(|D|)u,N(u)\rangle
  -\nu\langle m_t(|D|)\nabla u,\nabla u\rangle.}
 \tag{10.13}
\]

Equation (10.13) is the continuum analytic target suggested by the checked finite-shell
identity; justifying the limit and estimating the first pairing uniformly are not yet done.
It is nevertheless a sharper formulation of the missing theorem: the multiplier is
solution-dependent and rough in frequency, but it is monotone and dominated by the Laplacian,
and its dissipation is retained with the same selector.

Finiteness of \(\int_0^T H(t)\,dt\), equivalently the weighted variation integral in (10.9),
is therefore a sufficient continuation criterion for a smooth
solution.  It is deliberately one-sided: energy that reaches high modes once and then
dissipates is charged once, while repeated transfers into the same high-frequency tail are
charged through positive variation.  The open estimate is now an explicit bound on this
quantity using the energy-paid geometric band and vortex-line flux inequality.

The dangerous commutator is therefore repeated positive variation of high-frequency kinetic
energy, weighted more heavily as the cutoff rises.  A monotone or sign-definite estimate on the
absolute fourth-increment defect is stronger than necessary.  What must be ruled out is recurrent
forward transfer which continues to beat high-mode viscosity after the geometric near field has
already been absorbed.  `NSFormal/SpectralFlux.lean` also checks the finite-shell Abel identity
behind (10.3).

## 11. Relation to existing work

The direction cancellation in Section 3 is the mechanism introduced by
[Constantin--Fefferman](https://iumj.org/article/3627/).  The fixed-scale filtered near-field
argument and derivative-compatible increment observable are closely related to
[Yu, *Filtered Vortex Stretching and Subgrid Defects*](https://arxiv.org/abs/2606.27560), a
June 2026 preprint.  The contribution of this note is to combine that coercivity with the
periodic far-field integration by parts, optimize the common energy-paid exponent to \(1/3\),
exhibit the energy-class \(L^4\) obstruction explicitly, and restate the surviving signed
defect as positive high-mode energy variation and positive heat-scale flux slope.  The cubic
commutator estimate itself belongs to the classical
[Constantin--E--Titi coarse-graining method](https://doi.org/10.1007/BF02099744); the
\(1/12\)-gap calculation diagnoses the loss in the increment-only estimate, while the elementary
Lamb-vector identity (8.16) removes that loss for the global flux amplitude.
No novelty claim should be made before a broader literature audit.

The subgrid vortex force and circulation balance in (8.21)--(8.24) are the filtered identities
used by [Eyink, *The Cascade of Circulations in Fluid
Turbulence*](https://arxiv.org/abs/physics/0606159).  Equation (8.23), emphasizing that energy
flux and loop circulation flux test the same curled force, is an elementary Hodge consequence
of those identities.

The curve formulation (9.4) is consistent with
[Smirnov's decomposition of solenoidal vector charges](https://www.mathnet.ru/aa405).  For the
smooth solution considered here, local flow boxes already give (9.4); the measure-theoretic
decomposition is relevant when passing to weak or blow-up limits.

The normalized ballistic direction in (9.24) is close in spirit to
[Miller's locally anisotropic vorticity criterion](https://arxiv.org/abs/2002.02152), which
uses a global unit field \(v\) with controlled \(\nabla v\) and the critical quantity
\(v\times\omega\in L_t^4L_x^2\).  Existing
[periodic stability of two-dimensional motions](https://arxiv.org/abs/1406.0693) likewise
requires strong-norm closeness of the full 3D data and forcing.  Neither result currently
consumes an orbitwise mean-square direction estimate: assembling the directions \(e_\gamma\)
into a measurable, let alone Lipschitz, global field and proving the critical fourth-power
bound are additional obligations.  They nevertheless identify a rigorous interface for the
constant-direction branch rather than requiring a new planar stability theory from scratch.

The spectral viewpoint is also compatible with the dissipation-wavenumber framework of
[Cheskidov--Shvydkoy](https://arxiv.org/abs/1102.1944).  Their criterion shows why merely
identifying a cutoff is insufficient: regularity requires a quantitative relation between
forward transfer and viscosity above it.

## 12. Next theorem to attack

The target is no longer a pointwise strain inequality or an absolute fourth-moment bound.  It
is the following scale-transfer statement.

> **Dynamic high-tail recurrence target.**  At the common energy-paid scale
> \(s_G=(1+\Omega)^{-2/3}\), justify the continuum selector identity (10.13) and prove that its
> time integral is finite, equivalently constructing a stopping chain which explicitly debits
> every newly resolved band.
> In vortex-line variables, the new estimate must retain the signed line pairings in (8.20) or
> (8.25), use (9.7) only for the active component, and separately control persistent curves and
> pass the planar zero-direction-cost test (9.8)--(9.12).  In the recurrent ballistic branch it
> should use the adaptive split (9.31)--(9.33): fixed turning charge on the slow branch and
> energy-critical transverse vorticity on the ballistic branch, with scalar diffusion paying
> the exactly planar limit.  The missing theorem may use the explicit tensor \(P_c\) in
> (9.47) and close the now-checked, optimally centered Frobenius debit \(Q_c^F\) in
> (9.52)--(9.57).  The most promising version separates angular and radial charges as in
> (9.55), using scalar-vorticity diffusion on the radial branch instead of the globally
> critical fallback (9.54).
> Alternatively it must construct a single admissible spatial direction field from the
> orbitwise directions and prove (9.37)—more sharply, choose a useful frame \(a(t)\) and prove
> \(Q_{A,a}\Omega\lesssim\nu^4\) from (9.40)--(9.45)—or control the signed work without making
> either construction.

An absolute \(L^4\)-increment bound is impossible from energy alone by (5.5)--(5.6).  A viable
proof must use at least one of:

1. cancellation of the signed cubic flux against the solution-dependent monotone multiplier
   (10.11)--(10.13), now with amplitude at the geometric scale paid by (8.18);
2. the energy--circulation duality (8.23)--(8.25), together with the active vortex-line bound
   (9.7) and a genuinely dynamic or scalar-diffusive estimate for the persistent component;
3. a parabolic recurrence theorem showing that a scale-critical profile cannot repeatedly
   outrun the speed limit in (8.5) while continuing to beat high-mode viscosity.  The theorem
   must debit those outruns: the safe terminal schedule itself is ruled out by (8.6)--(8.7).

This is substantially narrower than the manuscript's organization theorem: every term is an
explicit functional of the solution, and the two parts already removed are controlled by exact
identities and the energy inequality.
