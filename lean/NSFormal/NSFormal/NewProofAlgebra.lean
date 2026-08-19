import Mathlib

/-!
# Lean gate: the Write-Out Campaign's NEW algebra (certifying the new proofs)
Identities that entered DURING W1–W16, previously sympy-only. Improper integrals via the
antiderivative route (integral_Ioi_of_hasDerivAt_of_tendsto).
-/

open MeasureTheory Real Filter Topology Set

/-- W10's exponent chain: (x^(-1/3))^(-5/2) = x^(5/6) — the arithmetic behind the γ-display. -/
theorem w10_exponent_chain (x : ℝ) (hx : 0 < x) :
    (x ^ (-(1:ℝ)/3)) ^ (-(5:ℝ)/2) = x ^ ((5:ℝ)/6) := by
  rw [← Real.rpow_mul hx.le]
  norm_num

/-- At the geometric heat scale `s = x⁻²ᐟ³`, the heat-kernel smoothing factor
`s⁻³ᐟ⁴` times the enstrophy factor `x¹ᐟ²` is exactly linear in `x`.  This is the
exponent arithmetic behind the Lamb-vector flux estimate in `DYNAMICS.md`. -/
theorem lamb_flux_exponent_chain (x : ℝ) (hx : 0 < x) :
    (x ^ (-(2 : ℝ) / 3)) ^ (-(3 : ℝ) / 4) * x ^ ((1 : ℝ) / 2) = x := by
  rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  norm_num

/-- At the geometric heat scale, the squared \(L²\)-to-\(L^\infty\) heat-smoothing factor
`s⁻³ᐟ²` is exactly linear in the enstrophy rate `x`. -/
theorem filtered_stretching_exponent_chain (x : ℝ) (hx : 0 < x) :
    (x ^ (-(2 : ℝ) / 3)) ^ (-(3 : ℝ) / 2) = x := by
  rw [← Real.rpow_mul hx.le]
  norm_num

/-- Energy-paid threshold for the normalized ballistic-direction error.  If the squared
transverse vorticity is bounded by `2 * W * deficit * mass`, the curve-family mass obeys a
square bound, and `W * deficit` stays bounded, then the fourth power of the transverse
component is linear in enstrophy. -/
theorem ballistic_cross_component_fourth_paid
    {crossSq W deficit mass volumeConstant enstrophy threshold : ℝ}
    (hcross0 : 0 ≤ crossSq) (hW : 0 ≤ W) (hdeficit : 0 ≤ deficit)
    (hmass0 : 0 ≤ mass)
    (hthreshold0 : 0 ≤ threshold)
    (hcross : crossSq ≤ 2 * W * deficit * mass)
    (hmass : mass ^ 2 ≤ volumeConstant * enstrophy)
    (hthreshold : W * deficit ≤ threshold) :
    crossSq ^ 2 ≤ 4 * threshold ^ 2 * volumeConstant * enstrophy := by
  have hWd0 : 0 ≤ W * deficit := mul_nonneg hW hdeficit
  have hright0 : 0 ≤ 2 * W * deficit * mass := by positivity
  have hcross_sq : crossSq ^ 2 ≤ (2 * W * deficit * mass) ^ 2 :=
    (sq_le_sq₀ hcross0 hright0).2 hcross
  have hthreshold_sq : (W * deficit) ^ 2 ≤ threshold ^ 2 :=
    (sq_le_sq₀ hWd0 hthreshold0).2 hthreshold
  calc
    crossSq ^ 2 ≤ (2 * W * deficit * mass) ^ 2 := hcross_sq
    _ = 4 * (W * deficit) ^ 2 * mass ^ 2 := by ring
    _ ≤ 4 * threshold ^ 2 * mass ^ 2 := by gcongr
    _ ≤ 4 * threshold ^ 2 * (volumeConstant * enstrophy) := by gcongr
    _ = 4 * threshold ^ 2 * volumeConstant * enstrophy := by ring

/-- Exact fourth-power split behind the variable-direction anisotropic ledger.  Here `mixed`
is the still-unestimated integration-by-parts error caused by spatial variation of the selected
direction.  Keeping it explicit avoids prematurely replacing its signed integral by a uniform
gradient norm. -/
theorem variable_direction_strain_fourth_split
    {strainSq crossSq mixed : ℝ}
    (hstrain0 : 0 ≤ strainSq) (hcross0 : 0 ≤ crossSq) (hmixed0 : 0 ≤ mixed)
    (hstrain : strainSq ≤ crossSq / 4 + mixed) :
    strainSq ^ 2 ≤ crossSq ^ 2 / 8 + 2 * mixed ^ 2 := by
  have hsum0 : 0 ≤ crossSq / 4 + mixed := by positivity
  have hstrainSq : strainSq ^ 2 ≤ (crossSq / 4 + mixed) ^ 2 :=
    (sq_le_sq₀ hstrain0 hsum0).2 hstrain
  have hsplit :
      (crossSq / 4 + mixed) ^ 2 ≤ crossSq ^ 2 / 8 + 2 * mixed ^ 2 := by
    nlinarith [sq_nonneg (crossSq / 4 - mixed)]
  exact hstrainSq.trans hsplit

/-- Energy-gradient corollary of `variable_direction_strain_fourth_split`.  If the transverse
fourth power is enstrophy-paid and the error square is bounded by energy times enstrophy times
the squared direction-gradient scale, then the directional strain fourth power has exactly the
displayed stronger parabolic debit. -/
theorem variable_direction_strain_fourth_paid
    {strainSq crossSq mixed crossCoefficient mixedCoefficient energy energyCap
      enstrophy gradientSq : ℝ}
    (hstrain0 : 0 ≤ strainSq) (hcross0 : 0 ≤ crossSq) (hmixed0 : 0 ≤ mixed)
    (hmixedCoefficient0 : 0 ≤ mixedCoefficient)
    (henstrophy0 : 0 ≤ enstrophy) (hgradientSq0 : 0 ≤ gradientSq)
    (hstrain : strainSq ≤ crossSq / 4 + mixed)
    (hcross : crossSq ^ 2 ≤ crossCoefficient * enstrophy)
    (hmixed : mixed ^ 2 ≤
      mixedCoefficient * energy * enstrophy * gradientSq)
    (henergy : energy ≤ energyCap) :
    strainSq ^ 2 ≤
      (crossCoefficient / 8 +
        2 * mixedCoefficient * energyCap * gradientSq) * enstrophy := by
  have hsplit := variable_direction_strain_fourth_split
    hstrain0 hcross0 hmixed0 hstrain
  calc
    strainSq ^ 2 ≤ crossSq ^ 2 / 8 + 2 * mixed ^ 2 := hsplit
    _ ≤ (crossCoefficient * enstrophy) / 8 +
        2 * (mixedCoefficient * energy * enstrophy * gradientSq) := by gcongr
    _ ≤ (crossCoefficient * enstrophy) / 8 +
        2 * (mixedCoefficient * energyCap * enstrophy * gradientSq) := by gcongr
    _ = (crossCoefficient / 8 +
        2 * mixedCoefficient * energyCap * gradientSq) * enstrophy := by ring

/-- Critical absorption ledger for the normalized-vorticity direction.  If its directional
strain fourth power is bounded by palinstrophy times the inverse-vorticity quotient, then the
quartic strain interpolation absorbs the nonlinear production precisely when the
scale-invariant product `quotient * enstrophy` is small enough.  Smallness of `quotient` alone
would be dimensionally incorrect. -/
theorem critical_weighted_direction_debit_absorbed
    {nonlinear directionalFourth palinstrophy quotient enstrophy
      coefficient viscosity : ℝ}
    (hnonlinear0 : 0 ≤ nonlinear)
    (hpalinstrophy0 : 0 ≤ palinstrophy)
    (henstrophy0 : 0 ≤ enstrophy)
    (hviscosity0 : 0 ≤ viscosity)
    (hdirection : directionalFourth ≤ palinstrophy * quotient)
    (hnonlinear : nonlinear ^ 4 ≤
      coefficient ^ 4 * directionalFourth * enstrophy * palinstrophy ^ 3)
    (hcritical : coefficient ^ 4 * quotient * enstrophy ≤ viscosity ^ 4) :
    nonlinear ≤ viscosity * palinstrophy := by
  have hfourth : nonlinear ^ 4 ≤ (viscosity * palinstrophy) ^ 4 := by
    calc
      nonlinear ^ 4 ≤
          coefficient ^ 4 * directionalFourth * enstrophy * palinstrophy ^ 3 :=
        hnonlinear
      _ ≤ coefficient ^ 4 * (palinstrophy * quotient) * enstrophy *
          palinstrophy ^ 3 := by
        gcongr
      _ = (coefficient ^ 4 * quotient * enstrophy) * palinstrophy ^ 4 := by
        ring
      _ ≤ viscosity ^ 4 * palinstrophy ^ 4 := by
        gcongr
      _ = (viscosity * palinstrophy) ^ 4 := by
        ring
  exact (pow_le_pow_iff_left₀ hnonlinear0
    (mul_nonneg hviscosity0 hpalinstrophy0) (by norm_num : (4 : ℕ) ≠ 0)).mp hfourth

/-- Exact scalar absorption associated with the sharp direction-only stretching identity.  If
`production² ≤ 2 · directionDissipation · weightedVelocityVariance`, then Young's
inequality pays the direction charge directly from viscosity and leaves only the critical
weighted velocity variance. -/
theorem direction_production_le_diffusion_add_weighted_variance
    {production directionDissipation weightedVelocityVariance viscosity : ℝ}
    (hdirection : 0 ≤ directionDissipation)
    (hvariance : 0 ≤ weightedVelocityVariance)
    (hviscosity : 0 < viscosity)
    (hproduction : production ^ 2 ≤
      2 * directionDissipation * weightedVelocityVariance) :
    production ≤ viscosity * directionDissipation +
      weightedVelocityVariance / (2 * viscosity) := by
  have hright0 : 0 ≤ viscosity * directionDissipation +
      weightedVelocityVariance / (2 * viscosity) := by positivity
  have hyoung : 2 * directionDissipation * weightedVelocityVariance ≤
      (viscosity * directionDissipation +
        weightedVelocityVariance / (2 * viscosity)) ^ 2 := by
    have hid :
        (viscosity * directionDissipation +
            weightedVelocityVariance / (2 * viscosity)) ^ 2 -
          2 * directionDissipation * weightedVelocityVariance =
        (viscosity * directionDissipation -
            weightedVelocityVariance / (2 * viscosity)) ^ 2 := by
      field_simp [hviscosity.ne']
      ring
    nlinarith [sq_nonneg
      (viscosity * directionDissipation -
        weightedVelocityVariance / (2 * viscosity))]
  by_cases hp : production ≤ 0
  · exact hp.trans hright0
  · have hp0 : 0 ≤ production := le_of_lt (lt_of_not_ge hp)
    apply (sq_le_sq₀ hp0 hright0).mp
    exact hproduction.trans hyoung

/-- After direction-only absorption, the enstrophy balance retains scalar-amplitude diffusion.
This is the algebraic endpoint of the new takeover reduction. -/
theorem enstrophy_rate_add_radial_diffusion_le_weighted_variance
    {enstrophyRate radialDissipation directionDissipation
      weightedVelocityVariance viscosity production : ℝ}
    (hbalance : enstrophyRate +
      viscosity * (radialDissipation + directionDissipation) ≤ production)
    (hproduction : production ≤ viscosity * directionDissipation +
      weightedVelocityVariance / (2 * viscosity)) :
    enstrophyRate + viscosity * radialDissipation ≤
      weightedVelocityVariance / (2 * viscosity) := by
  linarith

/-- Scale-critical two-factor absorption criterion for the direction-only identity.  It keeps
the planar limit exact: when direction dissipation vanishes, no condition on the weighted
velocity variance is needed. -/
theorem direction_production_absorbed_by_total_diffusion
    {production directionDissipation totalDissipation
      weightedVelocityVariance viscosity : ℝ}
    (htotal : 0 ≤ totalDissipation) (hviscosity : 0 ≤ viscosity)
    (hproduction : production ^ 2 ≤
      2 * directionDissipation * weightedVelocityVariance)
    (hcritical : 2 * directionDissipation * weightedVelocityVariance ≤
      viscosity ^ 2 * totalDissipation ^ 2) :
    production ≤ viscosity * totalDissipation := by
  have hright : 0 ≤ viscosity * totalDissipation :=
    mul_nonneg hviscosity htotal
  by_cases hp : production ≤ 0
  · exact hp.trans hright
  · have hp0 : 0 ≤ production := le_of_lt (lt_of_not_ge hp)
    apply (sq_le_sq₀ hp0 hright).mp
    calc
      production ^ 2 ≤ 2 * directionDissipation * weightedVelocityVariance :=
        hproduction
      _ ≤ viscosity ^ 2 * totalDissipation ^ 2 := hcritical
      _ = (viscosity * totalDissipation) ^ 2 := by ring

/-- Young fallback for the stronger effective direction charge.  The geometric inequality
`effectiveDirection ≤ 2 directionDissipation` pays half of the effective charge from the
full direction diffusion and retains the improved factor `1/2` on the variance remainder. -/
theorem effective_direction_production_le_diffusion_add_weighted_variance
    {production effectiveDirection directionDissipation
      weightedVelocityVariance viscosity : ℝ}
    (hdirection : 0 ≤ directionDissipation)
    (hvariance : 0 ≤ weightedVelocityVariance)
    (hviscosity : 0 < viscosity)
    (heffective : effectiveDirection ≤ 2 * directionDissipation)
    (hproduction : production ^ 2 ≤
      effectiveDirection * weightedVelocityVariance) :
    production ≤ viscosity * directionDissipation +
      weightedVelocityVariance / (2 * viscosity) := by
  apply direction_production_le_diffusion_add_weighted_variance
    hdirection hvariance hviscosity
  exact hproduction.trans
    (mul_le_mul_of_nonneg_right heffective hvariance)

/-- Exact scale-critical absorption criterion with the projected self-transport credit left
inside the effective direction factor. -/
theorem effective_direction_production_absorbed_by_total_diffusion
    {production effectiveDirection totalDissipation
      weightedVelocityVariance viscosity : ℝ}
    (htotal : 0 ≤ totalDissipation) (hviscosity : 0 ≤ viscosity)
    (hproduction : production ^ 2 ≤
      effectiveDirection * weightedVelocityVariance)
    (hcritical : effectiveDirection * weightedVelocityVariance ≤
      viscosity ^ 2 * totalDissipation ^ 2) :
    production ≤ viscosity * totalDissipation := by
  have hright : 0 ≤ viscosity * totalDissipation :=
    mul_nonneg hviscosity htotal
  by_cases hp : production ≤ 0
  · exact hp.trans hright
  · have hp0 : 0 ≤ production := le_of_lt (lt_of_not_ge hp)
    apply (sq_le_sq₀ hp0 hright).mp
    calc
      production ^ 2 ≤ effectiveDirection * weightedVelocityVariance := hproduction
      _ ≤ viscosity ^ 2 * totalDissipation ^ 2 := hcritical
      _ = (viscosity * totalDissipation) ^ 2 := by ring

/-- Static amplitude-scaling obstruction for the exact critical product.  Under
`u ↦ A u`, the line-transport and palinstrophy charges scale like `A²`, while the
vorticity-weighted velocity variance scales like `A⁴`; hence the normalized product grows
like `A²` and cannot satisfy a data-independent smallness bound. -/
theorem selfTransport_variance_critical_product_amplitude_scaling
    (A lineTransport palinstrophy weightedVariance : ℝ)
    (hA : A ≠ 0) (hP : palinstrophy ≠ 0) :
    ((A ^ 2 * lineTransport) / (A ^ 2 * palinstrophy)) *
        ((A ^ 4 * weightedVariance) / (A ^ 2 * palinstrophy)) =
      A ^ 2 * ((lineTransport / palinstrophy) *
        (weightedVariance / palinstrophy)) := by
  field_simp [hA, hP]

/-- Sharp polynomial Young inequality for the `P³ᐟ⁴` production term.  The remainder
coefficient is attained at `z = 3A/(2ν)`. -/
theorem three_quarters_production_young
    (A z viscosity : ℝ) (hA : 0 ≤ A) (hz : 0 ≤ z) (hviscosity : 0 < viscosity) :
    A * z ^ 3 ≤
      (viscosity / 2) * z ^ 4 + 27 * A ^ 4 / (32 * viscosity ^ 3) := by
  have hden : 0 < 32 * viscosity ^ 3 := by positivity
  have hfactor :
      0 ≤ (-3 * A + 2 * viscosity * z) ^ 2 *
        (3 * A ^ 2 + 4 * A * viscosity * z + 4 * viscosity ^ 2 * z ^ 2) := by
    positivity
  have hid :
      27 * A ^ 4 -
        (A * z ^ 3 - (viscosity / 2) * z ^ 4) *
          (32 * viscosity ^ 3) =
      (-3 * A + 2 * viscosity * z) ^ 2 *
        (3 * A ^ 2 + 4 * A * viscosity * z + 4 * viscosity ^ 2 * z ^ 2) := by
    ring
  have hsub :
      A * z ^ 3 - (viscosity / 2) * z ^ 4 ≤
        27 * A ^ 4 / (32 * viscosity ^ 3) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hfactor]
  linarith

/-- Root-free assembly of the quotient and weighted-variance estimates.  This
is the exact fourth-power form needed before the sharp `P³ᴵ⁴` Young step. -/
theorem quotient_variance_fourth_production
    {production quotient quotientFraction weightedVariance
      enstrophy palinstrophy interpolationConstant : ℝ}
    (hproduction : production ^ 2 ≤ quotient * weightedVariance)
    (hquotient0 : 0 ≤ quotient) (hvariance0 : 0 ≤ weightedVariance)
    (_hfraction0 : 0 ≤ quotientFraction)
    (_henstrophy0 : 0 ≤ enstrophy) (_hpalinstrophy0 : 0 ≤ palinstrophy)
    (_hconstant0 : 0 ≤ interpolationConstant)
    (hquotient : quotient ≤ quotientFraction * palinstrophy)
    (hvariance : weightedVariance ^ 2 ≤
      interpolationConstant * enstrophy ^ 3 * palinstrophy) :
    production ^ 4 ≤
      interpolationConstant * quotientFraction ^ 2 *
        enstrophy ^ 3 * palinstrophy ^ 3 := by
  have hqv0 : 0 ≤ quotient * weightedVariance :=
    mul_nonneg hquotient0 hvariance0
  have hsquare : (production ^ 2) ^ 2 ≤
      (quotient * weightedVariance) ^ 2 :=
    (sq_le_sq₀ (sq_nonneg production) hqv0).2 hproduction
  calc
    production ^ 4 = (production ^ 2) ^ 2 := by ring
    _ ≤ (quotient * weightedVariance) ^ 2 := hsquare
    _ = quotient ^ 2 * weightedVariance ^ 2 := by ring
    _ ≤ (quotientFraction * palinstrophy) ^ 2 *
        (interpolationConstant * enstrophy ^ 3 * palinstrophy) := by
      gcongr
    _ = interpolationConstant * quotientFraction ^ 2 *
        enstrophy ^ 3 * palinstrophy ^ 3 := by ring

/-- Sharp root-free Young inequality.  If `N⁴ ≤ A P³`, then the
`P³ᴵ⁴` term is absorbed without introducing real fourth roots. -/
theorem fourth_production_young
    {production coefficient palinstrophy viscosity : ℝ}
    (hproduction0 : 0 ≤ production) (hcoefficient0 : 0 ≤ coefficient)
    (hpalinstrophy0 : 0 ≤ palinstrophy) (hviscosity : 0 < viscosity)
    (hfourth : production ^ 4 ≤ coefficient * palinstrophy ^ 3) :
    production ≤ (viscosity / 2) * palinstrophy +
      27 * coefficient / (32 * viscosity ^ 3) := by
  by_cases hP0 : palinstrophy = 0
  · subst palinstrophy
    have hp4 : production ^ 4 = 0 := by
      apply le_antisymm
      · simpa using hfourth
      · positivity
    have hp : production = 0 :=
      (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hp4
    rw [hp]
    positivity
  · have hP : 0 < palinstrophy := lt_of_le_of_ne hpalinstrophy0 (Ne.symm hP0)
    let y : ℝ := viscosity * palinstrophy
    have hy : 0 < y := mul_pos hviscosity hP
    have hden : 0 < 32 * y ^ 3 := by positivity
    have hfactor :
        0 ≤ (3 * production - 2 * y) ^ 2 *
          (3 * production ^ 2 + 4 * production * y + 4 * y ^ 2) := by
      positivity
    have hid :
        ((y / 2 + 27 * production ^ 4 / (32 * y ^ 3)) - production) *
            (32 * y ^ 3) =
          (3 * production - 2 * y) ^ 2 *
            (3 * production ^ 2 + 4 * production * y + 4 * y ^ 2) := by
      field_simp [hy.ne']
      ring
    have hbase :
        production ≤ y / 2 + 27 * production ^ 4 / (32 * y ^ 3) := by
      have hdiffMul : 0 ≤
          ((y / 2 + 27 * production ^ 4 / (32 * y ^ 3)) - production) *
            (32 * y ^ 3) := by
        rw [hid]
        exact hfactor
      have hdiff : 0 ≤
          (y / 2 + 27 * production ^ 4 / (32 * y ^ 3)) - production :=
        (mul_nonneg_iff_of_pos_right hden).mp hdiffMul
      linarith
    have hcoefficient : production ^ 4 / palinstrophy ^ 3 ≤ coefficient := by
      apply (div_le_iff₀ (pow_pos hP 3)).2
      simpa [mul_comm] using hfourth
    have hremainder :
        27 * production ^ 4 / (32 * y ^ 3) ≤
          27 * coefficient / (32 * viscosity ^ 3) := by
      dsimp [y]
      have hscale : 0 ≤ 27 / (32 * viscosity ^ 3) := by positivity
      calc
        27 * production ^ 4 / (32 * (viscosity * palinstrophy) ^ 3) =
            (27 / (32 * viscosity ^ 3)) *
              (production ^ 4 / palinstrophy ^ 3) := by
          field_simp [hviscosity.ne', hP0]
        _ ≤ (27 / (32 * viscosity ^ 3)) * coefficient := by
          exact mul_le_mul_of_nonneg_left hcoefficient hscale
        _ = 27 * coefficient / (32 * viscosity ^ 3) := by ring
    calc
      production ≤ y / 2 + 27 * production ^ 4 / (32 * y ^ 3) := hbase
      _ ≤ y / 2 + 27 * coefficient / (32 * viscosity ^ 3) := by gcongr
      _ = (viscosity / 2) * palinstrophy +
          27 * coefficient / (32 * viscosity ^ 3) := by
        dsimp [y]
        ring

/-- End-to-end root-free quotient remainder.  The only analytic input not
contained in the exact kinematic ledger is the weighted-variance interpolation
`V² ≤ K E³ P`. -/
theorem quotient_variance_cubic_remainder
    {production quotient quotientFraction weightedVariance
      enstrophy palinstrophy interpolationConstant viscosity : ℝ}
    (hproduction0 : 0 ≤ production)
    (hproduction : production ^ 2 ≤ quotient * weightedVariance)
    (hquotient0 : 0 ≤ quotient) (hvariance0 : 0 ≤ weightedVariance)
    (hfraction0 : 0 ≤ quotientFraction)
    (henstrophy0 : 0 ≤ enstrophy) (hpalinstrophy0 : 0 ≤ palinstrophy)
    (hconstant0 : 0 ≤ interpolationConstant) (hviscosity : 0 < viscosity)
    (hquotient : quotient ≤ quotientFraction * palinstrophy)
    (hvariance : weightedVariance ^ 2 ≤
      interpolationConstant * enstrophy ^ 3 * palinstrophy) :
    production ≤ (viscosity / 2) * palinstrophy +
      27 * (interpolationConstant * quotientFraction ^ 2 * enstrophy ^ 3) /
        (32 * viscosity ^ 3) := by
  apply fourth_production_young hproduction0
    (mul_nonneg (mul_nonneg hconstant0 (sq_nonneg quotientFraction))
      (pow_nonneg henstrophy0 3))
    hpalinstrophy0 hviscosity
  have hfourth := quotient_variance_fourth_production
    hproduction hquotient0 hvariance0 hfraction0 henstrophy0
      hpalinstrophy0 hconstant0 hquotient hvariance
  simpa only [mul_assoc] using hfourth

/-- Integer-power moment ledger for the weighted velocity variance.  The three hypotheses
are ordinary `L²` Cauchy inequalities for
`V = ∫ |u|²|ω|²`, `H = ∫ |u|⁴|ω|²`, and `J = ∫ |u|²|ω|⁴`:
`V² ≤ H W₂`, `H² ≤ U₆ J`, and `J² ≤ H W₆`.  Their combination avoids all
fractional Hölder powers. -/
theorem weighted_variance_sixth_moment_ledger
    {variance mixedVelocityFour mixedVorticityFour velocitySixth
      vorticitySecond vorticitySixth : ℝ}
    (hmixedVelocity0 : 0 ≤ mixedVelocityFour)
    (hmixedVorticity0 : 0 ≤ mixedVorticityFour)
    (hvelocitySixth0 : 0 ≤ velocitySixth)
    (hvorticitySecond0 : 0 ≤ vorticitySecond)
    (hvorticitySixth0 : 0 ≤ vorticitySixth)
    (hvariance : variance ^ 2 ≤ mixedVelocityFour * vorticitySecond)
    (hmixedVelocity : mixedVelocityFour ^ 2 ≤
      velocitySixth * mixedVorticityFour)
    (hmixedVorticity : mixedVorticityFour ^ 2 ≤
      mixedVelocityFour * vorticitySixth) :
    variance ^ 6 ≤ velocitySixth ^ 2 * vorticitySixth * vorticitySecond ^ 3 := by
  have hmixedVelocityFourth : mixedVelocityFour ^ 4 ≤
      (velocitySixth * mixedVorticityFour) ^ 2 := by
    calc
      mixedVelocityFour ^ 4 = (mixedVelocityFour ^ 2) ^ 2 := by ring
      _ ≤ (velocitySixth * mixedVorticityFour) ^ 2 :=
        (sq_le_sq₀ (sq_nonneg mixedVelocityFour)
          (mul_nonneg hvelocitySixth0 hmixedVorticity0)).2 hmixedVelocity
  have hmixedVelocityCube : mixedVelocityFour ^ 3 ≤
      velocitySixth ^ 2 * vorticitySixth := by
    by_cases hzero : mixedVelocityFour = 0
    · have hnonneg : 0 ≤ velocitySixth ^ 2 * vorticitySixth :=
        mul_nonneg (sq_nonneg velocitySixth) hvorticitySixth0
      simpa [hzero] using hnonneg
    · have hpositive : 0 < mixedVelocityFour :=
        lt_of_le_of_ne hmixedVelocity0 (Ne.symm hzero)
      apply le_of_mul_le_mul_left
      · calc
          mixedVelocityFour * mixedVelocityFour ^ 3 = mixedVelocityFour ^ 4 := by ring
          _ ≤ (velocitySixth * mixedVorticityFour) ^ 2 :=
            hmixedVelocityFourth
          _ = velocitySixth ^ 2 * mixedVorticityFour ^ 2 := by ring
          _ ≤ velocitySixth ^ 2 *
              (mixedVelocityFour * vorticitySixth) :=
            mul_le_mul_of_nonneg_left hmixedVorticity (sq_nonneg velocitySixth)
          _ = mixedVelocityFour *
              (velocitySixth ^ 2 * vorticitySixth) := by ring
      · exact hpositive
  calc
    variance ^ 6 = (variance ^ 2) ^ 3 := by ring
    _ ≤ (mixedVelocityFour * vorticitySecond) ^ 3 :=
      pow_le_pow_left₀ (sq_nonneg variance) hvariance 3
    _ = mixedVelocityFour ^ 3 * vorticitySecond ^ 3 := by ring
    _ ≤ (velocitySixth ^ 2 * vorticitySixth) *
        vorticitySecond ^ 3 := by gcongr
    _ = velocitySixth ^ 2 * vorticitySixth * vorticitySecond ^ 3 := by ring

/-- Add the two standard sixth-moment Sobolev inputs to the integer-power ledger. -/
theorem weighted_variance_sixth_of_sobolev_moments
    {variance mixedVelocityFour mixedVorticityFour velocitySixth
      vorticitySecond vorticitySixth palinstrophy
      velocitySobolevConstant vorticitySobolevConstant : ℝ}
    (hmixedVelocity0 : 0 ≤ mixedVelocityFour)
    (hmixedVorticity0 : 0 ≤ mixedVorticityFour)
    (hvelocitySixth0 : 0 ≤ velocitySixth)
    (hvorticitySecond0 : 0 ≤ vorticitySecond)
    (hvorticitySixth0 : 0 ≤ vorticitySixth)
    (_hpalinstrophy0 : 0 ≤ palinstrophy)
    (_hvelocityConstant0 : 0 ≤ velocitySobolevConstant)
    (_hvorticityConstant0 : 0 ≤ vorticitySobolevConstant)
    (hvariance : variance ^ 2 ≤ mixedVelocityFour * vorticitySecond)
    (hmixedVelocity : mixedVelocityFour ^ 2 ≤
      velocitySixth * mixedVorticityFour)
    (hmixedVorticity : mixedVorticityFour ^ 2 ≤
      mixedVelocityFour * vorticitySixth)
    (hvelocitySobolev : velocitySixth ≤
      velocitySobolevConstant * vorticitySecond ^ 3)
    (hvorticitySobolev : vorticitySixth ≤
      vorticitySobolevConstant * palinstrophy ^ 3) :
    variance ^ 6 ≤
      velocitySobolevConstant ^ 2 * vorticitySobolevConstant *
        vorticitySecond ^ 9 * palinstrophy ^ 3 := by
  have hmoment := weighted_variance_sixth_moment_ledger
    hmixedVelocity0 hmixedVorticity0 hvelocitySixth0 hvorticitySecond0
      hvorticitySixth0 hvariance hmixedVelocity hmixedVorticity
  calc
    variance ^ 6 ≤ velocitySixth ^ 2 * vorticitySixth *
        vorticitySecond ^ 3 := hmoment
    _ ≤ (velocitySobolevConstant * vorticitySecond ^ 3) ^ 2 *
        (vorticitySobolevConstant * palinstrophy ^ 3) *
          vorticitySecond ^ 3 := by gcongr
    _ = velocitySobolevConstant ^ 2 * vorticitySobolevConstant *
        vorticitySecond ^ 9 * palinstrophy ^ 3 := by ring

/-- Root-free extraction of `V² ≤ K W₂³ P`.  It is enough that the chosen interpolation
constant has cube at least the product of the two sixth-moment Sobolev constants. -/
theorem weighted_variance_interpolation_of_sobolev_moments
    {variance mixedVelocityFour mixedVorticityFour velocitySixth
      vorticitySecond vorticitySixth palinstrophy interpolationConstant
      velocitySobolevConstant vorticitySobolevConstant : ℝ}
    (hmixedVelocity0 : 0 ≤ mixedVelocityFour)
    (hmixedVorticity0 : 0 ≤ mixedVorticityFour)
    (hvelocitySixth0 : 0 ≤ velocitySixth)
    (hvorticitySecond0 : 0 ≤ vorticitySecond)
    (hvorticitySixth0 : 0 ≤ vorticitySixth)
    (hpalinstrophy0 : 0 ≤ palinstrophy)
    (hinterpolationConstant0 : 0 ≤ interpolationConstant)
    (hvelocityConstant0 : 0 ≤ velocitySobolevConstant)
    (hvorticityConstant0 : 0 ≤ vorticitySobolevConstant)
    (hvariance : variance ^ 2 ≤ mixedVelocityFour * vorticitySecond)
    (hmixedVelocity : mixedVelocityFour ^ 2 ≤
      velocitySixth * mixedVorticityFour)
    (hmixedVorticity : mixedVorticityFour ^ 2 ≤
      mixedVelocityFour * vorticitySixth)
    (hvelocitySobolev : velocitySixth ≤
      velocitySobolevConstant * vorticitySecond ^ 3)
    (hvorticitySobolev : vorticitySixth ≤
      vorticitySobolevConstant * palinstrophy ^ 3)
    (hconstants : velocitySobolevConstant ^ 2 * vorticitySobolevConstant ≤
      interpolationConstant ^ 3) :
    variance ^ 2 ≤ interpolationConstant * vorticitySecond ^ 3 * palinstrophy := by
  have hsixth := weighted_variance_sixth_of_sobolev_moments
    hmixedVelocity0 hmixedVorticity0 hvelocitySixth0 hvorticitySecond0
      hvorticitySixth0 hpalinstrophy0 hvelocityConstant0 hvorticityConstant0
      hvariance hmixedVelocity hmixedVorticity hvelocitySobolev hvorticitySobolev
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0)
    (mul_nonneg
      (mul_nonneg hinterpolationConstant0 (pow_nonneg hvorticitySecond0 3))
      hpalinstrophy0)
  calc
    (variance ^ 2) ^ 3 = variance ^ 6 := by ring
    _ ≤ velocitySobolevConstant ^ 2 * vorticitySobolevConstant *
        vorticitySecond ^ 9 * palinstrophy ^ 3 := hsixth
    _ ≤ interpolationConstant ^ 3 * vorticitySecond ^ 9 *
        palinstrophy ^ 3 := by gcongr
    _ = (interpolationConstant * vorticitySecond ^ 3 * palinstrophy) ^ 3 := by
      ring

/-- Exponent chain for the elementary torus estimate of the centered quotient.  Multiplying
`Q ≲ W⁻⁴ᐟ³ Ω⁵ᐟ³` by enstrophy produces the scale-invariant concentration ratio
`(Ω² / W)⁴ᐟ³`. -/
theorem weighted_quotient_concentration_exponent_chain
    (W Ω : ℝ) (hW : 0 < W) (hΩ : 0 < Ω) :
    W ^ (-(4 : ℝ) / 3) * Ω ^ ((5 : ℝ) / 3) * Ω =
      (Ω ^ 2 / W) ^ ((4 : ℝ) / 3) := by
  rw [show -(4 : ℝ) / 3 = -((4 : ℝ) / 3) by ring,
    Real.rpow_neg hW.le]
  conv_lhs => rhs; rw [show Ω = Ω ^ (1 : ℝ) by exact (Real.rpow_one Ω).symm]
  rw [mul_assoc, ← Real.rpow_add hΩ]
  rw [Real.div_rpow (sq_nonneg Ω) hW.le]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hΩ.le]
  norm_num
  ring

/-- Scalar core of the analyticity-volume concentration cap.  If a near-maximum vorticity
core has the critical volume floor `measure² * W³ ≥ c² * ν³`, then its contribution to
enstrophy forces `W / Ω²` to be at most a constant times `ν⁻³`.  The analytic-radius and
core-volume premises themselves remain PDE/geometric obligations. -/
theorem analytic_volume_forces_critical_concentration_cap
    {W Ω measure c θ viscosity : ℝ}
    (hW : 0 ≤ W) (hΩ : 0 ≤ Ω) (hmeasure : 0 ≤ measure)
    (hvolume : c ^ 2 * viscosity ^ 3 ≤ measure ^ 2 * W ^ 3)
    (henstrophy : θ ^ 2 * W ^ 2 * measure ≤ Ω) :
    c ^ 2 * θ ^ 4 * viscosity ^ 3 * W ≤ Ω ^ 2 := by
  have hcore0 : 0 ≤ θ ^ 2 * W ^ 2 * measure := by positivity
  have hsquare : (θ ^ 2 * W ^ 2 * measure) ^ 2 ≤ Ω ^ 2 :=
    (sq_le_sq₀ hcore0 hΩ).2 henstrophy
  calc
    c ^ 2 * θ ^ 4 * viscosity ^ 3 * W =
        θ ^ 4 * W * (c ^ 2 * viscosity ^ 3) := by ring
    _ ≤ θ ^ 4 * W * (measure ^ 2 * W ^ 3) := by
      gcongr
    _ = (θ ^ 2 * W ^ 2 * measure) ^ 2 := by ring
    _ ≤ Ω ^ 2 := hsquare

/-- Scalar Young inequality with the coefficient used to absorb filtered vortex stretching
into one quarter of the viscous palinstrophy. -/
theorem filtered_stretching_young (ν a b : ℝ) (hν : 0 < ν) :
    a * b ≤ ν / 4 * b ^ 2 + a ^ 2 / ν := by
  have hsq : 0 ≤ (ν * b - 2 * a) ^ 2 := sq_nonneg _
  have hνne : ν ≠ 0 := hν.ne'
  field_simp
  nlinarith

/-- If the geometric heat scale `x⁻²ᐟ³` lies below an admissible scale, and that scale lies
below a terminal parabolic cone, then the rate `x` is at least the inverse `3/2` power of the
cone width. -/
theorem geometric_scale_below_cone_forces_rate (x scale allowance : ℝ)
    (hx : 0 < x)
    (hgeometric : x ^ (-(2 : ℝ) / 3) ≤ scale)
    (hcone : scale ≤ allowance) :
    allowance ^ (-(3 : ℝ) / 2) ≤ x := by
  have hxs : 0 < x ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hx _
  have hbase : x ^ (-(2 : ℝ) / 3) ≤ allowance := hgeometric.trans hcone
  have hpow := Real.rpow_le_rpow_of_nonpos hxs hbase
    (by norm_num : (-(3 : ℝ) / 2) ≤ 0)
  calc
    allowance ^ (-(3 : ℝ) / 2) ≤
        (x ^ (-(2 : ℝ) / 3)) ^ (-(3 : ℝ) / 2) := hpow
    _ = x := by
      rw [← Real.rpow_mul hx.le]
      norm_num

/-- Specialization of `geometric_scale_below_cone_forces_rate` to a parabolic cone `a * τ`.
It exposes the nonintegrable `τ⁻³ᐟ²` lower rate forced by a viscosity-safe terminal schedule. -/
theorem parabolic_safe_scale_forces_inverse_three_halves (x scale a τ : ℝ)
    (hx : 0 < x) (ha : 0 < a) (hτ : 0 < τ)
    (hgeometric : x ^ (-(2 : ℝ) / 3) ≤ scale)
    (hcone : scale ≤ a * τ) :
    a ^ (-(3 : ℝ) / 2) * τ ^ (-(3 : ℝ) / 2) ≤ x := by
  have h := geometric_scale_below_cone_forces_rate x scale (a * τ) hx
    hgeometric hcone
  rwa [Real.mul_rpow ha.le hτ.le] at h

/-- The inverse `3/2` power is not integrable at the terminal time. -/
theorem inverse_three_halves_not_integrable_near_zero :
    ¬ IntegrableOn (fun τ : ℝ => τ ^ (-(3 : ℝ) / 2)) (Ioo 0 1) := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  norm_num

/-- Any rate which dominates a positive multiple of `τ⁻³ᐟ²` almost everywhere near zero is
not integrable there. -/
theorem not_integrable_of_const_mul_inverse_three_halves_le
    (c : ℝ) (hc : 0 < c) (rate : ℝ → ℝ)
    (hrate : ∀ᵐ τ ∂volume.restrict (Ioo (0 : ℝ) 1),
      c * τ ^ (-(3 : ℝ) / 2) ≤ rate τ) :
    ¬ IntegrableOn rate (Ioo 0 1) := by
  intro hint
  have hcont : ContinuousOn (fun τ : ℝ => c * τ ^ (-(3 : ℝ) / 2)) (Ioo 0 1) := by
    intro τ hτ
    exact continuousWithinAt_const.mul
      (Real.continuousAt_rpow_const τ _ (Or.inl hτ.1.ne')).continuousWithinAt
  have hscaled : IntegrableOn (fun τ : ℝ => c * τ ^ (-(3 : ℝ) / 2)) (Ioo 0 1) := by
    apply hint.mono' (hcont.aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hrate] with τ hτ hle
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hc (Real.rpow_pos_of_pos hτ.1 _))]
    exact hle
  apply inverse_three_halves_not_integrable_near_zero
  exact ((integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc.ne') _).mp hscaled)

/-- Cone-form schedule obstruction.  On almost every remaining time `τ ∈ (0,1)`, suppose a
scale stays above the energy-paid geometric scale `x⁻²ᐟ³` but below a terminal cone `aτ`.
Then `x` cannot have a finite time integral.  In the Navier--Stokes application
`x = 1 + Ω(T - τ)` and `a` is the retained parabolic scale speed. -/
theorem safe_scale_cone_not_integrable
    (x scale : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hx : ∀ᵐ τ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < x τ)
    (hgeometric : ∀ᵐ τ ∂volume.restrict (Ioo (0 : ℝ) 1),
      x τ ^ (-(2 : ℝ) / 3) ≤ scale τ)
    (hcone : ∀ᵐ τ ∂volume.restrict (Ioo (0 : ℝ) 1),
      scale τ ≤ a * τ) :
    ¬ IntegrableOn x (Ioo 0 1) := by
  apply not_integrable_of_const_mul_inverse_three_halves_le
    (a ^ (-(3 : ℝ) / 2)) (Real.rpow_pos_of_pos ha _) x
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hx, hgeometric, hcone]
    with τ hτ hxτ hgeoτ hconeτ
  exact parabolic_safe_scale_forces_inverse_three_halves
    (x τ) (scale τ) a τ hxτ ha hτ.1 hgeoτ hconeτ

/-- A continuous remaining-time scale which starts at zero and has derivative at most `a`
lies below the terminal parabolic cone `aτ`.  This is the calculus step converting the
viscosity-speed condition into the cone hypothesis above. -/
theorem terminal_cone_of_deriv_le
    (scale speed : ℝ → ℝ) (a : ℝ)
    (hcont : ContinuousOn scale (Icc 0 1))
    (hderiv : ∀ τ ∈ Ioo (0 : ℝ) 1, HasDerivAt scale (speed τ) τ)
    (hspeed : ∀ τ ∈ Ioo (0 : ℝ) 1, speed τ ≤ a)
    (hterminal : scale 0 = 0) :
    ∀ τ ∈ Icc (0 : ℝ) 1, scale τ ≤ a * τ := by
  let f : ℝ → ℝ := scale - fun τ => a * τ
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 1) := by
    exact hcont.sub (continuous_const.mul continuous_id).continuousOn
  have hfderiv : ∀ τ ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt f (speed τ - a) (Ioo 0 1) τ := by
    intro τ hτ
    dsimp [f]
    simpa only [id_eq, mul_one] using
      ((hderiv τ hτ).sub ((hasDerivAt_id τ).const_mul a)).hasDerivWithinAt
  have hanti : AntitoneOn f (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun τ => speed τ - a)
      (convex_Icc 0 1) hfcont
    · simpa only [interior_Icc] using hfderiv
    · intro τ hτ
      rw [interior_Icc] at hτ
      linarith [hspeed τ hτ]
  intro τ hτ
  have hzero_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hf_le := hanti hzero_mem hτ hτ.1
  dsimp [f] at hf_le
  rw [hterminal] at hf_le
  linarith

/-- End-to-end viscosity-safe schedule obstruction.  A terminal scale with derivative at most
`a` in remaining-time coordinates lies below `aτ`; if it also stays above the geometric scale
`x⁻²ᐟ³`, then the rate `x` is not time-integrable. -/
theorem safe_scale_schedule_not_integrable
    (x scale speed : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn scale (Icc 0 1))
    (hderiv : ∀ τ ∈ Ioo (0 : ℝ) 1, HasDerivAt scale (speed τ) τ)
    (hspeed : ∀ τ ∈ Ioo (0 : ℝ) 1, speed τ ≤ a)
    (hterminal : scale 0 = 0)
    (hx : ∀ᵐ τ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < x τ)
    (hgeometric : ∀ᵐ τ ∂volume.restrict (Ioo (0 : ℝ) 1),
      x τ ^ (-(2 : ℝ) / 3) ≤ scale τ) :
    ¬ IntegrableOn x (Ioo 0 1) := by
  apply safe_scale_cone_not_integrable x scale a ha hx hgeometric
  have hterminalCone :=
    terminal_cone_of_deriv_le scale speed a hcont hderiv hspeed hterminal
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
  exact hterminalCone τ ⟨hτ.1.le, hτ.2.le⟩

/-- Exact value of the elementary regularization tradeoff at its stationary scale. -/
theorem regularization_balance_at_stationary_scale
    (A D c : ℝ) (hc : c ≠ 0) (hD : D = 2 * A * c ^ 6) :
    A * c ^ 4 + D / c ^ 2 = 3 * A * c ^ 4 := by
  rw [hD]
  field_simp [hc]
  ring

/-- The stationary scale globally minimizes `A x⁴ + D/x²`.  Thus the crude fallback
`Q_c ≤ c⁻² B` inevitably produces the two-thirds interpolation exponent; optimizing the
regularization parameter alone cannot improve it. -/
theorem regularization_balance_minimum
    (A D c x : ℝ) (hA : 0 ≤ A) (hx : x ≠ 0)
    (hD : D = 2 * A * c ^ 6) :
    3 * A * c ^ 4 ≤ A * x ^ 4 + D / x ^ 2 := by
  rw [hD]
  rw [← sub_le_iff_le_add']
  rw [le_div_iff₀ (sq_pos_of_ne_zero hx)]
  have hfactor : 0 ≤ A * (x ^ 2 - c ^ 2) ^ 2 * (x ^ 2 + 2 * c ^ 2) := by
    positivity
  nlinarith

/-- Exponent audit for the crude regularized quotient route.  The standard estimate
`B ≲ Ω³ᴵ² P¹ᴵ²`, followed by optimization of `c⁴ + P B/c²`, returns exactly
`Ω P`; it does not improve the classical enstrophy--palinstrophy scaling. -/
theorem crude_regularized_interpolation_exponent_chain
    (Ω P : ℝ) (hΩ : 0 < Ω) (hP : 0 < P) :
    (Ω ^ ((3 : ℝ) / 2) * P ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) =
      Ω * P := by
  rw [Real.mul_rpow (Real.rpow_nonneg hΩ.le _) (Real.rpow_nonneg hP.le _)]
  rw [← Real.rpow_mul hΩ.le, ← Real.rpow_mul hP.le]
  norm_num

/-- Exact weighted centering identity for one velocity component.  In the regularized quotient,
the weight is `|∇u|²/(|ω|²+c²)`, so the best Galilean frame is its weighted velocity mean. -/
theorem weighted_centering_identity
    (raw moment mass frame : ℝ) (hmass : mass ≠ 0) :
    raw - 2 * frame * moment + frame ^ 2 * mass =
      raw - moment ^ 2 / mass + mass * (frame - moment / mass) ^ 2 := by
  field_simp [hmass]
  ring

/-- The weighted mean globally minimizes the centered quadratic charge. -/
theorem weighted_centering_minimum
    (raw moment mass frame : ℝ) (hmass : 0 < mass) :
    raw - moment ^ 2 / mass ≤
      raw - 2 * frame * moment + frame ^ 2 * mass := by
  rw [weighted_centering_identity raw moment mass frame hmass.ne']
  exact le_add_of_nonneg_right (mul_nonneg hmass.le (sq_nonneg _))

/-!
Queued for the analysis-phase batch (each sympy-certified today): W7's Duhamel integral
∫₀^∞ e^{−as} = 1/a; the Gram integral ⟨r, W′⟩ = −2 (results/sympy_w4.log + the banked
m1_impulse instrument); the W1/W8 tail integrals; W16's beta integral = π; the ℂ²-skew lemma;
W9's measure-theoretic Chebyshev (Mathlib's mul_meas_ge_le_integral_of_nonneg wraps it).
No sorries are committed to this project.
-/
