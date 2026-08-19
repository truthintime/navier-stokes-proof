import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Energy-paid dynamic continuation inequality

This file formalizes the real-variable endgame of the quotient-weighted
enstrophy criterion.  The logarithmic derivative is essential: from

`E' ≤ C Θ² E³` and `Θ² E ≤ M`

one obtains `(log E)' ≤ C M E`.  Thus an independent `L¹` budget for `E`
gives a uniform exponential bound.  We do not incorrectly replace the cubic
inequality by a linear differential inequality for `E` itself.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section

/-- Logarithmic Gronwall estimate paid by an `L¹` budget. -/
theorem positive_rate_le_square_of_integral_budget
    {E E' : ℝ → ℝ} {a t C M B : ℝ}
    (hat : a ≤ t) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hEpos : ∀ x ∈ Icc a t, 0 < E x)
    (hEcont : ContinuousOn E (Icc a t))
    (hEderiv : ∀ x ∈ Ioo a t, HasDerivAt E (E' x) x)
    (hrate : ∀ x ∈ Ioo a t, E' x ≤ C * M * E x ^ 2)
    (hEint : IntegrableOn E (Icc a t))
    (hbudget : (∫ x in a..t, E x) ≤ B) :
    E t ≤ E a * Real.exp (C * M * B) := by
  have hlogCont : ContinuousOn (fun x => Real.log (E x)) (Icc a t) :=
    hEcont.log (fun x hx => (hEpos x hx).ne')
  have hlogDeriv : ∀ x ∈ Ioo a t,
      HasDerivWithinAt (fun y => Real.log (E y)) (E' x / E x) (Ioi x) x := by
    intro x hx
    exact ((hEderiv x hx).log
      ((hEpos x ⟨hx.1.le, hx.2.le⟩).ne')).hasDerivWithinAt
  have hphiInt : IntegrableOn (fun x => C * M * E x) (Icc a t) :=
    hEint.const_mul (C * M)
  have hlogRate : ∀ x ∈ Ioo a t, E' x / E x ≤ C * M * E x := by
    intro x hx
    apply (div_le_iff₀ (hEpos x ⟨hx.1.le, hx.2.le⟩)).2
    have h := hrate x hx
    nlinarith
  have hlogIntegral := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    hat hlogCont hlogDeriv hphiInt hlogRate
  rw [intervalIntegral.integral_const_mul] at hlogIntegral
  have hCM : 0 ≤ C * M := mul_nonneg hC hM
  have hlogBound :
      Real.log (E t) - Real.log (E a) ≤ C * M * B :=
    hlogIntegral.trans (mul_le_mul_of_nonneg_left hbudget hCM)
  have hexp := Real.exp_le_exp.mpr (sub_le_iff_le_add.mp hlogBound)
  rw [Real.exp_add, Real.exp_log (hEpos t (right_mem_Icc.mpr hat)),
    Real.exp_log (hEpos a (left_mem_Icc.mpr hat))] at hexp
  simpa [mul_comm] using hexp

/-- Dynamic quotient criterion in the form produced by the sharp
`P³ᴵ⁴` Young inequality.  A bounded scale-invariant product `Θ² E`,
together with the energy-paid time integral of `E`, rules out finite-time
growth on the interval. -/
theorem quotient_cubic_rate_bounded_of_energy_budget
    {E E' Θ : ℝ → ℝ} {a t C M B : ℝ}
    (hat : a ≤ t) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hEpos : ∀ x ∈ Icc a t, 0 < E x)
    (hEcont : ContinuousOn E (Icc a t))
    (hEderiv : ∀ x ∈ Ioo a t, HasDerivAt E (E' x) x)
    (hcubic : ∀ x ∈ Ioo a t,
      E' x ≤ C * Θ x ^ 2 * E x ^ 3)
    (hcritical : ∀ x ∈ Ioo a t, Θ x ^ 2 * E x ≤ M)
    (hEint : IntegrableOn E (Icc a t))
    (hbudget : (∫ x in a..t, E x) ≤ B) :
    E t ≤ E a * Real.exp (C * M * B) := by
  apply positive_rate_le_square_of_integral_budget
    hat hC hM hEpos hEcont hEderiv ?_ hEint hbudget
  intro x hx
  calc
    E' x ≤ C * Θ x ^ 2 * E x ^ 3 := hcubic x hx
    _ = C * (Θ x ^ 2 * E x) * E x ^ 2 := by ring
    _ ≤ C * M * E x ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcritical x hx) hC)
        (sq_nonneg (E x))

/-- The criterion has elementary nonzero witnesses: constant positive
enstrophy with zero quotient satisfies every differential premise. -/
theorem constant_positive_witnesses_quotient_cubic_rate
    {a t E₀ : ℝ} (_hat : a ≤ t) (_hE₀ : 0 < E₀) :
    ∀ x ∈ Ioo a t,
      deriv (fun _ : ℝ => E₀) x ≤
        (1 : ℝ) * (0 : ℝ) ^ 2 * E₀ ^ 3 := by
  intro x _hx
  simp

/-! ## Signed production correlation -/

/-- Zero-safe normalized positive-production correlation.  It records signed
cancellation lost by the absolute quotient/variance Cauchy ledger. -/
def positiveProductionCorrelation (production quotient variance : ℝ) : ℝ :=
  if quotient * variance = 0 then 0
  else (max production 0) ^ 2 / (quotient * variance)

/-- The zero-safe correlation is nonnegative. -/
theorem positiveProductionCorrelation_nonneg
    (production quotient variance : ℝ)
    (hquotient : 0 ≤ quotient) (hvariance : 0 ≤ variance) :
    0 ≤ positiveProductionCorrelation production quotient variance := by
  rw [positiveProductionCorrelation]
  split_ifs with hzero
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _) (mul_nonneg hquotient hvariance)

/-- Cauchy's production bound places the normalized correlation in `[0,1]`. -/
theorem positiveProductionCorrelation_le_one
    {production quotient variance : ℝ}
    (hquotient : 0 ≤ quotient) (hvariance : 0 ≤ variance)
    (hproduction : production ^ 2 ≤ quotient * variance) :
    positiveProductionCorrelation production quotient variance ≤ 1 := by
  rw [positiveProductionCorrelation]
  split_ifs with hzero
  · norm_num
  · have hden : 0 < quotient * variance :=
      lt_of_le_of_ne (mul_nonneg hquotient hvariance) (Ne.symm hzero)
    apply (div_le_iff₀ hden).2
    have hpositiveSq : (max production 0) ^ 2 ≤ production ^ 2 := by
      by_cases hp : 0 ≤ production
      · rw [max_eq_left hp]
      · rw [max_eq_right (le_of_not_ge hp)]
        simpa using sq_nonneg production
    exact hpositiveSq.trans (by simpa using hproduction)

/-- The correlation exactly recovers the squared positive production, including
the zero-denominator case forced by the Cauchy bound. -/
theorem positiveProductionCorrelation_mul_eq_positivePart_sq
    {production quotient variance : ℝ}
    (hproduction : production ^ 2 ≤ quotient * variance) :
    positiveProductionCorrelation production quotient variance *
        (quotient * variance) = (max production 0) ^ 2 := by
  rw [positiveProductionCorrelation]
  split_ifs with hzero
  · rw [zero_mul]
    have hpSq : production ^ 2 = 0 := by
      apply le_antisymm
      · simpa [hzero] using hproduction
      · exact sq_nonneg production
    have hp : production = 0 := sq_eq_zero_iff.mp hpSq
    simp [hp]
  · exact div_mul_cancel₀ _ hzero

/-- Exact rigidity identity behind integral Cauchy--Schwarz.  The Cauchy defect is the
squared distance of `g` from the one-dimensional span of `f`, multiplied by `‖f‖₂²`.
This is the quantitative starting point for studying near-saturation of the signed
vortex-stretching factorization. -/
theorem integral_cauchy_defect_eq_scaled_projection_residual
    {α E : Type*} [MeasureSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : α → E)
    (hfSq : Integrable (fun x => ‖f x‖ ^ 2))
    (hgSq : Integrable (fun x => ‖g x‖ ^ 2))
    (hfg : Integrable (fun x => inner ℝ (f x) (g x)))
    (hQ : (∫ x, ‖f x‖ ^ 2) ≠ 0) :
    (∫ x, ‖f x‖ ^ 2) *
        (∫ x, ‖g x -
          (((∫ y, inner ℝ (f y) (g y)) / (∫ y, ‖f y‖ ^ 2)) • f x)‖ ^ 2) =
      (∫ x, ‖f x‖ ^ 2) * (∫ x, ‖g x‖ ^ 2) -
        (∫ x, inner ℝ (f x) (g x)) ^ 2 := by
  let Q : ℝ := ∫ x, ‖f x‖ ^ 2
  let N : ℝ := ∫ x, inner ℝ (f x) (g x)
  let c : ℝ := N / Q
  have hpoint : ∀ x,
      ‖g x - c • f x‖ ^ 2 =
        ‖g x‖ ^ 2 - 2 * c * inner ℝ (f x) (g x) +
          c ^ 2 * ‖f x‖ ^ 2 := by
    intro x
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm (g x) (f x)]
    ring
  have hmiddle : Integrable (fun x =>
      2 * c * inner ℝ (f x) (g x)) := hfg.const_mul (2 * c)
  have hlast : Integrable (fun x => c ^ 2 * ‖f x‖ ^ 2) :=
    hfSq.const_mul (c ^ 2)
  have hintegral :
      (∫ x, ‖g x - c • f x‖ ^ 2) =
        (∫ x, ‖g x‖ ^ 2) - 2 * c * N + c ^ 2 * Q := by
    calc
      (∫ x, ‖g x - c • f x‖ ^ 2) =
          ∫ x, (‖g x‖ ^ 2 - 2 * c * inner ℝ (f x) (g x)) +
            c ^ 2 * ‖f x‖ ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = (∫ x, ‖g x‖ ^ 2 - 2 * c * inner ℝ (f x) (g x)) +
          ∫ x, c ^ 2 * ‖f x‖ ^ 2 :=
        integral_add (hgSq.sub hmiddle) hlast
      _ = ((∫ x, ‖g x‖ ^ 2) -
          ∫ x, 2 * c * inner ℝ (f x) (g x)) +
          ∫ x, c ^ 2 * ‖f x‖ ^ 2 := by
        rw [integral_sub hgSq hmiddle]
      _ = (∫ x, ‖g x‖ ^ 2) - 2 * c * N + c ^ 2 * Q := by
        rw [integral_const_mul, integral_const_mul]
  change Q * (∫ x, ‖g x - c • f x‖ ^ 2) =
    Q * (∫ x, ‖g x‖ ^ 2) - N ^ 2
  rw [hintegral]
  dsimp [c]
  field_simp [show Q ≠ 0 by simpa [Q] using hQ]
  <;> ring

/-- Exact signed cancellation: zero total production has zero correlation even
when the absolute quotient and variance are positive. -/
@[simp]
theorem positiveProductionCorrelation_zero_production
    (quotient variance : ℝ) :
    positiveProductionCorrelation 0 quotient variance = 0 := by
  simp [positiveProductionCorrelation]

/-- Positive amplitude rescaling leaves the normalized correlation invariant:
`N`, `G`, and `V` scale like `A³`, `A²`, and `A⁴`.  Thus correlation only
helps the critical criterion when it is dynamically depleted; its definition
alone does not remove the amplitude obstruction. -/
theorem positiveProductionCorrelation_amplitude_invariant
    (A production quotient variance : ℝ) (hA : 0 < A) :
    positiveProductionCorrelation (A ^ 3 * production)
        (A ^ 2 * quotient) (A ^ 4 * variance) =
      positiveProductionCorrelation production quotient variance := by
  have hA2 : A ^ 2 ≠ 0 := pow_ne_zero _ hA.ne'
  have hA3 : A ^ 3 ≠ 0 := pow_ne_zero _ hA.ne'
  have hA4 : A ^ 4 ≠ 0 := pow_ne_zero _ hA.ne'
  have hmax : max (A ^ 3 * production) 0 = A ^ 3 * max production 0 := by
    by_cases hp : 0 ≤ production
    · rw [max_eq_left hp, max_eq_left]
      exact mul_nonneg (pow_nonneg hA.le _) hp
    · have hp' : production ≤ 0 := le_of_not_ge hp
      rw [max_eq_right hp', max_eq_right]
      · ring
      · exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hA.le _) hp'
  rw [positiveProductionCorrelation, positiveProductionCorrelation]
  by_cases hbase : quotient * variance = 0
  · have hscaled : (A ^ 2 * quotient) * (A ^ 4 * variance) = 0 := by
      rw [show (A ^ 2 * quotient) * (A ^ 4 * variance) =
        A ^ 6 * (quotient * variance) by ring, hbase, mul_zero]
    rw [if_pos hscaled, if_pos hbase]
  · have hscaled : (A ^ 2 * quotient) * (A ^ 4 * variance) ≠ 0 := by
      intro hzero
      apply hbase
      have : A ^ 6 * (quotient * variance) = 0 := by
        calc
          A ^ 6 * (quotient * variance) =
              (A ^ 2 * quotient) * (A ^ 4 * variance) := by ring
          _ = 0 := hzero
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hA.ne')
    rw [if_neg hscaled, if_neg hbase, hmax]
    field_simp [hA2, hA3, hA4, hA.ne']

/-- A common positive scaling of production, quotient, and variance also leaves the
correlation invariant.  This is the scaling pattern generated by Navier--Stokes spatial
concentration, where all three integrated quantities scale like `λ³`. -/
theorem positiveProductionCorrelation_common_scale_invariant
    (scale production quotient variance : ℝ) (hscale : 0 < scale) :
    positiveProductionCorrelation (scale * production)
        (scale * quotient) (scale * variance) =
      positiveProductionCorrelation production quotient variance := by
  have hscale0 : scale ≠ 0 := hscale.ne'
  have hmax : max (scale * production) 0 = scale * max production 0 := by
    by_cases hp : 0 ≤ production
    · rw [max_eq_left hp, max_eq_left]
      exact mul_nonneg hscale.le hp
    · have hp' : production ≤ 0 := le_of_not_ge hp
      rw [max_eq_right hp', max_eq_right]
      · ring
      · exact mul_nonpos_of_nonneg_of_nonpos hscale.le hp'
  rw [positiveProductionCorrelation, positiveProductionCorrelation]
  by_cases hbase : quotient * variance = 0
  · have hscaled : (scale * quotient) * (scale * variance) = 0 := by
      rw [show (scale * quotient) * (scale * variance) =
        scale ^ 2 * (quotient * variance) by ring, hbase, mul_zero]
    rw [if_pos hscaled, if_pos hbase]
  · have hscaled : (scale * quotient) * (scale * variance) ≠ 0 := by
      intro hzero
      apply hbase
      have : scale ^ 2 * (quotient * variance) = 0 := by
        calc
          scale ^ 2 * (quotient * variance) =
              (scale * quotient) * (scale * variance) := by ring
          _ = 0 := hzero
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hscale0)
    rw [if_neg hscaled, if_neg hbase, hmax]
    field_simp [hscale0]

/-- Zero-safe fraction of palinstrophy occupied by the self-transport quotient. -/
def quotientPalinstrophyFraction (quotient palinstrophy : ℝ) : ℝ :=
  if palinstrophy = 0 then 0 else quotient / palinstrophy

theorem quotientPalinstrophyFraction_nonneg
    (quotient palinstrophy : ℝ) (hquotient : 0 ≤ quotient)
    (hpalinstrophy : 0 ≤ palinstrophy) :
    0 ≤ quotientPalinstrophyFraction quotient palinstrophy := by
  rw [quotientPalinstrophyFraction]
  split_ifs with hzero
  · exact le_rfl
  · exact div_nonneg hquotient hpalinstrophy

theorem quotientPalinstrophyFraction_le_one
    (quotient palinstrophy : ℝ) (hpalinstrophy : 0 ≤ palinstrophy)
    (hquotient : quotient ≤ palinstrophy) :
    quotientPalinstrophyFraction quotient palinstrophy ≤ 1 := by
  rw [quotientPalinstrophyFraction]
  split_ifs with hzero
  · norm_num
  · exact (div_le_one (lt_of_le_of_ne hpalinstrophy (Ne.symm hzero))).2 hquotient

/-- Under the natural nonnegativity and domination hypotheses, the zero-safe fraction exactly
reconstructs the quotient even in the zero-palinstrophy case. -/
theorem quotientPalinstrophyFraction_mul_eq_quotient
    (quotient palinstrophy : ℝ)
    (hquotient0 : 0 ≤ quotient)
    (hquotient : quotient ≤ palinstrophy) :
    quotientPalinstrophyFraction quotient palinstrophy * palinstrophy = quotient := by
  rw [quotientPalinstrophyFraction]
  split_ifs with hzero
  · rw [zero_mul]
    linarith
  · exact div_mul_cancel₀ quotient hzero

/-- The quotient fraction is invariant when quotient and palinstrophy have the same
positive scaling. -/
theorem quotientPalinstrophyFraction_common_scale_invariant
    (scale quotient palinstrophy : ℝ) (hscale : 0 < scale) :
    quotientPalinstrophyFraction (scale * quotient) (scale * palinstrophy) =
      quotientPalinstrophyFraction quotient palinstrophy := by
  rw [quotientPalinstrophyFraction, quotientPalinstrophyFraction]
  by_cases hpalinstrophy : palinstrophy = 0
  · have hscaled : scale * palinstrophy = 0 := by rw [hpalinstrophy, mul_zero]
    rw [if_pos hscaled, if_pos hpalinstrophy]
  · have hscaled : scale * palinstrophy ≠ 0 :=
      mul_ne_zero hscale.ne' hpalinstrophy
    rw [if_neg hscaled, if_neg hpalinstrophy]
    field_simp [hscale.ne', hpalinstrophy]

/-- Scale-critical coefficient in the correlation-refined continuation criterion. -/
def correlatedCriticalDepletionFactor
    (production quotient variance palinstrophy enstrophy : ℝ) : ℝ :=
  positiveProductionCorrelation production quotient variance ^ 2 *
    quotientPalinstrophyFraction quotient palinstrophy ^ 2 * enstrophy

/-- Once the signed correlation and quotient fraction are multiplied, the auxiliary
self-transport quotient cancels exactly.  This zero-safe polynomial identity shows that
the correlated critical obstruction is intrinsically a ratio of positive stretching to
palinstrophy times weighted velocity variance. -/
theorem correlatedCriticalDepletionFactor_mul_palinstrophyVariance_sq
    {production quotient variance palinstrophy enstrophy : ℝ}
    (hproduction : production ^ 2 ≤ quotient * variance)
    (hquotient0 : 0 ≤ quotient) (hquotient : quotient ≤ palinstrophy) :
    correlatedCriticalDepletionFactor production quotient variance
        palinstrophy enstrophy * (palinstrophy * variance) ^ 2 =
      (max production 0) ^ 4 * enstrophy := by
  have hcorrelation := positiveProductionCorrelation_mul_eq_positivePart_sq
    hproduction
  have hfraction := quotientPalinstrophyFraction_mul_eq_quotient
    quotient palinstrophy hquotient0 hquotient
  unfold correlatedCriticalDepletionFactor
  calc
    positiveProductionCorrelation production quotient variance ^ 2 *
          quotientPalinstrophyFraction quotient palinstrophy ^ 2 * enstrophy *
          (palinstrophy * variance) ^ 2 =
        (positiveProductionCorrelation production quotient variance *
            (quotientPalinstrophyFraction quotient palinstrophy * palinstrophy) *
            variance) ^ 2 * enstrophy := by ring
    _ = (positiveProductionCorrelation production quotient variance *
          (quotient * variance)) ^ 2 * enstrophy := by rw [hfraction]; ring
    _ = ((max production 0) ^ 2) ^ 2 * enstrophy := by rw [hcorrelation]
    _ = (max production 0) ^ 4 * enstrophy := by ring

/-- Quotient-free form of the signed scale-critical obstruction.  Division in `ℝ` is
zero-safe, and the Cauchy/domination hypotheses force both sides to vanish when the
denominator is zero. -/
theorem correlatedCriticalDepletionFactor_eq_positiveProduction_ratio
    {production quotient variance palinstrophy enstrophy : ℝ}
    (hproduction : production ^ 2 ≤ quotient * variance)
    (hquotient0 : 0 ≤ quotient) (hquotient : quotient ≤ palinstrophy) :
    correlatedCriticalDepletionFactor production quotient variance
        palinstrophy enstrophy =
      (max production 0) ^ 4 * enstrophy /
        (palinstrophy * variance) ^ 2 := by
  by_cases hden : palinstrophy * variance = 0
  · rcases mul_eq_zero.mp hden with hp | hv
    · have hq : quotient = 0 := by
        apply le_antisymm
        · simpa [hp] using hquotient
        · exact hquotient0
      simp [correlatedCriticalDepletionFactor, positiveProductionCorrelation,
        quotientPalinstrophyFraction, hp, hq]
    · simp [correlatedCriticalDepletionFactor, positiveProductionCorrelation, hv]
  · apply (eq_div_iff (pow_ne_zero 2 hden)).2
    exact correlatedCriticalDepletionFactor_mul_palinstrophyVariance_sq
      hproduction hquotient0 hquotient

/-- Under Navier--Stokes concentration scaling, `N,Q,V,P` all acquire `λ³` while
enstrophy acquires `λ`.  Both normalized geometric factors are invariant, so their
critical product with enstrophy grows exactly like `λ`.  Normalization alone therefore
cannot exclude a concentrating profile. -/
theorem correlatedCriticalDepletionFactor_concentration_scaling
    (scaleParameter production quotient variance palinstrophy enstrophy : ℝ)
    (hscaleParameter : 0 < scaleParameter) :
    correlatedCriticalDepletionFactor
        (scaleParameter ^ 3 * production) (scaleParameter ^ 3 * quotient)
        (scaleParameter ^ 3 * variance) (scaleParameter ^ 3 * palinstrophy)
        (scaleParameter * enstrophy) =
      scaleParameter * correlatedCriticalDepletionFactor
        production quotient variance palinstrophy enstrophy := by
  rw [correlatedCriticalDepletionFactor, correlatedCriticalDepletionFactor]
  rw [positiveProductionCorrelation_common_scale_invariant
    (scaleParameter ^ 3) production quotient variance
      (pow_pos hscaleParameter 3)]
  rw [quotientPalinstrophyFraction_common_scale_invariant
    (scaleParameter ^ 3) quotient palinstrophy (pow_pos hscaleParameter 3)]
  ring

/-- The first-integral-weighted helicity defect gap has exactly the critical
Navier--Stokes concentration scaling.  Quotient and defect scale as `λ³` and
`λ⁶`, while a tube-scale weight has `L²` mass `λ⁻³` and its weighted helicity
is invariant; both sides therefore acquire the same factor `λ³`. -/
theorem firstIntegralWeightedDefectGap_concentration_invariant
    (scaleParameter quotient weightedHelicity weightMass defect : ℝ)
    (hscaleParameter : 0 < scaleParameter) :
    ((scaleParameter ^ 3 * quotient) * weightedHelicity ^ 2 ≤
        (weightMass / scaleParameter ^ 3) *
          (scaleParameter ^ 6 * defect)) ↔
      quotient * weightedHelicity ^ 2 ≤ weightMass * defect := by
  have hscaleCube : scaleParameter ^ 3 ≠ 0 :=
    pow_ne_zero 3 hscaleParameter.ne'
  have hleft :
      (scaleParameter ^ 3 * quotient) * weightedHelicity ^ 2 =
        scaleParameter ^ 3 * (quotient * weightedHelicity ^ 2) := by
    ring
  have hright :
      (weightMass / scaleParameter ^ 3) *
          (scaleParameter ^ 6 * defect) =
        scaleParameter ^ 3 * (weightMass * defect) := by
    field_simp [hscaleCube]
  rw [hleft, hright]
  exact mul_le_mul_iff_of_pos_left (pow_pos hscaleParameter 3)

/-- A localized-helicity defect gap gives an explicit upper bound on the
normalized Cauchy saturation ratio.  The dimensionless loss is exactly
`weightedHelicity² / (weightMass * variance)`. -/
theorem normalizedProductionRatio_le_one_sub_localizedHelicityRatio
    {production quotient variance weightMass weightedHelicity : ℝ}
    (hquotient : 0 < quotient) (hvariance : 0 < variance)
    (hweightMass : 0 < weightMass)
    (hgap : quotient * weightedHelicity ^ 2 ≤
      weightMass * (quotient * variance - production ^ 2)) :
    production ^ 2 / (quotient * variance) ≤
      1 - weightedHelicity ^ 2 / (weightMass * variance) := by
  have hquotientVariance : 0 < quotient * variance :=
    mul_pos hquotient hvariance
  have hpaid : quotient * weightedHelicity ^ 2 / weightMass ≤
      quotient * variance - production ^ 2 := by
    apply (div_le_iff₀ hweightMass).2
    nlinarith
  apply (div_le_iff₀ hquotientVariance).2
  calc
    production ^ 2 ≤
        quotient * variance - quotient * weightedHelicity ^ 2 / weightMass := by
      linarith
    _ = (1 - weightedHelicity ^ 2 / (weightMass * variance)) *
        (quotient * variance) := by
      field_simp [hweightMass.ne', hvariance.ne']

/-- The preceding bound also controls the zero-safe positive-production
correlation.  Negative production only makes this correlation vanish, so no
sign assumption on `production` is needed. -/
theorem positiveProductionCorrelation_le_one_sub_localizedHelicityRatio
    {production quotient variance weightMass weightedHelicity : ℝ}
    (hquotient : 0 < quotient) (hvariance : 0 < variance)
    (hweightMass : 0 < weightMass)
    (hgap : quotient * weightedHelicity ^ 2 ≤
      weightMass * (quotient * variance - production ^ 2)) :
    positiveProductionCorrelation production quotient variance ≤
      1 - weightedHelicity ^ 2 / (weightMass * variance) := by
  rw [positiveProductionCorrelation,
    if_neg (mul_pos hquotient hvariance).ne']
  have hpositiveSq : (max production 0) ^ 2 ≤ production ^ 2 := by
    by_cases hproduction : 0 ≤ production
    · rw [max_eq_left hproduction]
    · rw [max_eq_right (le_of_not_ge hproduction)]
      simpa using sq_nonneg production
  have hnormalized :=
    normalizedProductionRatio_le_one_sub_localizedHelicityRatio
      hquotient hvariance hweightMass hgap
  exact ((div_le_div_iff_of_pos_right
    (mul_pos hquotient hvariance)).2 hpositiveSq).trans hnormalized

/-- A localized-helicity defect gap bounds the complete correlated critical
factor.  This is the pointwise algebraic handoff from geometry to the dynamic
continuation criterion. -/
theorem correlatedCriticalFactor_le_localizedHelicityFactor
    {production quotient variance weightMass weightedHelicity
      quotientFraction enstrophy : ℝ}
    (hquotient : 0 < quotient) (hvariance : 0 < variance)
    (hweightMass : 0 < weightMass)
    (hquotientFraction : 0 ≤ quotientFraction)
    (henstrophy : 0 ≤ enstrophy)
    (hgap : quotient * weightedHelicity ^ 2 ≤
      weightMass * (quotient * variance - production ^ 2)) :
    (positiveProductionCorrelation production quotient variance *
        quotientFraction) ^ 2 * enstrophy ≤
      ((1 - weightedHelicity ^ 2 / (weightMass * variance)) *
        quotientFraction) ^ 2 * enstrophy := by
  have hcorrelationNonneg := positiveProductionCorrelation_nonneg
    production quotient variance hquotient.le hvariance.le
  have hcorrelationBound :=
    positiveProductionCorrelation_le_one_sub_localizedHelicityRatio
      hquotient hvariance hweightMass hgap
  have hlocalizedNonneg :
      0 ≤ 1 - weightedHelicity ^ 2 / (weightMass * variance) :=
    hcorrelationNonneg.trans hcorrelationBound
  have hproduct :
      positiveProductionCorrelation production quotient variance *
          quotientFraction ≤
        (1 - weightedHelicity ^ 2 / (weightMass * variance)) *
          quotientFraction :=
    mul_le_mul_of_nonneg_right hcorrelationBound hquotientFraction
  have hsquare :
      (positiveProductionCorrelation production quotient variance *
          quotientFraction) ^ 2 ≤
        ((1 - weightedHelicity ^ 2 / (weightMass * variance)) *
          quotientFraction) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hcorrelationNonneg hquotientFraction)
      (mul_nonneg hlocalizedNonneg hquotientFraction)).2 hproduct
  exact mul_le_mul_of_nonneg_right hsquare henstrophy

/-- If an adjoint orbit average retains amplitude `retained`, its weight mass
is at most `retained²`.  After paying a linear leakage scale, the localized
gap therefore leaves at most `1 - (retained - leakageScale)² / variance` of
the dangerous positive-production correlation. -/
theorem positiveProductionCorrelation_le_one_sub_retainedAverageAmplitude
    {production quotient variance weightMass retained leakageScale : ℝ}
    (hquotient : 0 < quotient) (hvariance : 0 < variance)
    (hweightMass : 0 < weightMass)
    (hweightMassBound : weightMass ≤ retained ^ 2)
    (hgap : quotient *
        (retained * (retained - leakageScale)) ^ 2 ≤
      weightMass * (quotient * variance - production ^ 2)) :
    positiveProductionCorrelation production quotient variance ≤
      1 - (retained - leakageScale) ^ 2 / variance := by
  have hbase :=
    positiveProductionCorrelation_le_one_sub_localizedHelicityRatio
      hquotient hvariance hweightMass hgap
  have hmassScaled :
      weightMass * (retained - leakageScale) ^ 2 ≤
        retained ^ 2 * (retained - leakageScale) ^ 2 :=
    mul_le_mul_of_nonneg_right hweightMassBound (sq_nonneg _)
  have hratio :
      (retained - leakageScale) ^ 2 / variance ≤
        (retained * (retained - leakageScale)) ^ 2 /
          (weightMass * variance) := by
    rw [div_le_div_iff₀ hvariance (mul_pos hweightMass hvariance)]
    calc
      (retained - leakageScale) ^ 2 * (weightMass * variance) =
          (weightMass * (retained - leakageScale) ^ 2) * variance := by ring
      _ ≤ (retained ^ 2 * (retained - leakageScale) ^ 2) * variance :=
        mul_le_mul_of_nonneg_right hmassScaled hvariance.le
      _ = (retained * (retained - leakageScale)) ^ 2 * variance := by ring
  exact hbase.trans (sub_le_sub_left hratio 1)

/-- The retained-amplitude estimate controls the complete correlated critical
factor after multiplication by the quotient fraction and enstrophy. -/
theorem correlatedCriticalFactor_le_retainedAverageFactor
    {production quotient variance weightMass retained leakageScale
      quotientFraction enstrophy : ℝ}
    (hquotient : 0 < quotient) (hvariance : 0 < variance)
    (hweightMass : 0 < weightMass)
    (hweightMassBound : weightMass ≤ retained ^ 2)
    (hquotientFraction : 0 ≤ quotientFraction)
    (henstrophy : 0 ≤ enstrophy)
    (hgap : quotient *
        (retained * (retained - leakageScale)) ^ 2 ≤
      weightMass * (quotient * variance - production ^ 2)) :
    (positiveProductionCorrelation production quotient variance *
        quotientFraction) ^ 2 * enstrophy ≤
      ((1 - (retained - leakageScale) ^ 2 / variance) *
        quotientFraction) ^ 2 * enstrophy := by
  have hcorrelationNonneg := positiveProductionCorrelation_nonneg
    production quotient variance hquotient.le hvariance.le
  have hcorrelationBound :=
    positiveProductionCorrelation_le_one_sub_retainedAverageAmplitude
      hquotient hvariance hweightMass hweightMassBound hgap
  have hallowanceNonneg :
      0 ≤ 1 - (retained - leakageScale) ^ 2 / variance :=
    hcorrelationNonneg.trans hcorrelationBound
  have hproduct :=
    mul_le_mul_of_nonneg_right hcorrelationBound hquotientFraction
  have hsquare :=
    (sq_le_sq₀ (mul_nonneg hcorrelationNonneg hquotientFraction)
      (mul_nonneg hallowanceNonneg hquotientFraction)).2 hproduct
  exact mul_le_mul_of_nonneg_right hsquare henstrophy

/-- The dimensionless helicity loss in the saturation bound is invariant under
the same active-scale concentration law as the underlying defect gap. -/
theorem localizedHelicityRatio_concentration_invariant
    (scaleParameter weightedHelicity weightMass variance : ℝ)
    (hscaleParameter : 0 < scaleParameter) :
    weightedHelicity ^ 2 /
        ((weightMass / scaleParameter ^ 3) *
          (scaleParameter ^ 3 * variance)) =
      weightedHelicity ^ 2 / (weightMass * variance) := by
  have hscaleCube : scaleParameter ^ 3 ≠ 0 :=
    pow_ne_zero 3 hscaleParameter.ne'
  field_simp [hscaleCube]

/-- A corrected localized-helicity gap remains coercive after paying any
certified transport-error budget.  This is the algebraic form needed for
approximately invariant vortex-tube weights. -/
theorem robustLocalizedDefectGap_of_transportError
    (quotient weightMass defect helicity coefficient transportError
      errorBudget : ℝ)
    (hquotient : 0 ≤ quotient)
    (hcorrected :
      quotient * (helicity - coefficient * transportError) ^ 2 ≤
        weightMass * defect)
    (herror : |transportError| ≤ errorBudget) :
    quotient *
        (max (|helicity| - |coefficient| * errorBudget) 0) ^ 2 ≤
      weightMass * defect := by
  have hcoefficientError :
      |coefficient * transportError| ≤ |coefficient| * errorBudget := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left herror (abs_nonneg coefficient)
  have htriangle :
      |helicity| ≤
        |helicity - coefficient * transportError| +
          |coefficient * transportError| := by
    calc
      |helicity| =
          |(helicity - coefficient * transportError) +
            coefficient * transportError| := by ring_nf
      _ ≤ |helicity - coefficient * transportError| +
          |coefficient * transportError| := abs_add_le _ _
  have hcore :
      |helicity| - |coefficient| * errorBudget ≤
        |helicity - coefficient * transportError| := by
    linarith
  have hmax :
      max (|helicity| - |coefficient| * errorBudget) 0 ≤
        |helicity - coefficient * transportError| :=
    max_le hcore (abs_nonneg _)
  have hsquare :
      (max (|helicity| - |coefficient| * errorBudget) 0) ^ 2 ≤
        |helicity - coefficient * transportError| ^ 2 :=
    (sq_le_sq₀ (le_max_right _ _) (abs_nonneg _)).2 hmax
  have hscaled := mul_le_mul_of_nonneg_left hsquare hquotient
  rw [sq_abs] at hscaled
  exact hscaled.trans hcorrected

/-- A profile with strictly positive correlated critical factor generates concentration
rescalings whose factor exceeds any prescribed real bound. -/
theorem correlatedCriticalDepletionFactor_unbounded_under_concentration
    (production quotient variance palinstrophy enstrophy bound : ℝ)
    (hpositive : 0 < correlatedCriticalDepletionFactor
      production quotient variance palinstrophy enstrophy) :
    ∃ scaleParameter : ℝ, 0 < scaleParameter ∧
      bound < correlatedCriticalDepletionFactor
        (scaleParameter ^ 3 * production) (scaleParameter ^ 3 * quotient)
        (scaleParameter ^ 3 * variance) (scaleParameter ^ 3 * palinstrophy)
        (scaleParameter * enstrophy) := by
  let factor := correlatedCriticalDepletionFactor
    production quotient variance palinstrophy enstrophy
  let scaleParameter := (|bound| + 1) / factor
  have hscaleParameter : 0 < scaleParameter := by
    dsimp [scaleParameter, factor]
    exact div_pos (by positivity) hpositive
  refine ⟨scaleParameter, hscaleParameter, ?_⟩
  rw [correlatedCriticalDepletionFactor_concentration_scaling
    scaleParameter production quotient variance palinstrophy enstrophy
    hscaleParameter]
  dsimp [scaleParameter, factor]
  rw [div_mul_cancel₀]
  · linarith [le_abs_self bound]
  · exact hpositive.ne'

/-- Correlation-refined cubic criterion.  The effective dynamic factor is
`correlation * quotientFraction`, whose square is the coefficient retained by
the sharp Young remainder. -/
theorem correlated_quotient_cubic_rate_bounded_of_energy_budget
    {E E' correlation quotientFraction : ℝ → ℝ}
    {a t C M B : ℝ}
    (hat : a ≤ t) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hEpos : ∀ x ∈ Icc a t, 0 < E x)
    (hEcont : ContinuousOn E (Icc a t))
    (hEderiv : ∀ x ∈ Ioo a t, HasDerivAt E (E' x) x)
    (hcubic : ∀ x ∈ Ioo a t,
      E' x ≤ C * (correlation x * quotientFraction x) ^ 2 * E x ^ 3)
    (hcritical : ∀ x ∈ Ioo a t,
      (correlation x * quotientFraction x) ^ 2 * E x ≤ M)
    (hEint : IntegrableOn E (Icc a t))
    (hbudget : (∫ x in a..t, E x) ≤ B) :
    E t ≤ E a * Real.exp (C * M * B) :=
  quotient_cubic_rate_bounded_of_energy_budget
    hat hC hM hEpos hEcont hEderiv hcubic hcritical hEint hbudget

/-- Dynamic continuation criterion paid directly by a localized-helicity
signal.  It is enough to control the critical product formed from the
remaining saturation allowance
`1 - weightedHelicity² / (weightMass * variance)` and the quotient fraction.
The defect-gap hypothesis then supplies the sharper correlation bound used by
the cubic enstrophy rate. -/
theorem localizedHelicity_refined_cubic_rate_bounded_of_energy_budget
    {E E' production quotient variance weightMass weightedHelicity
      quotientFraction : ℝ → ℝ}
    {a t C M B : ℝ}
    (hat : a ≤ t) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hEpos : ∀ x ∈ Icc a t, 0 < E x)
    (hEcont : ContinuousOn E (Icc a t))
    (hEderiv : ∀ x ∈ Ioo a t, HasDerivAt E (E' x) x)
    (hquotient : ∀ x ∈ Ioo a t, 0 < quotient x)
    (hvariance : ∀ x ∈ Ioo a t, 0 < variance x)
    (hweightMass : ∀ x ∈ Ioo a t, 0 < weightMass x)
    (hquotientFraction : ∀ x ∈ Ioo a t, 0 ≤ quotientFraction x)
    (hgap : ∀ x ∈ Ioo a t,
      quotient x * weightedHelicity x ^ 2 ≤
        weightMass x *
          (quotient x * variance x - production x ^ 2))
    (hcubic : ∀ x ∈ Ioo a t,
      E' x ≤ C *
        (positiveProductionCorrelation (production x) (quotient x)
          (variance x) * quotientFraction x) ^ 2 * E x ^ 3)
    (hcritical : ∀ x ∈ Ioo a t,
      ((1 - weightedHelicity x ^ 2 /
          (weightMass x * variance x)) * quotientFraction x) ^ 2 *
        E x ≤ M)
    (hEint : IntegrableOn E (Icc a t))
    (hbudget : (∫ x in a..t, E x) ≤ B) :
    E t ≤ E a * Real.exp (C * M * B) := by
  apply correlated_quotient_cubic_rate_bounded_of_energy_budget
    hat hC hM hEpos hEcont hEderiv hcubic ?_ hEint hbudget
  intro x hx
  exact (correlatedCriticalFactor_le_localizedHelicityFactor
    (hquotient x hx) (hvariance x hx) (hweightMass x hx)
    (hquotientFraction x hx)
    (hEpos x ⟨hx.1.le, hx.2.le⟩).le (hgap x hx)).trans
      (hcritical x hx)

/-- Dynamic continuation criterion stated in the scalar retained-amplitude
variables furnished by an adjoint orbit average.  The construction succeeds
whenever the retained amplitude minus its leakage scale controls the remaining
critical factor. -/
theorem retainedAverage_refined_cubic_rate_bounded_of_energy_budget
    {E E' production quotient variance weightMass retained leakageScale
      quotientFraction : ℝ → ℝ}
    {a t C M B : ℝ}
    (hat : a ≤ t) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hEpos : ∀ x ∈ Icc a t, 0 < E x)
    (hEcont : ContinuousOn E (Icc a t))
    (hEderiv : ∀ x ∈ Ioo a t, HasDerivAt E (E' x) x)
    (hquotient : ∀ x ∈ Ioo a t, 0 < quotient x)
    (hvariance : ∀ x ∈ Ioo a t, 0 < variance x)
    (hweightMass : ∀ x ∈ Ioo a t, 0 < weightMass x)
    (hweightMassBound : ∀ x ∈ Ioo a t,
      weightMass x ≤ retained x ^ 2)
    (hquotientFraction : ∀ x ∈ Ioo a t, 0 ≤ quotientFraction x)
    (hgap : ∀ x ∈ Ioo a t,
      quotient x *
          (retained x * (retained x - leakageScale x)) ^ 2 ≤
        weightMass x *
          (quotient x * variance x - production x ^ 2))
    (hcubic : ∀ x ∈ Ioo a t,
      E' x ≤ C *
        (positiveProductionCorrelation (production x) (quotient x)
          (variance x) * quotientFraction x) ^ 2 * E x ^ 3)
    (hcritical : ∀ x ∈ Ioo a t,
      ((1 - (retained x - leakageScale x) ^ 2 / variance x) *
          quotientFraction x) ^ 2 * E x ≤ M)
    (hEint : IntegrableOn E (Icc a t))
    (hbudget : (∫ x in a..t, E x) ≤ B) :
    E t ≤ E a * Real.exp (C * M * B) := by
  apply correlated_quotient_cubic_rate_bounded_of_energy_budget
    hat hC hM hEpos hEcont hEderiv hcubic ?_ hEint hbudget
  intro x hx
  exact (correlatedCriticalFactor_le_retainedAverageFactor
    (hquotient x hx) (hvariance x hx) (hweightMass x hx)
    (hweightMassBound x hx) (hquotientFraction x hx)
    (hEpos x ⟨hx.1.le, hx.2.le⟩).le (hgap x hx)).trans
      (hcritical x hx)
