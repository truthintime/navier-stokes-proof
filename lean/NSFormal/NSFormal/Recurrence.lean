import NSFormal.Budget
import NSFormal.PeriodicIntegration

/-!
# Long recurrent segments: drift versus curvature

This file begins the recurrent, nonclosed part of the vortex-line ledger.  It
records the exact vector-valued integration-by-parts identity behind the
finite-segment estimate and checks the algebra which turns slow lift drift into
a length-times-curvature floor and then into weighted line charges.
-/

open MeasureTheory Set
open scoped Interval InnerProductSpace

noncomputable section

/-- For a `C¹` vector path, its integral differs from its terminal tangent
times the interval length by the first moment of its derivative.  Applied to
the unit tangent of an arc-length curve, this is the exact starting point for
the recurrent drift/curvature dichotomy. -/
theorem intervalIntegral_eq_endpoint_sub_weighted_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L : ℝ} (hξ : ContDiff ℝ 1 ξ) :
    (∫ s in (0 : ℝ)..L, ξ s) =
      L • ξ L - ∫ s in (0 : ℝ)..L, s • deriv ξ s := by
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (u := id) (u' := fun _ : ℝ => (1 : ℝ))
    (v := ξ) (v' := deriv ξ)
    (fun s _hs => hasDerivAt_id s)
    (fun s _hs => (hξ.differentiable one_ne_zero).differentiableAt.hasDerivAt)
    (continuous_const.intervalIntegrable 0 L)
    ((hξ.continuous_deriv (by norm_num)).intervalIntegrable 0 L)
  simp only [id_eq, one_smul, zero_smul, sub_zero] at hparts
  apply eq_sub_of_add_eq
  rw [add_comm]
  exact (sub_eq_iff_eq_add.mp hparts.symm).symm

/-- Weighted Cauchy--Schwarz for the first moment of a `C¹` vector path. -/
theorem norm_intervalIntegral_weighted_deriv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L : ℝ} (hL : 0 ≤ L) (hξ : ContDiff ℝ 1 ξ) :
    ‖∫ s in (0 : ℝ)..L, s • deriv ξ s‖ ≤
      (L ^ 3 / 3) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖deriv ξ s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 L)
  have hderiv_cont : Continuous (deriv ξ) := hξ.continuous_deriv (by norm_num)
  have hs_mem : MemLp (fun s : ℝ => s) 2 μ := by
    apply (memLp_two_iff_integrable_sq continuous_id.aestronglyMeasurable).2
    exact (continuous_id.pow 2).intervalIntegrable 0 L |>.1
  have hk_mem : MemLp (fun s : ℝ => ‖deriv ξ s‖) 2 μ := by
    apply (memLp_two_iff_integrable_sq hderiv_cont.norm.aestronglyMeasurable).2
    exact (hderiv_cont.norm.pow 2).intervalIntegrable 0 L |>.1
  have hs_mem_real : MemLp (fun s : ℝ => s) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hs_mem
  have hk_mem_real : MemLp (fun s : ℝ => ‖deriv ξ s‖)
      (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hk_mem
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := fun s : ℝ => s) (g := fun s : ℝ => ‖deriv ξ s‖)
    ((ae_restrict_mem (μ := volume) measurableSet_Ioc).mono fun s hs => hs.1.le)
    (Filter.Eventually.of_forall fun s => norm_nonneg (deriv ξ s))
    hs_mem_real hk_mem_real
  have hs2 : (∫ s, s ^ (2 : ℝ) ∂μ) = L ^ 3 / 3 := by
    change (∫ s in Ioc 0 L, s ^ (2 : ℝ)) = _
    rw [← intervalIntegral.integral_of_le hL]
    norm_num [integral_pow]
  have hmain :
      ‖∫ s in Ioc 0 L, s • deriv ξ s‖ ≤
        (L ^ 3 / 3) ^ ((1 : ℝ) / 2) *
          (∫ s in Ioc 0 L, ‖deriv ξ s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    calc
      ‖∫ s in Ioc 0 L, s • deriv ξ s‖ ≤
          ∫ s in Ioc 0 L, ‖s • deriv ξ s‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ s in Ioc 0 L, s * ‖deriv ξ s‖ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        rw [norm_smul, Real.norm_of_nonneg hs.1.le]
      _ ≤ (∫ s, s ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
          (∫ s, ‖deriv ξ s‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
        simpa [μ] using hholder
      _ = (L ^ 3 / 3) ^ ((1 : ℝ) / 2) *
          (∫ s in Ioc 0 L, ‖deriv ξ s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [hs2]
        simp only [μ, Real.rpow_two]
  simpa only [intervalIntegral.integral_of_le hL] using hmain

/-- A unit terminal tangent turns the weighted Cauchy--Schwarz estimate into
the finite-segment drift/curvature inequality.  For an arc-length curve,
`ξ` is its unit tangent, the integral is the lifted endpoint displacement,
and the last integral is the total squared curvature. -/
theorem unit_tangent_drift_curvature_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L : ℝ} (hL : 0 ≤ L) (hξ : ContDiff ℝ 1 ξ)
    (hunit : ‖ξ L‖ = 1) :
    (L - ‖∫ s in (0 : ℝ)..L, ξ s‖) ^ 2 ≤
      L ^ 3 / 3 * (∫ s in (0 : ℝ)..L, ‖deriv ξ s‖ ^ 2) := by
  let displacement : E := ∫ s in (0 : ℝ)..L, ξ s
  let moment : E := ∫ s in (0 : ℝ)..L, s • deriv ξ s
  have hid : displacement = L • ξ L - moment :=
    intervalIntegral_eq_endpoint_sub_weighted_deriv hξ
  have hnorm_terminal : ‖L • ξ L‖ = L := by
    rw [norm_smul, Real.norm_of_nonneg hL, hunit, mul_one]
  have hsub : L • ξ L - displacement = moment := by
    rw [hid]
    abel
  have hgap_abs : |L - ‖displacement‖| ≤ ‖moment‖ := by
    calc
      |L - ‖displacement‖| = |‖L • ξ L‖ - ‖displacement‖| := by
        rw [hnorm_terminal]
      _ ≤ ‖L • ξ L - displacement‖ := abs_norm_sub_norm_le _ _
      _ = ‖moment‖ := by rw [hsub]
  have hgap_sq : (L - ‖displacement‖) ^ 2 ≤ ‖moment‖ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hgap_abs
  have hA0 : 0 ≤ L ^ 3 / 3 := by positivity
  have hB0 : 0 ≤ ∫ s in (0 : ℝ)..L, ‖deriv ξ s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hL fun _ _ => sq_nonneg _
  have hcs : ‖moment‖ ≤
      (L ^ 3 / 3) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖deriv ξ s‖ ^ 2) ^ ((1 : ℝ) / 2) :=
    norm_intervalIntegral_weighted_deriv_le hL hξ
  have hcs_sq : ‖moment‖ ^ 2 ≤
      ((L ^ 3 / 3) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖deriv ξ s‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _))).2 hcs
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, mul_pow,
    Real.sq_sqrt hA0, Real.sq_sqrt hB0] at hcs_sq
  exact hgap_sq.trans hcs_sq

/-- Algebraic core of the recurrent turning estimate.  If the lift
displacement is at most `α L`, and weighted Cauchy--Schwarz gives
`(L-drift)² ≤ L³ curvature / 3`, then
`L * curvature ≥ 3(1-α)²`.

The analytic antecedent is what `intervalIntegral_eq_endpoint_sub_weighted_deriv`
produces for a unit tangent after taking norms and applying Cauchy--Schwarz. -/
theorem slow_lift_drift_forces_curvature_product
    {L α drift curvature : ℝ}
    (hL : 0 < L) (hα1 : α ≤ 1)
    (hslow : drift ≤ α * L)
    (hweighted : (L - drift) ^ 2 ≤ L ^ 3 * curvature / 3) :
    3 * (1 - α) ^ 2 ≤ L * curvature := by
  have hgap : (1 - α) * L ≤ L - drift := by
    nlinarith
  have hgap0 : 0 ≤ (1 - α) * L := mul_nonneg (sub_nonneg.mpr hα1) hL.le
  have hright0 : 0 ≤ L - drift := hgap0.trans hgap
  have hsquares : ((1 - α) * L) ^ 2 ≤ (L - drift) ^ 2 := by
    exact (sq_le_sq₀ hgap0 hright0).2 hgap
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  apply le_of_mul_le_mul_right _ hLsq
  calc
    (3 * (1 - α) ^ 2) * L ^ 2 =
        3 * (((1 - α) * L) ^ 2) := by ring
    _ ≤ 3 * ((L - drift) ^ 2) := by gcongr
    _ ≤ 3 * (L ^ 3 * curvature / 3) := by gcongr
    _ = (L * curvature) * L ^ 2 := by ring

/-- Fully analytic finite-segment turning floor: a `C¹` unit-tangent path
whose lifted endpoint drift is at most `α` times its length must pay a
positive length-times-squared-curvature charge. -/
theorem slow_unit_tangent_forces_curvature_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L α : ℝ}
    (hL : 0 < L) (hα1 : α ≤ 1) (hξ : ContDiff ℝ 1 ξ)
    (hunit : ‖ξ L‖ = 1)
    (hslow : ‖∫ s in (0 : ℝ)..L, ξ s‖ ≤ α * L) :
    3 * (1 - α) ^ 2 ≤
      L * (∫ s in (0 : ℝ)..L, ‖deriv ξ s‖ ^ 2) := by
  apply slow_lift_drift_forces_curvature_product hL hα1 hslow
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    unit_tangent_drift_curvature_bound hL.le hξ hunit

/-- Cauchy--Schwarz for the real inner-product pairing of two continuous vector paths on an
interval.  This is the line-work estimate used without taking an absolute value curve by
curve until after subtracting a coherent constant direction. -/
theorem abs_intervalIntegral_inner_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f g : ℝ → E} {L : ℝ} (hL : 0 ≤ L) (hf : Continuous f) (hg : Continuous g) :
    |∫ s in (0 : ℝ)..L, ⟪f s, g s⟫_ℝ| ≤
      (∫ s in (0 : ℝ)..L, ‖f s‖ ^ 2) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖g s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 L)
  have hf_mem : MemLp (fun s : ℝ => ‖f s‖) 2 μ := by
    apply (memLp_two_iff_integrable_sq hf.norm.aestronglyMeasurable).2
    exact (hf.norm.pow 2).intervalIntegrable 0 L |>.1
  have hg_mem : MemLp (fun s : ℝ => ‖g s‖) 2 μ := by
    apply (memLp_two_iff_integrable_sq hg.norm.aestronglyMeasurable).2
    exact (hg.norm.pow 2).intervalIntegrable 0 L |>.1
  have hf_mem_real : MemLp (fun s : ℝ => ‖f s‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hf_mem
  have hg_mem_real : MemLp (fun s : ℝ => ‖g s‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hg_mem
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := fun s : ℝ => ‖f s‖) (g := fun s : ℝ => ‖g s‖)
    (Filter.Eventually.of_forall fun s => norm_nonneg (f s))
    (Filter.Eventually.of_forall fun s => norm_nonneg (g s))
    hf_mem_real hg_mem_real
  have hmain : |∫ s in Ioc 0 L, ⟪f s, g s⟫_ℝ| ≤
      (∫ s in Ioc 0 L, ‖f s‖ ^ 2) ^ ((1 : ℝ) / 2) *
        (∫ s in Ioc 0 L, ‖g s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    calc
      |∫ s in Ioc 0 L, ⟪f s, g s⟫_ℝ| ≤
          ∫ s in Ioc 0 L, |⟪f s, g s⟫_ℝ| := by
        simpa only [← Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := μ) (fun s => ⟪f s, g s⟫_ℝ))
      _ ≤ ∫ s in Ioc 0 L, ‖f s‖ * ‖g s‖ := by
        apply integral_mono_ae
        · have hinner_cont : Continuous (fun s => ⟪f s, g s⟫_ℝ) := hf.inner hg
          exact hinner_cont.norm.intervalIntegrable 0 L |>.1
        · exact (hf.norm.mul hg.norm).intervalIntegrable 0 L |>.1
        · exact Filter.Eventually.of_forall fun s => abs_real_inner_le_norm (f s) (g s)
      _ ≤ (∫ s, ‖f s‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
          (∫ s, ‖g s‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
        simpa [μ] using hholder
      _ = (∫ s in Ioc 0 L, ‖f s‖ ^ 2) ^ ((1 : ℝ) / 2) *
          (∫ s in Ioc 0 L, ‖g s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
        simp only [μ, Real.rpow_two]
  simpa only [intervalIntegral.integral_of_le hL] using hmain

/-- Exact ballistic-coherence identity.  A unit-speed tangent whose endpoint displacement is
close to length `L` is close in mean square to its constant average direction. -/
theorem unit_tangent_variance_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L : ℝ} (hL : 0 < L) (hξ : Continuous ξ)
    (hunit : ∀ s ∈ uIcc (0 : ℝ) L, ‖ξ s‖ = 1) :
    (∫ s in (0 : ℝ)..L,
      ‖ξ s - (L⁻¹ : ℝ) • (∫ r in (0 : ℝ)..L, ξ r)‖ ^ 2) =
      L - ‖∫ r in (0 : ℝ)..L, ξ r‖ ^ 2 / L := by
  let displacement : E := ∫ r in (0 : ℝ)..L, ξ r
  let average : E := (L⁻¹ : ℝ) • displacement
  have hξ_int : IntervalIntegrable ξ volume 0 L := hξ.intervalIntegrable 0 L
  have hnorm_sq_int : IntervalIntegrable (fun s => ‖ξ s‖ ^ 2) volume 0 L :=
    (hξ.norm.pow 2).intervalIntegrable 0 L
  have hinner_int : IntervalIntegrable (fun s => ⟪ξ s, average⟫_ℝ) volume 0 L :=
    (hξ.inner continuous_const).intervalIntegrable 0 L
  have hconst_int : IntervalIntegrable (fun _ : ℝ => ‖average‖ ^ 2) volume 0 L :=
    continuous_const.intervalIntegrable 0 L
  have hnorm_integral : (∫ s in (0 : ℝ)..L, ‖ξ s‖ ^ 2) = L := by
    calc
      (∫ s in (0 : ℝ)..L, ‖ξ s‖ ^ 2) = ∫ _s in (0 : ℝ)..L, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [hunit s hs]
        norm_num
      _ = L := by simp
  have hinner_integral : (∫ s in (0 : ℝ)..L, ⟪ξ s, average⟫_ℝ) =
      ⟪displacement, average⟫_ℝ := by
    calc
      (∫ s in (0 : ℝ)..L, ⟪ξ s, average⟫_ℝ) =
          ∫ s in (0 : ℝ)..L, ⟪average, ξ s⟫_ℝ := by
        apply intervalIntegral.integral_congr
        intro s _hs
        exact real_inner_comm _ _
      _ = ⟪average, displacement⟫_ℝ := by
        exact (innerSL ℝ average).intervalIntegral_comp_comm hξ_int
      _ = ⟪displacement, average⟫_ℝ := real_inner_comm _ _
  have haverage_inner : ⟪displacement, average⟫_ℝ =
      L⁻¹ * ‖displacement‖ ^ 2 := by
    rw [show average = (L⁻¹ : ℝ) • displacement by rfl,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
  have haverage_norm : ‖average‖ ^ 2 = L⁻¹ ^ 2 * ‖displacement‖ ^ 2 := by
    rw [show average = (L⁻¹ : ℝ) • displacement by rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hL.le), mul_pow]
  calc
    (∫ s in (0 : ℝ)..L, ‖ξ s - (L⁻¹ : ℝ) • displacement‖ ^ 2) =
        ∫ s in (0 : ℝ)..L,
          (‖ξ s‖ ^ 2 - 2 * ⟪ξ s, average⟫_ℝ + ‖average‖ ^ 2) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      dsimp only
      rw [show (L⁻¹ : ℝ) • displacement = average by rfl, norm_sub_sq_real]
    _ = (∫ s in (0 : ℝ)..L, ‖ξ s‖ ^ 2) -
          2 * (∫ s in (0 : ℝ)..L, ⟪ξ s, average⟫_ℝ) +
          ∫ _s in (0 : ℝ)..L, ‖average‖ ^ 2 := by
      rw [intervalIntegral.integral_add
        (hnorm_sq_int.sub (hinner_int.const_mul 2)) hconst_int,
        intervalIntegral.integral_sub hnorm_sq_int (hinner_int.const_mul 2),
        intervalIntegral.integral_const_mul]
    _ = L - ‖displacement‖ ^ 2 / L := by
      rw [hnorm_integral, hinner_integral, haverage_inner,
        intervalIntegral.integral_const, haverage_norm]
      have hcancel : L ^ 2 * L⁻¹ ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hL.ne', one_pow]
      field_simp [hL.ne']
      linear_combination ‖displacement‖ ^ 2 * hcancel

/-- Normalized ballistic direction identity.  The mean-square distance from the unit tangent
to the unit vector in the displacement direction is exactly twice the length deficit. -/
theorem unit_tangent_normalized_direction_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L : ℝ} (hξ : Continuous ξ)
    (hunit : ∀ s ∈ uIcc (0 : ℝ) L, ‖ξ s‖ = 1)
    (hdisplacement : (∫ r in (0 : ℝ)..L, ξ r) ≠ 0) :
    (∫ s in (0 : ℝ)..L,
      ‖ξ s - ‖∫ r in (0 : ℝ)..L, ξ r‖⁻¹ •
        (∫ r in (0 : ℝ)..L, ξ r)‖ ^ 2) =
      2 * (L - ‖∫ r in (0 : ℝ)..L, ξ r‖) := by
  let displacement : E := ∫ r in (0 : ℝ)..L, ξ r
  let direction : E := ‖displacement‖⁻¹ • displacement
  have hdne : displacement ≠ 0 := hdisplacement
  have hdnorm_ne : ‖displacement‖ ≠ 0 := norm_ne_zero_iff.mpr hdne
  have hξ_int : IntervalIntegrable ξ volume 0 L := hξ.intervalIntegrable 0 L
  have hnorm_sq_int : IntervalIntegrable (fun s => ‖ξ s‖ ^ 2) volume 0 L :=
    (hξ.norm.pow 2).intervalIntegrable 0 L
  have hinner_int : IntervalIntegrable (fun s => ⟪ξ s, direction⟫_ℝ) volume 0 L :=
    (hξ.inner continuous_const).intervalIntegrable 0 L
  have hconst_int : IntervalIntegrable (fun _ : ℝ => ‖direction‖ ^ 2) volume 0 L :=
    continuous_const.intervalIntegrable 0 L
  have hnorm_integral : (∫ s in (0 : ℝ)..L, ‖ξ s‖ ^ 2) = L := by
    calc
      (∫ s in (0 : ℝ)..L, ‖ξ s‖ ^ 2) = ∫ _s in (0 : ℝ)..L, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [hunit s hs]
        norm_num
      _ = L := by simp
  have hinner_integral : (∫ s in (0 : ℝ)..L, ⟪ξ s, direction⟫_ℝ) =
      ⟪displacement, direction⟫_ℝ := by
    calc
      (∫ s in (0 : ℝ)..L, ⟪ξ s, direction⟫_ℝ) =
          ∫ s in (0 : ℝ)..L, ⟪direction, ξ s⟫_ℝ := by
        apply intervalIntegral.integral_congr
        intro s _hs
        exact real_inner_comm _ _
      _ = ⟪direction, displacement⟫_ℝ := by
        exact (innerSL ℝ direction).intervalIntegral_comp_comm hξ_int
      _ = ⟪displacement, direction⟫_ℝ := real_inner_comm _ _
  have hdirection_inner : ⟪displacement, direction⟫_ℝ = ‖displacement‖ := by
    rw [show direction = ‖displacement‖⁻¹ • displacement by rfl,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hdnorm_ne]
  have hdirection_norm : ‖direction‖ = 1 := by
    rw [show direction = ‖displacement‖⁻¹ • displacement by rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hdnorm_ne]
  calc
    (∫ s in (0 : ℝ)..L, ‖ξ s - direction‖ ^ 2) =
        ∫ s in (0 : ℝ)..L,
          (‖ξ s‖ ^ 2 - 2 * ⟪ξ s, direction⟫_ℝ + ‖direction‖ ^ 2) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      dsimp only
      rw [norm_sub_sq_real]
    _ = (∫ s in (0 : ℝ)..L, ‖ξ s‖ ^ 2) -
          2 * (∫ s in (0 : ℝ)..L, ⟪ξ s, direction⟫_ℝ) +
          ∫ _s in (0 : ℝ)..L, ‖direction‖ ^ 2 := by
      rw [intervalIntegral.integral_add
        (hnorm_sq_int.sub (hinner_int.const_mul 2)) hconst_int,
        intervalIntegral.integral_sub hnorm_sq_int (hinner_int.const_mul 2),
        intervalIntegral.integral_const_mul]
    _ = 2 * (L - ‖displacement‖) := by
      rw [hnorm_integral, hinner_integral, hdirection_inner,
        intervalIntegral.integral_const, hdirection_norm]
      ring

/-- Near-maximal lift drift forces the tangent to be close in mean square to one constant
direction.  This is the quantitative planar-like structure in the ballistic branch. -/
theorem ballistic_drift_forces_tangent_coherence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L α : ℝ} (hL : 0 < L) (hα : 0 ≤ α)
    (hξ : Continuous ξ) (hunit : ∀ s ∈ uIcc (0 : ℝ) L, ‖ξ s‖ = 1)
    (hballistic : α * L ≤ ‖∫ r in (0 : ℝ)..L, ξ r‖) :
    (∫ s in (0 : ℝ)..L,
      ‖ξ s - (L⁻¹ : ℝ) • (∫ r in (0 : ℝ)..L, ξ r)‖ ^ 2) ≤
      L * (1 - α ^ 2) := by
  rw [unit_tangent_variance_identity hL hξ hunit]
  have hαL0 : 0 ≤ α * L := mul_nonneg hα hL.le
  have hsquare : (α * L) ^ 2 ≤ ‖∫ r in (0 : ℝ)..L, ξ r‖ ^ 2 :=
    (sq_le_sq₀ hαL0 (norm_nonneg _)).2 hballistic
  have hdiv : α ^ 2 * L ≤ ‖∫ r in (0 : ℝ)..L, ξ r‖ ^ 2 / L := by
    apply (le_div_iff₀ hL).2
    nlinarith
  nlinarith

/-- The corresponding estimate for the normalized displacement direction. -/
theorem ballistic_drift_forces_unit_direction_coherence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L α : ℝ} (hL : 0 < L) (hα : 0 < α)
    (hξ : Continuous ξ) (hunit : ∀ s ∈ uIcc (0 : ℝ) L, ‖ξ s‖ = 1)
    (hballistic : α * L ≤ ‖∫ r in (0 : ℝ)..L, ξ r‖) :
    (∫ s in (0 : ℝ)..L,
      ‖ξ s - ‖∫ r in (0 : ℝ)..L, ξ r‖⁻¹ •
        (∫ r in (0 : ℝ)..L, ξ r)‖ ^ 2) ≤
      2 * L * (1 - α) := by
  have hnorm_pos : 0 < ‖∫ r in (0 : ℝ)..L, ξ r‖ :=
    (mul_pos hα hL).trans_le hballistic
  have hdisplacement : (∫ r in (0 : ℝ)..L, ξ r) ≠ 0 :=
    norm_pos_iff.mp hnorm_pos
  rw [unit_tangent_normalized_direction_identity hξ hunit hdisplacement]
  nlinarith

/-- A ballistic line pairing is its signed constant-average-direction pairing plus an error
controlled by tangent coherence and the `L²` size of the paired field.  This leaves the first
term signed, so the exactly planar limit can be paid by scalar diffusion rather than by a
direction norm. -/
theorem ballistic_line_pairing_error_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ξ field : ℝ → E} {L α : ℝ} (hL : 0 < L) (hα : 0 ≤ α)
    (hξ : Continuous ξ) (hfield : Continuous field)
    (hunit : ∀ s ∈ uIcc (0 : ℝ) L, ‖ξ s‖ = 1)
    (hballistic : α * L ≤ ‖∫ r in (0 : ℝ)..L, ξ r‖) :
    |(∫ s in (0 : ℝ)..L, ⟪ξ s, field s⟫_ℝ) -
        ∫ s in (0 : ℝ)..L,
          ⟪(L⁻¹ : ℝ) • (∫ r in (0 : ℝ)..L, ξ r), field s⟫_ℝ| ≤
      (L * (1 - α ^ 2)) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖field s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  let average : E := (L⁻¹ : ℝ) • (∫ r in (0 : ℝ)..L, ξ r)
  have hleft_int : IntervalIntegrable (fun s => ⟪ξ s, field s⟫_ℝ) volume 0 L :=
    (hξ.inner hfield).intervalIntegrable 0 L
  have hright_int : IntervalIntegrable (fun s => ⟪average, field s⟫_ℝ) volume 0 L :=
    (continuous_const.inner hfield).intervalIntegrable 0 L
  have hsplit :
      (∫ s in (0 : ℝ)..L, ⟪ξ s, field s⟫_ℝ) -
          (∫ s in (0 : ℝ)..L, ⟪average, field s⟫_ℝ) =
        ∫ s in (0 : ℝ)..L, ⟪ξ s - average, field s⟫_ℝ := by
    rw [← intervalIntegral.integral_sub hleft_int hright_int]
    apply intervalIntegral.integral_congr
    intro s _hs
    exact (inner_sub_left _ _ _).symm
  have hA0 : 0 ≤ ∫ s in (0 : ℝ)..L, ‖ξ s - average‖ ^ 2 :=
    intervalIntegral.integral_nonneg hL.le fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ ∫ s in (0 : ℝ)..L, ‖field s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hL.le fun _ _ => sq_nonneg _
  have hvariance : (∫ s in (0 : ℝ)..L, ‖ξ s - average‖ ^ 2) ≤
      L * (1 - α ^ 2) :=
    ballistic_drift_forces_tangent_coherence hL hα hξ hunit hballistic
  calc
    |(∫ s in (0 : ℝ)..L, ⟪ξ s, field s⟫_ℝ) -
        ∫ s in (0 : ℝ)..L, ⟪average, field s⟫_ℝ| =
        |∫ s in (0 : ℝ)..L, ⟪ξ s - average, field s⟫_ℝ| := by rw [hsplit]
    _ ≤ (∫ s in (0 : ℝ)..L, ‖ξ s - average‖ ^ 2) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖field s‖ ^ 2) ^ ((1 : ℝ) / 2) :=
      abs_intervalIntegral_inner_le hL.le (hξ.sub continuous_const) hfield
    _ ≤ (L * (1 - α ^ 2)) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖field s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.rpow_le_rpow hA0 hvariance (by norm_num)
      · exact Real.rpow_nonneg hB0 _

/-- Unit-direction version of the ballistic line-pairing split.  This is the form directly
comparable with regularity criteria involving `v × ω` for a unit direction field `v`. -/
theorem ballistic_unit_direction_line_pairing_error_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ξ field : ℝ → E} {L α : ℝ} (hL : 0 < L) (hα : 0 < α)
    (hξ : Continuous ξ) (hfield : Continuous field)
    (hunit : ∀ s ∈ uIcc (0 : ℝ) L, ‖ξ s‖ = 1)
    (hballistic : α * L ≤ ‖∫ r in (0 : ℝ)..L, ξ r‖) :
    |(∫ s in (0 : ℝ)..L, ⟪ξ s, field s⟫_ℝ) -
        ∫ s in (0 : ℝ)..L,
          ⟪‖∫ r in (0 : ℝ)..L, ξ r‖⁻¹ •
            (∫ r in (0 : ℝ)..L, ξ r), field s⟫_ℝ| ≤
      (2 * L * (1 - α)) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖field s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  let direction : E := ‖∫ r in (0 : ℝ)..L, ξ r‖⁻¹ •
    (∫ r in (0 : ℝ)..L, ξ r)
  have hleft_int : IntervalIntegrable (fun s => ⟪ξ s, field s⟫_ℝ) volume 0 L :=
    (hξ.inner hfield).intervalIntegrable 0 L
  have hright_int : IntervalIntegrable (fun s => ⟪direction, field s⟫_ℝ) volume 0 L :=
    (continuous_const.inner hfield).intervalIntegrable 0 L
  have hsplit :
      (∫ s in (0 : ℝ)..L, ⟪ξ s, field s⟫_ℝ) -
          (∫ s in (0 : ℝ)..L, ⟪direction, field s⟫_ℝ) =
        ∫ s in (0 : ℝ)..L, ⟪ξ s - direction, field s⟫_ℝ := by
    rw [← intervalIntegral.integral_sub hleft_int hright_int]
    apply intervalIntegral.integral_congr
    intro s _hs
    exact (inner_sub_left _ _ _).symm
  have hA0 : 0 ≤ ∫ s in (0 : ℝ)..L, ‖ξ s - direction‖ ^ 2 :=
    intervalIntegral.integral_nonneg hL.le fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ ∫ s in (0 : ℝ)..L, ‖field s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hL.le fun _ _ => sq_nonneg _
  have hcoherence : (∫ s in (0 : ℝ)..L, ‖ξ s - direction‖ ^ 2) ≤
      2 * L * (1 - α) :=
    ballistic_drift_forces_unit_direction_coherence hL hα hξ hunit hballistic
  calc
    |(∫ s in (0 : ℝ)..L, ⟪ξ s, field s⟫_ℝ) -
        ∫ s in (0 : ℝ)..L, ⟪direction, field s⟫_ℝ| =
        |∫ s in (0 : ℝ)..L, ⟪ξ s - direction, field s⟫_ℝ| := by rw [hsplit]
    _ ≤ (∫ s in (0 : ℝ)..L, ‖ξ s - direction‖ ^ 2) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖field s‖ ^ 2) ^ ((1 : ℝ) / 2) :=
      abs_intervalIntegral_inner_le hL.le (hξ.sub continuous_const) hfield
    _ ≤ (2 * L * (1 - α)) ^ ((1 : ℝ) / 2) *
        (∫ s in (0 : ℝ)..L, ‖field s‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.rpow_le_rpow hA0 hcoherence (by norm_num)
      · exact Real.rpow_nonneg hB0 _

/-- Weighting a recurrent segment by a vorticity floor converts a geometric
`length × curvature` floor into the product of its energy and direction
charges. -/
theorem recurrent_turning_charge_product
    {weight length curvatureFloor energy direction geometricFloor : ℝ}
    (hweight : 0 ≤ weight) (hlength : 0 ≤ length)
    (hcurvature : 0 ≤ curvatureFloor)
    (hturn : geometricFloor ≤ length * curvatureFloor)
    (henergy : weight * length ≤ energy)
    (hdirection : weight * curvatureFloor ≤ direction) :
    weight ^ 2 * geometricFloor ≤ energy * direction := by
  have hwl : 0 ≤ weight * length := mul_nonneg hweight hlength
  have hwc : 0 ≤ weight * curvatureFloor := mul_nonneg hweight hcurvature
  calc
    weight ^ 2 * geometricFloor ≤ weight ^ 2 * (length * curvatureFloor) := by
      gcongr
    _ = (weight * length) * (weight * curvatureFloor) := by ring
    _ ≤ energy * direction :=
      mul_le_mul henergy hdirection hwc (hwl.trans henergy)

/-- The explicit slow-drift recurrent charge floor obtained by combining the
previous two theorems. -/
theorem slow_recurrent_turning_charge_product
    {L α drift curvature weight energy direction : ℝ}
    (hL : 0 < L) (hα1 : α ≤ 1)
    (hcurvature : 0 ≤ curvature) (hweight : 0 ≤ weight)
    (hslow : drift ≤ α * L)
    (hweighted : (L - drift) ^ 2 ≤ L ^ 3 * curvature / 3)
    (henergy : weight * L ≤ energy)
    (hdirection : weight * curvature ≤ direction) :
    3 * weight ^ 2 * (1 - α) ^ 2 ≤ energy * direction := by
  have h := recurrent_turning_charge_product hweight hL.le hcurvature
    (slow_lift_drift_forces_curvature_product hL hα1 hslow hweighted)
    henergy hdirection
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Adaptive balanced turning ledger.  Choosing `α = 1 - c / W` and the persistent
vorticity weight `θ W` cancels the peak amplitude: every slow-drift line pays the fixed charge
`3 (θ c)²`, independent of `W`. -/
theorem adaptive_slow_recurrent_turning_charge_product
    {L W c θ drift curvature energy direction : ℝ}
    (hL : 0 < L) (hW : 0 < W) (hc : 0 ≤ c) (hθ : 0 ≤ θ)
    (hcurvature : 0 ≤ curvature)
    (hslow : drift ≤ (1 - c / W) * L)
    (hweighted : (L - drift) ^ 2 ≤ L ^ 3 * curvature / 3)
    (henergy : (θ * W) * L ≤ energy)
    (hdirection : (θ * W) * curvature ≤ direction) :
    3 * (θ * c) ^ 2 ≤ energy * direction := by
  have hα1 : 1 - c / W ≤ 1 := by
    linarith [div_nonneg hc hW.le]
  have hweight : 0 ≤ θ * W := mul_nonneg hθ hW.le
  have hbase := slow_recurrent_turning_charge_product hL hα1 hcurvature hweight
    hslow hweighted henergy hdirection
  have hcancel : (θ * W) ^ 2 * (1 - (1 - c / W)) ^ 2 = (θ * c) ^ 2 := by
    field_simp [hW.ne']
    ring
  rw [← hcancel]
  simpa [mul_assoc] using hbase

/-- Algebraic universal-cover branch.  If a near return has lift displacement
bounded by `error + period * winding`, but the displacement is larger than
`α L`, then it carries the displayed winding density. -/
theorem ballistic_recurrence_forces_winding
    {L α drift error period winding δ : ℝ}
    (hperiod : 0 < period)
    (hdecomp : drift ≤ error + period * winding)
    (herror : error ≤ δ) (hballistic : α * L < drift) :
    (α * L - δ) / period < winding := by
  apply (div_lt_iff₀ hperiod).2
  linarith

/-- Finite recurrent-segment dichotomy: under the weighted curvature estimate
and the universal-cover displacement bound, every segment either pays a
turning floor or carries quantitative lattice winding. -/
theorem recurrent_segment_turning_or_winding
    {L α drift curvature error period winding δ : ℝ}
    (hL : 0 < L) (hα1 : α ≤ 1) (hperiod : 0 < period)
    (hweighted : (L - drift) ^ 2 ≤ L ^ 3 * curvature / 3)
    (hdecomp : drift ≤ error + period * winding) (herror : error ≤ δ) :
    3 * (1 - α) ^ 2 ≤ L * curvature ∨
      (α * L - δ) / period < winding := by
  by_cases hslow : drift ≤ α * L
  · exact Or.inl <|
      slow_lift_drift_forces_curvature_product hL hα1 hslow hweighted
  · exact Or.inr <|
      ballistic_recurrence_forces_winding hperiod hdecomp herror (lt_of_not_ge hslow)

/-- Analytic recurrent-segment trichotomy packaged as two branches.  A unit tangent either
pays squared curvature, or it simultaneously carries lattice winding and is close in `L²` to
its constant average direction.  The latter is the quantitative input for a scalar-diffusive,
approximately planar treatment of persistent ballistic trajectories. -/
theorem recurrent_unit_tangent_turning_or_coherent_winding
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L α error period winding δ : ℝ}
    (hL : 0 < L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hperiod : 0 < period)
    (hξ : ContDiff ℝ 1 ξ)
    (hunit : ∀ s ∈ uIcc (0 : ℝ) L, ‖ξ s‖ = 1)
    (hdecomp : ‖∫ s in (0 : ℝ)..L, ξ s‖ ≤ error + period * winding)
    (herror : error ≤ δ) :
    3 * (1 - α) ^ 2 ≤
        L * (∫ s in (0 : ℝ)..L, ‖deriv ξ s‖ ^ 2) ∨
      ((∫ s in (0 : ℝ)..L,
          ‖ξ s - (L⁻¹ : ℝ) • (∫ r in (0 : ℝ)..L, ξ r)‖ ^ 2) ≤
          L * (1 - α ^ 2) ∧
        (α * L - δ) / period < winding) := by
  by_cases hslow : ‖∫ s in (0 : ℝ)..L, ξ s‖ ≤ α * L
  · exact Or.inl <| slow_unit_tangent_forces_curvature_product
      hL hα1 hξ (hunit L right_mem_uIcc) hslow
  · have hballistic : α * L < ‖∫ s in (0 : ℝ)..L, ξ s‖ := lt_of_not_ge hslow
    exact Or.inr ⟨
      ballistic_drift_forces_tangent_coherence hL hα0 hξ.continuous hunit hballistic.le,
      ballistic_recurrence_forces_winding hperiod hdecomp herror hballistic⟩

/-- Balanced adaptive recurrent dichotomy.  Taking `α = 1 - c / W` makes the slow branch pay
curvature `3(c/W)²`, while the ballistic branch is within `2L(c/W)` of its normalized unit
direction and carries the corresponding winding.  After weighting by persistent vorticity
`θW`, the first floor is independent of `W`; multiplying the second deficit by `W` gives `c`. -/
theorem adaptive_recurrent_turning_or_unit_coherent_winding
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ξ : ℝ → E} {L W c error period winding δ : ℝ}
    (hL : 0 < L) (hW : 0 < W) (hc : 0 < c) (hcW : c < W)
    (hperiod : 0 < period) (hξ : ContDiff ℝ 1 ξ)
    (hunit : ∀ s ∈ uIcc (0 : ℝ) L, ‖ξ s‖ = 1)
    (hdecomp : ‖∫ s in (0 : ℝ)..L, ξ s‖ ≤ error + period * winding)
    (herror : error ≤ δ) :
    3 * (c / W) ^ 2 ≤
        L * (∫ s in (0 : ℝ)..L, ‖deriv ξ s‖ ^ 2) ∨
      ((∫ s in (0 : ℝ)..L,
          ‖ξ s - ‖∫ r in (0 : ℝ)..L, ξ r‖⁻¹ •
            (∫ r in (0 : ℝ)..L, ξ r)‖ ^ 2) ≤
          2 * L * (c / W) ∧
        (((1 - c / W) * L - δ) / period < winding)) := by
  have hαpos : 0 < 1 - c / W := by
    rw [sub_pos, div_lt_one hW]
    exact hcW
  have hα1 : 1 - c / W ≤ 1 := by
    linarith [div_nonneg hc.le hW.le]
  by_cases hslow : ‖∫ s in (0 : ℝ)..L, ξ s‖ ≤ (1 - c / W) * L
  · have hturn := slow_unit_tangent_forces_curvature_product
      hL hα1 hξ (hunit L right_mem_uIcc) hslow
    exact Or.inl <| by
      convert hturn using 1
      all_goals ring
  · have hballistic : (1 - c / W) * L < ‖∫ s in (0 : ℝ)..L, ξ s‖ :=
      lt_of_not_ge hslow
    have hcoherence := ballistic_drift_forces_unit_direction_coherence
      hL hαpos hξ.continuous hunit hballistic.le
    have hwinding := ballistic_recurrence_forces_winding
      hperiod hdecomp herror hballistic
    have hcoherence' :
        (∫ s in (0 : ℝ)..L,
            ‖ξ s - ‖∫ r in (0 : ℝ)..L, ξ r‖⁻¹ •
              (∫ r in (0 : ℝ)..L, ξ r)‖ ^ 2) ≤
            2 * L * (c / W) := by
      convert hcoherence using 1
      all_goals ring
    exact Or.inr ⟨hcoherence', hwinding⟩
