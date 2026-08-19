import Mathlib
import NSFormal.NewProofAlgebra

/-!
# Analytic part of the strain budget

This file starts replacing the scalar exponent checks in `CampaignAlgebra` by the
measure-theoretic estimates used in the paper.  In particular, the theorem below
is the Hölder step in the time integration of the strain budget:

`∫ Ω^(5/6) ≤ (∫ Ω)^(5/6) μ(univ)^(1/6)`.

Unlike `w10_holder_exponents`, this theorem quantifies over a measurable function
and proves the integral inequality itself.
-/

open MeasureTheory

/-- Nonnegative `L²` Cauchy--Schwarz in integral form. -/
theorem integral_mul_le_sqrt_sq_integrals
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ≤
      (∫ x, f x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ x, g x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hg
  simpa using integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    hf_nonneg hg_nonneg hf' hg'

/-- Squared form of nonnegative integral Cauchy--Schwarz.  This is the weighted ledger used
when `f = |∇ω|` and `g = |u| |∇u| / |ω|` on a high-vorticity set. -/
theorem sq_integral_mul_le_integral_sq_mul_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hholder := integral_mul_le_sqrt_sq_integrals
    hf_nonneg hg_nonneg hf hg
  have hleft0 : 0 ≤ ∫ x, f x * g x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf_nonneg, hg_nonneg] with x hfx hgx
    exact mul_nonneg hfx hgx
  have hfSq0 : 0 ≤ ∫ x, f x ^ 2 ∂μ := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hgSq0 : 0 ≤ ∫ x, g x ^ 2 ∂μ := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hright0 : 0 ≤
      (∫ x, f x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ x, g x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
    positivity
  have hsquare := (sq_le_sq₀ hleft0 hright0).2 hholder
  have hfroot :
      ((∫ x, f x ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 =
        ∫ x, f x ^ 2 ∂μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hfSq0]
    norm_num
  have hgroot :
      ((∫ x, g x ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 =
        ∫ x, g x ^ 2 ∂μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hgSq0]
    norm_num
  rw [mul_pow, hfroot, hgroot] at hsquare
  exact hsquare

/-- Weighted direction-debit Cauchy ledger.  A nonnegative debit dominated pointwise by an
`L² × L²` product has its squared integral controlled by the product of the two quadratic
charges.  In the vorticity-direction application these charges are palinstrophy and
`∫ |u|² |∇u|² / |ω|²`. -/
theorem sq_integral_debit_le_sq_charges
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {debit f g : α → ℝ}
    (hdebit : Integrable debit μ)
    (hdebit_nonneg : 0 ≤ᵐ[μ] debit)
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hpoint : ∀ᵐ x ∂μ, debit x ≤ f x * g x) :
    (∫ x, debit x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hproduct : Integrable (fun x => f x * g x) μ :=
    hf.integrable_mul hg
  have hmono : (∫ x, debit x ∂μ) ≤ ∫ x, f x * g x ∂μ :=
    integral_mono_ae hdebit hproduct hpoint
  have hdebitIntegral0 : 0 ≤ ∫ x, debit x ∂μ :=
    integral_nonneg_of_ae hdebit_nonneg
  have hproductIntegral0 : 0 ≤ ∫ x, f x * g x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf_nonneg, hg_nonneg] with x hfx hgx
    exact mul_nonneg hfx hgx
  have hsquareMono : (∫ x, debit x ∂μ) ^ 2 ≤
      (∫ x, f x * g x ∂μ) ^ 2 :=
    (sq_le_sq₀ hdebitIntegral0 hproductIntegral0).2 hmono
  exact hsquareMono.trans <|
    sq_integral_mul_le_integral_sq_mul_integral_sq
      hf_nonneg hg_nonneg hf hg

/-- Two-channel version of the nonnegative Cauchy ledger.  It is used to keep angular and
radial director dissipation separate instead of merging them into total palinstrophy. -/
theorem sq_integral_debit_le_two_sq_charges
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {debit f₁ g₁ f₂ g₂ : α → ℝ}
    (hdebit : Integrable debit μ)
    (hdebit_nonneg : 0 ≤ᵐ[μ] debit)
    (hf₁_nonneg : 0 ≤ᵐ[μ] f₁) (hg₁_nonneg : 0 ≤ᵐ[μ] g₁)
    (hf₂_nonneg : 0 ≤ᵐ[μ] f₂) (hg₂_nonneg : 0 ≤ᵐ[μ] g₂)
    (hf₁ : MemLp f₁ 2 μ) (hg₁ : MemLp g₁ 2 μ)
    (hf₂ : MemLp f₂ 2 μ) (hg₂ : MemLp g₂ 2 μ)
    (hpoint : ∀ᵐ x ∂μ, debit x ≤ f₁ x * g₁ x + f₂ x * g₂ x) :
    (∫ x, debit x ∂μ) ^ 2 ≤
      2 * (∫ x, f₁ x ^ 2 ∂μ) * (∫ x, g₁ x ^ 2 ∂μ) +
      2 * (∫ x, f₂ x ^ 2 ∂μ) * (∫ x, g₂ x ^ 2 ∂μ) := by
  have hprod₁ : Integrable (fun x => f₁ x * g₁ x) μ := hf₁.integrable_mul hg₁
  have hprod₂ : Integrable (fun x => f₂ x * g₂ x) μ := hf₂.integrable_mul hg₂
  have hsum : Integrable (fun x => f₁ x * g₁ x + f₂ x * g₂ x) μ :=
    hprod₁.add hprod₂
  have hmono : (∫ x, debit x ∂μ) ≤
      ∫ x, f₁ x * g₁ x + f₂ x * g₂ x ∂μ :=
    integral_mono_ae hdebit hsum hpoint
  have hdebit0 : 0 ≤ ∫ x, debit x ∂μ :=
    integral_nonneg_of_ae hdebit_nonneg
  have hsum0 : 0 ≤ ∫ x, f₁ x * g₁ x + f₂ x * g₂ x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf₁_nonneg, hg₁_nonneg, hf₂_nonneg, hg₂_nonneg] with x hf1 hg1 hf2 hg2
    exact add_nonneg (mul_nonneg hf1 hg1) (mul_nonneg hf2 hg2)
  have hsquareMono := (sq_le_sq₀ hdebit0 hsum0).2 hmono
  rw [MeasureTheory.integral_add hprod₁ hprod₂] at hsquareMono
  have hcs₁ := sq_integral_mul_le_integral_sq_mul_integral_sq
    hf₁_nonneg hg₁_nonneg hf₁ hg₁
  have hcs₂ := sq_integral_mul_le_integral_sq_mul_integral_sq
    hf₂_nonneg hg₂_nonneg hf₂ hg₂
  have hsplit :
      ((∫ x, f₁ x * g₁ x ∂μ) + (∫ x, f₂ x * g₂ x ∂μ)) ^ 2 ≤
        2 * (∫ x, f₁ x * g₁ x ∂μ) ^ 2 +
          2 * (∫ x, f₂ x * g₂ x ∂μ) ^ 2 := by
    nlinarith [sq_nonneg
      ((∫ x, f₁ x * g₁ x ∂μ) - (∫ x, f₂ x * g₂ x ∂μ))]
  nlinarith

/-- On a region where a nonnegative amplitude `ρ` stays above a positive threshold, the
inverse-square weighted charge is controlled by the unweighted charge.  For
`F = |u|² |∇u|²`, `ρ = |ω|`, and `threshold = θ W`, this is the high-vorticity estimate
`∫ F / |ω|² ≤ (θ W)⁻² ∫ F`. -/
theorem integral_div_sq_le_inv_sq_mul_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ F : α → ℝ} {threshold : ℝ}
    (hthreshold : 0 < threshold)
    (hF : Integrable F μ)
    (hquotient : Integrable (fun x => F x / ρ x ^ 2) μ)
    (hF_nonneg : 0 ≤ᵐ[μ] F)
    (hρ : ∀ᵐ x ∂μ, threshold ≤ ρ x) :
    (∫ x, F x / ρ x ^ 2 ∂μ) ≤
      threshold⁻¹ ^ 2 * ∫ x, F x ∂μ := by
  have hscaled : Integrable (fun x => threshold⁻¹ ^ 2 * F x) μ :=
    hF.const_mul _
  calc
    (∫ x, F x / ρ x ^ 2 ∂μ) ≤
        ∫ x, threshold⁻¹ ^ 2 * F x ∂μ := by
      apply integral_mono_ae hquotient hscaled
      filter_upwards [hF_nonneg, hρ] with x hFx hρx
      have hρpos : 0 < ρ x := hthreshold.trans_le hρx
      calc
        F x / ρ x ^ 2 ≤ F x / threshold ^ 2 := by
          gcongr
        _ = threshold⁻¹ ^ 2 * F x := by
          rw [inv_pow]
          field_simp
    _ = threshold⁻¹ ^ 2 * ∫ x, F x ∂μ := by
      rw [integral_const_mul]

/-- Crude large-regularization bound for the nonsingular quotient.  This exposes the exact
tradeoff in the director method: replacing `ρ²` by `ρ²+c²` removes every zero, at the cost
of the fallback estimate `Q_c ≤ c⁻² ∫ F`. -/
theorem integral_div_add_sq_le_inv_sq_mul_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρSq F : α → ℝ} {c : ℝ}
    (hc : c ≠ 0)
    (hF : Integrable F μ)
    (hquotient : Integrable (fun x => F x / (ρSq x + c ^ 2)) μ)
    (hF_nonneg : 0 ≤ᵐ[μ] F)
    (hρ_nonneg : 0 ≤ᵐ[μ] ρSq) :
    (∫ x, F x / (ρSq x + c ^ 2) ∂μ) ≤
      c⁻¹ ^ 2 * ∫ x, F x ∂μ := by
  have hscaled : Integrable (fun x => c⁻¹ ^ 2 * F x) μ :=
    hF.const_mul _
  calc
    (∫ x, F x / (ρSq x + c ^ 2) ∂μ) ≤
        ∫ x, c⁻¹ ^ 2 * F x ∂μ := by
      apply integral_mono_ae hquotient hscaled
      filter_upwards [hF_nonneg, hρ_nonneg] with x hFx hρx
      change (0 : ℝ) ≤ F x at hFx
      change (0 : ℝ) ≤ ρSq x at hρx
      have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
      calc
        F x / (ρSq x + c ^ 2) ≤ F x / c ^ 2 := by
          gcongr
          linarith
        _ = c⁻¹ ^ 2 * F x := by
          rw [inv_pow]
          field_simp
    _ = c⁻¹ ^ 2 * ∫ x, F x ∂μ := by
      rw [integral_const_mul]

/-- Measure-theoretic weighted centering identity for a scalar component. -/
theorem integral_weighted_centering_identity
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (weight field : α → ℝ) (frame : ℝ)
    (hweight : Integrable weight μ)
    (hmoment : Integrable (fun x => weight x * field x) μ)
    (hraw : Integrable (fun x => weight x * field x ^ 2) μ)
    (hmass : (∫ x, weight x ∂μ) ≠ 0) :
    (∫ x, weight x * (field x - frame) ^ 2 ∂μ) =
      (∫ x, weight x * field x ^ 2 ∂μ) -
        (∫ x, weight x * field x ∂μ) ^ 2 / (∫ x, weight x ∂μ) +
        (∫ x, weight x ∂μ) *
          (frame - (∫ x, weight x * field x ∂μ) /
            (∫ x, weight x ∂μ)) ^ 2 := by
  have hexpand : (∫ x, weight x * (field x - frame) ^ 2 ∂μ) =
      (∫ x, weight x * field x ^ 2 ∂μ) -
        2 * frame * (∫ x, weight x * field x ∂μ) +
          frame ^ 2 * (∫ x, weight x ∂μ) := by
    calc
      (∫ x, weight x * (field x - frame) ^ 2 ∂μ) =
          ∫ x, (weight x * field x ^ 2 -
            (2 * frame) * (weight x * field x)) + frame ^ 2 * weight x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = (∫ x, weight x * field x ^ 2 -
          (2 * frame) * (weight x * field x) ∂μ) +
          ∫ x, frame ^ 2 * weight x ∂μ := by
        exact MeasureTheory.integral_add
          (f := fun x => weight x * field x ^ 2 -
            (2 * frame) * (weight x * field x))
          (g := fun x => frame ^ 2 * weight x)
          (hraw.sub (hmoment.const_mul _)) (hweight.const_mul _)
      _ = ((∫ x, weight x * field x ^ 2 ∂μ) -
          ∫ x, (2 * frame) * (weight x * field x) ∂μ) +
          ∫ x, frame ^ 2 * weight x ∂μ := by
        rw [MeasureTheory.integral_sub hraw (hmoment.const_mul _)]
      _ = (∫ x, weight x * field x ^ 2 ∂μ) -
          2 * frame * (∫ x, weight x * field x ∂μ) +
            frame ^ 2 * (∫ x, weight x ∂μ) := by
        rw [integral_const_mul, integral_const_mul]
  rw [hexpand]
  exact weighted_centering_identity
    (∫ x, weight x * field x ^ 2 ∂μ)
    (∫ x, weight x * field x ∂μ)
    (∫ x, weight x ∂μ) frame hmass

/-- The quotient-weighted scalar mean minimizes the integrated centered charge. -/
theorem integral_weighted_centering_minimum
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (weight field : α → ℝ) (frame : ℝ)
    (hweight : Integrable weight μ)
    (hmoment : Integrable (fun x => weight x * field x) μ)
    (hraw : Integrable (fun x => weight x * field x ^ 2) μ)
    (hmass : 0 < ∫ x, weight x ∂μ) :
    (∫ x, weight x * field x ^ 2 ∂μ) -
        (∫ x, weight x * field x ∂μ) ^ 2 / (∫ x, weight x ∂μ) ≤
      ∫ x, weight x * (field x - frame) ^ 2 ∂μ := by
  rw [integral_weighted_centering_identity
    weight field frame hweight hmoment hraw hmass.ne']
  exact le_add_of_nonneg_right (mul_nonneg hmass.le (sq_nonneg _))

/-- Low/high amplitude split for the regularized quotient.  The singular inverse-vorticity
charge is required only on the high set; the low set pays the explicit `c⁻²` factor. -/
theorem integral_regularized_quotient_le_low_high
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ρSq F : α → ℝ) (c : ℝ) (hc : c ≠ 0)
    (low : Set α) (hlow : low = {x | ρSq x < c ^ 2})
    (hlowMeasurable : MeasurableSet low)
    (hF : Integrable F μ)
    (hquotient : Integrable (fun x => F x / (ρSq x + c ^ 2)) μ)
    (hhigh : IntegrableOn (fun x => F x / ρSq x) lowᶜ μ)
    (hF_nonneg : ∀ x, 0 ≤ F x)
    (hρ_nonneg : ∀ x, 0 ≤ ρSq x) :
    (∫ x, F x / (ρSq x + c ^ 2) ∂μ) ≤
      c⁻¹ ^ 2 * (∫ x in low, F x ∂μ) +
        ∫ x in lowᶜ, F x / ρSq x ∂μ := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hlowBound :
      (∫ x in low, F x / (ρSq x + c ^ 2) ∂μ) ≤
        c⁻¹ ^ 2 * ∫ x in low, F x ∂μ := by
    calc
      (∫ x in low, F x / (ρSq x + c ^ 2) ∂μ) ≤
          ∫ x in low, c⁻¹ ^ 2 * F x ∂μ := by
        apply integral_mono_ae hquotient.integrableOn (hF.const_mul _).integrableOn
        exact Filter.Eventually.of_forall fun x => by
          calc
            F x / (ρSq x + c ^ 2) ≤ F x / c ^ 2 := by
              exact div_le_div_of_nonneg_left (hF_nonneg x) hc2
                (le_add_of_nonneg_left (hρ_nonneg x))
            _ = c⁻¹ ^ 2 * F x := by
              rw [inv_pow]
              field_simp
      _ = c⁻¹ ^ 2 * ∫ x in low, F x ∂μ := by
        rw [integral_const_mul]
  have hhighBound :
      (∫ x in lowᶜ, F x / (ρSq x + c ^ 2) ∂μ) ≤
        ∫ x in lowᶜ, F x / ρSq x ∂μ := by
    apply integral_mono_ae hquotient.integrableOn hhigh
    filter_upwards [ae_restrict_mem hlowMeasurable.compl] with x hx
    have hxHigh : c ^ 2 ≤ ρSq x := by
      rw [hlow] at hx
      simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] using hx
    calc
      F x / (ρSq x + c ^ 2) ≤ F x / ρSq x := by
        exact div_le_div_of_nonneg_left (hF_nonneg x)
          (hc2.trans_le hxHigh) (le_add_of_nonneg_right hc2.le)
      _ = F x / ρSq x := rfl
  rw [← MeasureTheory.integral_add_compl hlowMeasurable hquotient]
  exact add_le_add hlowBound hhighBound

/-- The cancellation-preserving scalar kernel still has a global `c⁻²` maximum, attained
when `ρ² = c²`.  Thus the sharper director derivative improves the low-vorticity geometry but
does not by itself remove the regularization obstruction. -/
theorem regularized_sharp_kernel_le_inv_four_sq
    (rhoSq c : ℝ) (hrho : 0 ≤ rhoSq) (hc : c ≠ 0) :
    rhoSq / (rhoSq + c ^ 2) ^ 2 ≤ 1 / (4 * c ^ 2) := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hden : 0 < rhoSq + c ^ 2 := add_pos_of_nonneg_of_pos hrho hc2
  rw [div_le_div_iff₀ (sq_pos_of_pos hden) (mul_pos (by norm_num) hc2)]
  nlinarith [sq_nonneg (rhoSq - c ^ 2)]

/-- The radial-amplitude kernel from the exact Frobenius director differential is smaller:
its global maximum is `27 / (256 c²)`, attained at `ρ² = c²/3`, and it decays cubically
in `ρ²` above the regularization scale. -/
theorem regularized_radial_kernel_le_twentyseven_div_twofiftysix_sq
    (rhoSq c : ℝ) (hrho : 0 ≤ rhoSq) (hc : c ≠ 0) :
    rhoSq * c ^ 4 / (rhoSq + c ^ 2) ^ 4 ≤
      27 / (256 * c ^ 2) := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hden : 0 < rhoSq + c ^ 2 := add_pos_of_nonneg_of_pos hrho hc2
  have hpositive : 0 ≤
      (3 * rhoSq - c ^ 2) ^ 2 *
        (3 * rhoSq ^ 2 + 14 * rhoSq * c ^ 2 + 27 * c ^ 4) := by
    apply mul_nonneg (sq_nonneg _)
    positivity
  rw [div_le_div_iff₀ (pow_pos hden 4) (mul_pos (by norm_num) hc2)]
  nlinarith

/-- Low/high split for the cancellation-preserving quotient.  On the low set it pays the
amplitude-sensitive charge `F ρ² / c⁴`, rather than the coarse `F / c²`; only the high set
retains the inverse-vorticity charge `F / ρ²`. -/
theorem integral_regularized_sharp_quotient_le_low_high
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ρSq F : α → ℝ) (c : ℝ) (hc : c ≠ 0)
    (low : Set α) (hlow : low = {x | ρSq x < c ^ 2})
    (hlowMeasurable : MeasurableSet low)
    (hquotient : Integrable
      (fun x => F x * ρSq x / (ρSq x + c ^ 2) ^ 2) μ)
    (hlowCharge : IntegrableOn (fun x => F x * ρSq x / c ^ 4) low μ)
    (hhighCharge : IntegrableOn (fun x => F x / ρSq x) lowᶜ μ)
    (hF_nonneg : ∀ x, 0 ≤ F x)
    (hρ_nonneg : ∀ x, 0 ≤ ρSq x) :
    (∫ x, F x * ρSq x / (ρSq x + c ^ 2) ^ 2 ∂μ) ≤
      (∫ x in low, F x * ρSq x / c ^ 4 ∂μ) +
        ∫ x in lowᶜ, F x / ρSq x ∂μ := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hlowBound :
      (∫ x in low, F x * ρSq x / (ρSq x + c ^ 2) ^ 2 ∂μ) ≤
        ∫ x in low, F x * ρSq x / c ^ 4 ∂μ := by
    apply integral_mono_ae hquotient.integrableOn hlowCharge
    exact Filter.Eventually.of_forall fun x => by
      have hrho := hρ_nonneg x
      have hden0 : 0 ≤ ρSq x + c ^ 2 := add_nonneg hrho hc2.le
      have hsq : c ^ 4 ≤ (ρSq x + c ^ 2) ^ 2 := by
        have hsquares := (sq_le_sq₀ hc2.le hden0).2
          (le_add_of_nonneg_left hrho)
        simpa [show c ^ 4 = (c ^ 2) ^ 2 by ring] using hsquares
      exact div_le_div_of_nonneg_left
        (mul_nonneg (hF_nonneg x) hrho) (by positivity) hsq
  have hhighBound :
      (∫ x in lowᶜ, F x * ρSq x / (ρSq x + c ^ 2) ^ 2 ∂μ) ≤
        ∫ x in lowᶜ, F x / ρSq x ∂μ := by
    apply integral_mono_ae hquotient.integrableOn hhighCharge
    filter_upwards [ae_restrict_mem hlowMeasurable.compl] with x hx
    have hxHigh : c ^ 2 ≤ ρSq x := by
      rw [hlow] at hx
      simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] using hx
    have hrhoPos : 0 < ρSq x := hc2.trans_le hxHigh
    have hden0 : 0 ≤ ρSq x + c ^ 2 :=
      add_nonneg (hρ_nonneg x) hc2.le
    have hsq : ρSq x ^ 2 ≤ (ρSq x + c ^ 2) ^ 2 :=
      (sq_le_sq₀ (hρ_nonneg x) hden0).2 (le_add_of_nonneg_right hc2.le)
    calc
      F x * ρSq x / (ρSq x + c ^ 2) ^ 2 ≤
          F x * ρSq x / ρSq x ^ 2 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (hF_nonneg x) (hρ_nonneg x)) (sq_pos_of_pos hrhoPos) hsq
      _ = F x / ρSq x := by
        field_simp [hrhoPos.ne']
  rw [← MeasureTheory.integral_add_compl hlowMeasurable hquotient]
  exact add_le_add hlowBound hhighBound

/-- Flux-measure Cauchy--Schwarz ledger.  If every curve carries a square-root product of
nonnegative energy and direction charges at least `floor`, then the total curve measure times
`floor` is bounded by the geometric mean of the integrated charges.  This is the
measure-theoretic core of the closed persistent-line estimate in `DYNAMICS.md`. -/
theorem flux_measure_le_sqrt_charges
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {energy direction : α → ℝ} {floor : ℝ}
    (henergy : Integrable energy μ) (hdirection : Integrable direction μ)
    (henergy_nonneg : 0 ≤ᵐ[μ] energy) (hdirection_nonneg : 0 ≤ᵐ[μ] direction)
    (hline : ∀ᵐ γ ∂μ,
      floor ≤ energy γ ^ ((1 : ℝ) / 2) * direction γ ^ ((1 : ℝ) / 2)) :
    floor * μ.real Set.univ ≤
      (∫ γ, energy γ ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ γ, direction γ ∂μ) ^ ((1 : ℝ) / 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have he_mem : MemLp energy 1 μ := memLp_one_iff_integrable.mpr henergy
  have hd_mem : MemLp direction 1 μ := memLp_one_iff_integrable.mpr hdirection
  have hse_mem : MemLp (fun γ => ‖energy γ‖ ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    convert he_mem.norm_rpow_div (ENNReal.ofReal ((1 : ℝ) / 2)) using 1
    · norm_num
    · simp [one_div]
  have hsd_mem : MemLp (fun γ => ‖direction γ‖ ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    convert hd_mem.norm_rpow_div (ENNReal.ofReal ((1 : ℝ) / 2)) using 1
    · norm_num
    · simp [one_div]
  have hse_mem_two : MemLp (fun γ => ‖energy γ‖ ^ ((1 : ℝ) / 2))
      (2 : ENNReal) μ := by simpa using hse_mem
  have hsd_mem_two : MemLp (fun γ => ‖direction γ‖ ^ ((1 : ℝ) / 2))
      (2 : ENNReal) μ := by simpa using hsd_mem
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := fun γ => ‖energy γ‖ ^ ((1 : ℝ) / 2))
    (g := fun γ => ‖direction γ‖ ^ ((1 : ℝ) / 2))
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    hse_mem hsd_mem
  have he_norm : (fun γ => ‖energy γ‖) =ᵐ[μ] energy := by
    filter_upwards [henergy_nonneg] with γ hγ
    exact Real.norm_of_nonneg hγ
  have hd_norm : (fun γ => ‖direction γ‖) =ᵐ[μ] direction := by
    filter_upwards [hdirection_nonneg] with γ hγ
    exact Real.norm_of_nonneg hγ
  have hlower : floor * μ.real Set.univ ≤
      ∫ γ, ‖energy γ‖ ^ ((1 : ℝ) / 2) * ‖direction γ‖ ^ ((1 : ℝ) / 2) ∂μ := by
    calc
      floor * μ.real Set.univ = ∫ _ : α, floor ∂μ := by
        rw [integral_const]
        simp only [Measure.real, smul_eq_mul]
        ring
      _ ≤ ∫ γ, ‖energy γ‖ ^ ((1 : ℝ) / 2) *
          ‖direction γ‖ ^ ((1 : ℝ) / 2) ∂μ := by
        apply integral_mono_ae (integrable_const floor)
          (hse_mem_two.integrable_mul hsd_mem_two)
        filter_upwards [hline, henergy_nonneg, hdirection_nonneg] with γ hγ heγ hdγ
        change floor ≤ ‖energy γ‖ ^ ((1 : ℝ) / 2) *
          ‖direction γ‖ ^ ((1 : ℝ) / 2)
        rw [Real.norm_of_nonneg heγ, Real.norm_of_nonneg hdγ]
        exact hγ
  calc
    floor * μ.real Set.univ ≤
        ∫ γ, ‖energy γ‖ ^ ((1 : ℝ) / 2) *
          ‖direction γ‖ ^ ((1 : ℝ) / 2) ∂μ := hlower
    _ ≤ (∫ γ, (‖energy γ‖ ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
          (∫ γ, (‖direction γ‖ ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) ∂μ) ^
            ((1 : ℝ) / 2) := by
      simpa using hholder
    _ = (∫ γ, energy γ ∂μ) ^ ((1 : ℝ) / 2) *
          (∫ γ, direction γ ∂μ) ^ ((1 : ℝ) / 2) := by
      congr 2
      · apply integral_congr_ae
        filter_upwards [he_norm] with γ hγ
        rw [← hγ, ← Real.rpow_mul (norm_nonneg _)]
        norm_num
      · apply integral_congr_ae
        filter_upwards [hd_norm] with γ hγ
        rw [← hγ, ← Real.rpow_mul (norm_nonneg _)]
        norm_num

/-- Curve-family signed-error ledger.  A pointwise line error bounded by the square root of a
coherence charge times a field charge integrates to the geometric mean of the total charges.
This is the global Cauchy step for the ballistic line-pairing error in `DYNAMICS.md`. -/
theorem norm_integral_signedError_le_sqrt_charges
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {signedError coherence fieldCharge : α → ℝ}
    (herror : Integrable signedError μ)
    (hcoherence : Integrable coherence μ) (hfield : Integrable fieldCharge μ)
    (hcoherence_nonneg : 0 ≤ᵐ[μ] coherence)
    (hfield_nonneg : 0 ≤ᵐ[μ] fieldCharge)
    (hline : ∀ᵐ γ ∂μ,
      |signedError γ| ≤
        coherence γ ^ ((1 : ℝ) / 2) * fieldCharge γ ^ ((1 : ℝ) / 2)) :
    ‖∫ γ, signedError γ ∂μ‖ ≤
      (∫ γ, coherence γ ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ γ, fieldCharge γ ∂μ) ^ ((1 : ℝ) / 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hc_mem : MemLp coherence 1 μ := memLp_one_iff_integrable.mpr hcoherence
  have hf_mem : MemLp fieldCharge 1 μ := memLp_one_iff_integrable.mpr hfield
  have hsc_mem : MemLp (fun γ => ‖coherence γ‖ ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    convert hc_mem.norm_rpow_div (ENNReal.ofReal ((1 : ℝ) / 2)) using 1
    · norm_num
    · simp [one_div]
  have hsf_mem : MemLp (fun γ => ‖fieldCharge γ‖ ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    convert hf_mem.norm_rpow_div (ENNReal.ofReal ((1 : ℝ) / 2)) using 1
    · norm_num
    · simp [one_div]
  have hsc_mem_two : MemLp (fun γ => ‖coherence γ‖ ^ ((1 : ℝ) / 2))
      (2 : ENNReal) μ := by simpa using hsc_mem
  have hsf_mem_two : MemLp (fun γ => ‖fieldCharge γ‖ ^ ((1 : ℝ) / 2))
      (2 : ENNReal) μ := by simpa using hsf_mem
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := fun γ => ‖coherence γ‖ ^ ((1 : ℝ) / 2))
    (g := fun γ => ‖fieldCharge γ‖ ^ ((1 : ℝ) / 2))
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    hsc_mem hsf_mem
  have hc_norm : (fun γ => ‖coherence γ‖) =ᵐ[μ] coherence := by
    filter_upwards [hcoherence_nonneg] with γ hγ
    exact Real.norm_of_nonneg hγ
  have hf_norm : (fun γ => ‖fieldCharge γ‖) =ᵐ[μ] fieldCharge := by
    filter_upwards [hfield_nonneg] with γ hγ
    exact Real.norm_of_nonneg hγ
  calc
    ‖∫ γ, signedError γ ∂μ‖ ≤ ∫ γ, ‖signedError γ‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ γ, ‖coherence γ‖ ^ ((1 : ℝ) / 2) *
        ‖fieldCharge γ‖ ^ ((1 : ℝ) / 2) ∂μ := by
      apply integral_mono_ae herror.norm
        (hsc_mem_two.integrable_mul hsf_mem_two)
      filter_upwards [hline, hcoherence_nonneg, hfield_nonneg] with γ hγ hcγ hfγ
      change |signedError γ| ≤ ‖coherence γ‖ ^ ((1 : ℝ) / 2) *
        ‖fieldCharge γ‖ ^ ((1 : ℝ) / 2)
      rw [Real.norm_of_nonneg hcγ, Real.norm_of_nonneg hfγ]
      exact hγ
    _ ≤ (∫ γ, (‖coherence γ‖ ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) ∂μ) ^
          ((1 : ℝ) / 2) *
        (∫ γ, (‖fieldCharge γ‖ ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) ∂μ) ^
          ((1 : ℝ) / 2) := by
      simpa using hholder
    _ = (∫ γ, coherence γ ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ γ, fieldCharge γ ∂μ) ^ ((1 : ℝ) / 2) := by
      congr 2
      · apply integral_congr_ae
        filter_upwards [hc_norm] with γ hγ
        rw [← hγ, ← Real.rpow_mul (norm_nonneg _)]
        norm_num
      · apply integral_congr_ae
        filter_upwards [hf_norm] with γ hγ
        rw [← hγ, ← Real.rpow_mul (norm_nonneg _)]
        norm_num

/-- Long-line ledger.  If every curve carries energy charge at least `floor`, then its total
flux measure is bounded by the integrated energy divided by that floor.  The multiplication
form avoids a division or a positivity side condition. -/
theorem floor_mul_measure_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {energy : α → ℝ} {floor : ℝ}
    (henergy : Integrable energy μ)
    (hline : ∀ᵐ γ ∂μ, floor ≤ energy γ) :
    floor * μ.real Set.univ ≤ ∫ γ, energy γ ∂μ := by
  calc
    floor * μ.real Set.univ = ∫ _ : α, floor ∂μ := by
      rw [integral_const]
      simp only [Measure.real, smul_eq_mul]
      ring
    _ ≤ ∫ γ, energy γ ∂μ :=
      integral_mono_ae (integrable_const floor) henergy hline

/-- Hölder's inequality in the exact exponents used to integrate the enstrophy
contribution to the strain budget. -/
theorem integral_rpow_five_six_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {Ω : α → ℝ} (hΩ : Integrable Ω μ) (hΩ_nonneg : 0 ≤ᵐ[μ] Ω) :
    (∫ t, Ω t ^ ((5 : ℝ) / 6) ∂μ) ≤
      (∫ t, Ω t ∂μ) ^ ((5 : ℝ) / 6) * μ.real Set.univ ^ ((1 : ℝ) / 6) := by
  have hpq : ((6 : ℝ) / 5).HolderConjugate 6 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hΩ_mem : MemLp Ω 1 μ := memLp_one_iff_integrable.mpr hΩ
  have hexp : ENNReal.ofReal ((6 : ℝ) / 5) = (ENNReal.ofReal ((5 : ℝ) / 6))⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (5 : ℝ) / 6)]
    norm_num
  have hpow_mem : MemLp (fun t => ‖Ω t‖ ^ ((5 : ℝ) / 6)) (ENNReal.ofReal ((6 : ℝ) / 5)) μ := by
    convert hΩ_mem.norm_rpow_div (ENNReal.ofReal ((5 : ℝ) / 6)) using 1
    · norm_num
    · simpa [one_div] using hexp
  have hone_mem : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (6 : ℝ)) μ :=
    memLp_const 1
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := fun t => ‖Ω t‖ ^ ((5 : ℝ) / 6)) (g := fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hpow_mem hone_mem
  have hnorm : (fun t => ‖Ω t‖) =ᵐ[μ] Ω := by
    filter_upwards [hΩ_nonneg] with t ht
    exact Real.norm_of_nonneg ht
  calc
    (∫ t, Ω t ^ ((5 : ℝ) / 6) ∂μ)
        = ∫ t, ‖Ω t‖ ^ ((5 : ℝ) / 6) * 1 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hΩ_nonneg] with t ht
            rw [Real.norm_of_nonneg ht, mul_one]
    _ ≤ (∫ t, (‖Ω t‖ ^ ((5 : ℝ) / 6)) ^ ((6 : ℝ) / 5) ∂μ) ^ ((5 : ℝ) / 6) *
          (∫ _ : α, (1 : ℝ) ^ (6 : ℝ) ∂μ) ^ ((1 : ℝ) / 6) := by
            simpa using hholder
    _ = (∫ t, Ω t ∂μ) ^ ((5 : ℝ) / 6) * μ.real Set.univ ^ ((1 : ℝ) / 6) := by
          congr 2
          · apply integral_congr_ae
            filter_upwards [hnorm] with t ht
            rw [← ht, ← Real.rpow_mul (norm_nonneg _)]
            norm_num
          · simp

/-- The finite-time form used in the paper: an `L¹` enstrophy budget `∫ Ω ≤ B`
implies the claimed `T^(1/6)` bound. -/
theorem integral_Icc_rpow_five_six_le
    {Ω : ℝ → ℝ} {T B : ℝ} (hT : 0 ≤ T)
    (hΩ : IntegrableOn Ω (Set.Icc 0 T))
    (hΩ_nonneg : 0 ≤ᵐ[volume.restrict (Set.Icc 0 T)] Ω)
    (hbudget : (∫ t in Set.Icc 0 T, Ω t) ≤ B) :
    (∫ t in Set.Icc 0 T, Ω t ^ ((5 : ℝ) / 6)) ≤
      B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) := by
  have hholder := integral_rpow_five_six_le
    (μ := volume.restrict (Set.Icc 0 T)) hΩ hΩ_nonneg
  have hholder' :
      (∫ t in Set.Icc 0 T, Ω t ^ ((5 : ℝ) / 6)) ≤
        (∫ t in Set.Icc 0 T, Ω t) ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) := by
    simpa [Measure.real, Real.volume_Icc, hT] using hholder
  have hint_nonneg : 0 ≤ ∫ t in Set.Icc 0 T, Ω t := integral_nonneg_of_ae hΩ_nonneg
  have hpow :
      (∫ t in Set.Icc 0 T, Ω t) ^ ((5 : ℝ) / 6) ≤ B ^ ((5 : ℝ) / 6) :=
    Real.rpow_le_rpow hint_nonneg hbudget (by norm_num)
  exact hholder'.trans (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hT _))

/-- A continuous pointwise strain estimate closes to the finite-time integrated
budget used by the maximum principle.  The three terms represent the
subcritical `Ω^(5/6)` contribution, the linear enstrophy contribution, and a
bounded background contribution. -/
theorem intervalIntegral_strain_budget_le
    {Ω γ : ℝ → ℝ} {T B C5 C1 C0 : ℝ}
    (hT : 0 ≤ T) (hC5 : 0 ≤ C5) (hC1 : 0 ≤ C1)
    (hΩ_cont : Continuous Ω) (hγ_cont : Continuous γ)
    (hΩ_nonneg : ∀ t, 0 ≤ Ω t)
    (hbudget : (∫ t in Set.Icc 0 T, Ω t) ≤ B)
    (hγ_bound : ∀ t ∈ Set.Icc 0 T,
      γ t ≤ C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0) :
    (∫ t in (0 : ℝ)..T, γ t) ≤
      C5 * B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) + C1 * B + C0 * T := by
  have hΩ_integrableOn : IntegrableOn Ω (Set.Icc 0 T) :=
    hΩ_cont.integrableOn_Icc
  have hΩ_ae : 0 ≤ᵐ[volume.restrict (Set.Icc 0 T)] Ω :=
    Filter.Eventually.of_forall hΩ_nonneg
  have hholder_set := integral_Icc_rpow_five_six_le
    hT hΩ_integrableOn hΩ_ae hbudget
  have hholder_interval :
      (∫ t in (0 : ℝ)..T, Ω t ^ ((5 : ℝ) / 6)) ≤
        B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) := by
    rw [intervalIntegral.integral_of_le hT,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hholder_set
  have hΩ_interval : (∫ t in (0 : ℝ)..T, Ω t) ≤ B := by
    rw [intervalIntegral.integral_of_le hT,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hbudget
  have hpow_cont : Continuous (fun t => Ω t ^ ((5 : ℝ) / 6)) :=
    hΩ_cont.rpow_const (fun _ => Or.inr (by norm_num))
  have h5_cont : Continuous (fun t => C5 * Ω t ^ ((5 : ℝ) / 6)) := by
    fun_prop
  have h1_cont : Continuous (fun t => C1 * Ω t) := by
    fun_prop
  have h0_cont : Continuous (fun _ : ℝ => C0) := continuous_const
  have hright_cont : Continuous
      (fun t => C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0) := by
    fun_prop
  have hmono :
      (∫ t in (0 : ℝ)..T, γ t) ≤
        ∫ t in (0 : ℝ)..T,
          (C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0) :=
    intervalIntegral.integral_mono_on hT
      (hγ_cont.intervalIntegrable 0 T)
      (hright_cont.intervalIntegrable 0 T) hγ_bound
  calc
    (∫ t in (0 : ℝ)..T, γ t)
        ≤ ∫ t in (0 : ℝ)..T,
            (C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0) := hmono
    _ = C5 * (∫ t in (0 : ℝ)..T, Ω t ^ ((5 : ℝ) / 6)) +
          C1 * (∫ t in (0 : ℝ)..T, Ω t) + C0 * T := by
          calc
            (∫ t in (0 : ℝ)..T,
                (C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0)) =
                (∫ t in (0 : ℝ)..T,
                  (C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t)) +
                ∫ _ in (0 : ℝ)..T, C0 := by
                  simpa only [Pi.add_apply] using
                    intervalIntegral.integral_add
                      ((h5_cont.add h1_cont).intervalIntegrable
                        (μ := volume) 0 T)
                      (h0_cont.intervalIntegrable (μ := volume) 0 T)
            _ = ((∫ t in (0 : ℝ)..T, C5 * Ω t ^ ((5 : ℝ) / 6)) +
                  ∫ t in (0 : ℝ)..T, C1 * Ω t) +
                ∫ _ in (0 : ℝ)..T, C0 := by
                  congr 1
                  simpa only [Pi.add_apply] using
                    intervalIntegral.integral_add
                      (h5_cont.intervalIntegrable (μ := volume) 0 T)
                      (h1_cont.intervalIntegrable (μ := volume) 0 T)
            _ = C5 * (∫ t in (0 : ℝ)..T, Ω t ^ ((5 : ℝ) / 6)) +
                  C1 * (∫ t in (0 : ℝ)..T, Ω t) + C0 * T := by
                  simp only [intervalIntegral.integral_const_mul,
                    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
                  ring
    _ ≤ C5 * (B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6)) +
          C1 * B + C0 * T := by
          gcongr
    _ = C5 * B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) + C1 * B + C0 * T := by
          ring
