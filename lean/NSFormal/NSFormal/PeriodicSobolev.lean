import NSFormal.DivCurl
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# Periodic Poincare and Sobolev estimates

This file builds the periodic Sobolev input needed by the spatial interpolation argument.
The first layer is deliberately elementary: finite-measure Cauchy--Schwarz, the fundamental
theorem of calculus on an interval, and the existence of a zero for a continuous mean-zero
function.  These lemmas use the concrete Lebesgue interval and will be tensorized on the
three-torus below.
-/

open Filter Function MeasureTheory Set
open scoped Interval

noncomputable section

/-- A continuous real function belongs to every `L^p` on an unordered bounded interval. -/
theorem continuous_memLp_restrict_uIoc
    (f : ℝ → ℝ) (a b : ℝ) (p : ENNReal) (hf : Continuous f) :
    MemLp f p (volume.restrict (Ι a b)) := by
  let _ : IsFiniteMeasure (volume.restrict (Ι a b)) :=
    ⟨by simp [Real.volume_uIoc]⟩
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  exact hC x (uIoc_subset_uIcc hx)

/-- Cauchy--Schwarz for the integral of a signed scalar function on a finite measure space,
written without square roots. -/
theorem sq_integral_le_measure_mul_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by
  have hCauchy := sq_integral_mul_le_integral_sq_mul_integral_sq
    (μ := μ) (f := fun x => |f x|) (g := fun _ => (1 : ℝ))
    (Eventually.of_forall fun _ => abs_nonneg _)
    (Eventually.of_forall fun _ => zero_le_one) hf.abs (memLp_const 1)
  have hAbsIntegral0 : 0 ≤ ∫ x, |f x| ∂μ :=
    integral_nonneg fun _ => abs_nonneg _
  have hSquare :
      (∫ x, f x ∂μ) ^ 2 ≤ (∫ x, |f x| ∂μ) ^ 2 := by
    rw [← sq_abs (∫ x, f x ∂μ)]
    exact (sq_le_sq₀ (abs_nonneg _) hAbsIntegral0).2 abs_integral_le_integral_abs
  calc
    (∫ x, f x ∂μ) ^ 2 ≤ (∫ x, |f x| ∂μ) ^ 2 := hSquare
    _ ≤ μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by
      simpa [sq_abs, mul_comm] using hCauchy

/-- Unordered-interval Cauchy--Schwarz.  The absolute values make the statement independent
of the orientation of the interval. -/
theorem intervalIntegral_sq_le_abs_sub_mul_abs_intervalIntegral_sq
    (f : ℝ → ℝ) (a b : ℝ) (hf : Continuous f) :
    (∫ x in a..b, f x) ^ 2 ≤
      |b - a| * |∫ x in a..b, f x ^ 2| := by
  let _ : IsFiniteMeasure (volume.restrict (Ι a b)) :=
    ⟨by simp [Real.volume_uIoc]⟩
  have h := sq_integral_le_measure_mul_integral_sq
    (μ := volume.restrict (Ι a b)) f
    (continuous_memLp_restrict_uIoc f a b 2 hf)
  have hmeasure : (volume.restrict (Ι a b)).real Set.univ = |b - a| := by
    simp [measureReal_def, Real.volume_uIoc]
  have hleft :
      (∫ x in a..b, f x) ^ 2 = (∫ x in Ι a b, f x) ^ 2 := by
    have habs := intervalIntegral.abs_integral_eq_abs_integral_uIoc
      (a := a) (b := b) (μ := volume) f
    calc
      (∫ x in a..b, f x) ^ 2 = |∫ x in a..b, f x| ^ 2 :=
        (sq_abs (∫ x in a..b, f x)).symm
      _ = |∫ x in Ι a b, f x| ^ 2 := congrArg (fun z : ℝ => z ^ 2) habs
      _ = (∫ x in Ι a b, f x) ^ 2 := sq_abs _
  have hsquareNonneg : 0 ≤ ∫ x in Ι a b, f x ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hright :
      (∫ x in Ι a b, f x ^ 2) = |∫ x in a..b, f x ^ 2| := by
    rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
    exact (abs_of_nonneg hsquareNonneg).symm
  rw [hmeasure, hright] at h
  rw [hleft]
  exact h

/-- Fundamental-theorem-of-calculus estimate between any two points of an interval.  This is
the pointwise engine of the one-dimensional Poincare inequality. -/
theorem function_sub_sq_le_intervalLength_mul_integral_deriv_sq
    (f : ℝ → ℝ) {a b c x : ℝ} (hab : a ≤ b)
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) (hf : ContDiff ℝ 1 f) :
    (f x - f c) ^ 2 ≤ (b - a) * ∫ y in a..b, deriv f y ^ 2 := by
  have hderiv : Continuous (deriv f) := hf.continuous_deriv_one
  have hFTC : (∫ y in c..x, deriv f y) = f x - f c :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc hf.contDiffOn
  have hCauchy := intervalIntegral_sq_le_abs_sub_mul_abs_intervalIntegral_sq
    (deriv f) c x hderiv
  rw [hFTC] at hCauchy
  have hlength : |x - c| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, hx.1, hx.2]
  have hc' : c ∈ [[a, b]] := by simpa [uIcc_of_le hab] using hc
  have hx' : x ∈ [[a, b]] := by simpa [uIcc_of_le hab] using hx
  have hsubset : Ι c x ⊆ Ι a b :=
    uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hc' hx')
  have hderivSqIntervalIntegrable :
      IntervalIntegrable (fun y => deriv f y ^ 2) volume a b :=
    (hderiv.pow 2).continuousOn.intervalIntegrable
  have hmonoAbs := intervalIntegral.abs_integral_mono_interval
    (μ := volume) (f := fun y => deriv f y ^ 2)
    (a := c) (b := x) (c := a) (d := b) hsubset
    (Eventually.of_forall fun _ => sq_nonneg _)
    hderivSqIntervalIntegrable
  have hbigNonneg : 0 ≤ ∫ y in a..b, deriv f y ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab fun _ => sq_nonneg _
  have hmono :
      |∫ y in c..x, deriv f y ^ 2| ≤ ∫ y in a..b, deriv f y ^ 2 := by
    simpa [abs_of_nonneg hbigNonneg] using hmonoAbs
  exact hCauchy.trans <|
    mul_le_mul hlength hmono (abs_nonneg _) (sub_nonneg.mpr hab)

/-- A continuous function with zero integral on a nondegenerate interval vanishes somewhere
on that interval. -/
theorem exists_zero_of_intervalIntegral_eq_zero
    (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : Continuous f)
    (hmean : (∫ x in a..b, f x) = 0) :
    ∃ c ∈ Icc a b, f c = 0 := by
  obtain ⟨c, hc, hvalue⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg
      (μ := volume) (a := a) (b := b) (f := f) (g := fun _ => (1 : ℝ))
      hf.continuousOn
      (ContinuousOn.intervalIntegrable
        (show ContinuousOn (fun _ : ℝ => (1 : ℝ)) (uIcc a b) by fun_prop))
      (fun _ _ => zero_le_one)
  have hcIcc : c ∈ Icc a b := by simpa [uIcc_of_le hab.le] using hc
  have hproduct : f c * (b - a) = 0 := by
    simpa [hmean] using hvalue.symm
  have hlengthNe : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  exact ⟨c, hcIcc, (mul_eq_zero.mp hproduct).resolve_right hlengthNe⟩

/-- Pointwise one-dimensional Poincare estimate for a smooth mean-zero function. -/
theorem pointwise_sq_le_intervalLength_mul_integral_deriv_sq_of_mean_zero
    (f : ℝ → ℝ) {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    (hf : ContDiff ℝ 1 f) (hmean : (∫ y in a..b, f y) = 0) :
    f x ^ 2 ≤ (b - a) * ∫ y in a..b, deriv f y ^ 2 := by
  obtain ⟨c, hc, hfc⟩ :=
    exists_zero_of_intervalIntegral_eq_zero f hab hf.continuous hmean
  simpa [hfc] using
    function_sub_sq_le_intervalLength_mul_integral_deriv_sq
      f hab.le hc hx hf

/-- A concrete one-dimensional Poincare inequality.  The non-sharp constant is the square of
the interval length; its advantage here is that it follows from FTC and Cauchy--Schwarz with
no spectral machinery. -/
theorem intervalIntegral_sq_le_length_sq_mul_integral_deriv_sq_of_mean_zero
    (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContDiff ℝ 1 f)
    (hmean : (∫ x in a..b, f x) = 0) :
    (∫ x in a..b, f x ^ 2) ≤
      (b - a) ^ 2 * ∫ x in a..b, deriv f x ^ 2 := by
  let D : ℝ := ∫ x in a..b, deriv f x ^ 2
  have hleft : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    (hf.continuous.pow 2).continuousOn.intervalIntegrable
  have hright : IntervalIntegrable (fun _ : ℝ => (b - a) * D) volume a b :=
    (show Continuous (fun _ : ℝ => (b - a) * D) by fun_prop).continuousOn.intervalIntegrable
  have hmono : (∫ x in a..b, f x ^ 2) ≤
      ∫ _x in a..b, (b - a) * D := by
    apply intervalIntegral.integral_mono_on hab.le hleft hright
    intro x hx
    exact pointwise_sq_le_intervalLength_mul_integral_deriv_sq_of_mean_zero
      f hab hx hf hmean
  calc
    (∫ x in a..b, f x ^ 2) ≤ ∫ _x in a..b, (b - a) * D := hmono
    _ = (b - a) ^ 2 * ∫ x in a..b, deriv f x ^ 2 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      unfold D
      ring

/-- Arithmetic mean of a scalar function over a nondegenerate oriented interval. -/
def intervalMean (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ x in a..b, f x) / (b - a)

/-- Variance form of the one-dimensional Poincare inequality, with no mean-zero assumption. -/
theorem intervalIntegral_sub_mean_sq_le_length_sq_mul_integral_deriv_sq
    (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContDiff ℝ 1 f) :
    (∫ x in a..b, (f x - intervalMean f a b) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in a..b, deriv f x ^ 2 := by
  let g : ℝ → ℝ := fun x => f x - intervalMean f a b
  have hg : ContDiff ℝ 1 g := hf.sub contDiff_const
  have hfInterval : IntervalIntegrable f volume a b :=
    hf.continuous.continuousOn.intervalIntegrable
  have hconstInterval :
      IntervalIntegrable (fun _ : ℝ => intervalMean f a b) volume a b :=
    (show Continuous (fun _ : ℝ => intervalMean f a b) by fun_prop).continuousOn.intervalIntegrable
  have hgMean : (∫ x in a..b, g x) = 0 := by
    rw [show (∫ x in a..b, g x) =
        (∫ x in a..b, f x) - ∫ x in a..b, intervalMean f a b by
      exact intervalIntegral.integral_sub hfInterval hconstInterval]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    unfold intervalMean
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  have hderiv : deriv g = deriv f := by
    funext x
    exact (((hf.differentiable one_ne_zero).differentiableAt.hasDerivAt).sub_const
      (intervalMean f a b)).deriv
  have h := intervalIntegral_sq_le_length_sq_mul_integral_deriv_sq_of_mean_zero
    g hab hg hgMean
  rw [hderiv] at h
  exact h

/-! ## Descent to a measured circle -/

/-- Mean of a lifted scalar function with respect to the (unnormalized) circle volume. -/
def addCircleLiftMean {T : ℝ} [Fact (0 < T)] (f : ℝ → ℝ) : ℝ :=
  (∫ x : AddCircle T, AddCircle.liftIoc T 0 f x) / T

/-- Integration on a measured circle as a linear map on continuous functions. -/
def addCircleIntegralLinearMap (T : ℝ) [Fact (0 < T)] :
    C(AddCircle T, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x : AddCircle T, f x
  map_add' f g := by
    change (∫ x : AddCircle T, f x + g x) = _
    rw [integral_add]
    · simpa only [IntegrableOn, Measure.restrict_univ] using
        f.continuous.continuousOn.integrableOn_compact
          (μ := volume) (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T)))
    · simpa only [IntegrableOn, Measure.restrict_univ] using
        g.continuous.continuousOn.integrableOn_compact
          (μ := volume) (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T)))
  map_smul' c f := by
    change (∫ x : AddCircle T, c * f x) = c * ∫ x : AddCircle T, f x
    exact integral_const_mul c (fun x : AddCircle T => f x)

@[simp]
theorem addCircleIntegralLinearMap_apply
    (T : ℝ) [Fact (0 < T)] (f : C(AddCircle T, ℝ)) :
    addCircleIntegralLinearMap T f = ∫ x : AddCircle T, f x := rfl

/-- Circle integration is continuous for the sup norm. -/
def addCircleIntegralCLM (T : ℝ) [Fact (0 < T)] :
    C(AddCircle T, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous (addCircleIntegralLinearMap T)
    (volume.real (Set.univ : Set (AddCircle T))) fun f => by
      calc
        ‖∫ x : AddCircle T, f x‖ ≤ ‖f‖ * volume.real Set.univ :=
          norm_integral_le_of_norm_le_const
            (f := fun x : AddCircle T => f x) (C := ‖f‖) (μ := volume)
            (Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)
        _ = volume.real Set.univ * ‖f‖ := mul_comm _ _

@[simp]
theorem addCircleIntegralCLM_apply
    (T : ℝ) [Fact (0 < T)] (f : C(AddCircle T, ℝ)) :
    addCircleIntegralCLM T f = ∫ x : AddCircle T, f x := rfl

theorem addCircleLiftMean_eq_intervalMean
    {T : ℝ} [Fact (0 < T)] (f : ℝ → ℝ) :
    addCircleLiftMean (T := T) f = intervalMean f 0 T := by
  unfold addCircleLiftMean intervalMean
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral]
  simp only [zero_add, sub_zero]

/-- Variance form of Poincare on the concrete measured circle. -/
theorem addCircle_integral_sub_mean_sq_le_period_sq_mul_deriv_sq
    {T : ℝ} [hT : Fact (0 < T)] (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ x : AddCircle T,
        (AddCircle.liftIoc T 0 f x - addCircleLiftMean (T := T) f) ^ 2) ≤
      T ^ 2 *
        ∫ x : AddCircle T, AddCircle.liftIoc T 0 (fun r => deriv f r ^ 2) x := by
  rw [addCircleLiftMean_eq_intervalMean f]
  change (∫ x : AddCircle T, AddCircle.liftIoc T 0
      (fun r => (f r - intervalMean f 0 T) ^ 2) x) ≤ _
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral,
    AddCircle.integral_liftIoc_eq_intervalIntegral]
  simpa only [zero_add, sub_zero] using
    intervalIntegral_sub_mean_sq_le_length_sq_mul_integral_deriv_sq
      f hT.out hf

/-- The interval Poincare estimate transported to the concrete measured circle. -/
theorem addCircle_integral_sq_le_period_sq_mul_deriv_sq_of_mean_zero
    {T : ℝ} [hT : Fact (0 < T)] (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hmean : (∫ x : AddCircle T, AddCircle.liftIoc T 0 f x) = 0) :
    (∫ x : AddCircle T, AddCircle.liftIoc T 0 (fun r => f r ^ 2) x) ≤
      T ^ 2 *
        ∫ x : AddCircle T, AddCircle.liftIoc T 0 (fun r => deriv f r ^ 2) x := by
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral] at hmean
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral,
    AddCircle.integral_liftIoc_eq_intervalIntegral]
  have hmean' : (∫ x in (0 : ℝ)..T, f x) = 0 := by
    simpa only [zero_add] using hmean
  simpa only [zero_add, sub_zero] using
    intervalIntegral_sq_le_length_sq_mul_integral_deriv_sq_of_mean_zero
      f hT.out hf hmean'

/-- Conditional mean of a scalar torus field along one coordinate circle. -/
def torusCoordinateSliceMean
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement) : ℝ :=
  (∫ a : AddCircle ((2 : ℝ) * Real.pi), torusCoordinateSlice f i y a) /
    ((2 : ℝ) * Real.pi)

/-- Averaging on a circle is an `L²` contraction, in the pointwise form needed for
tensorization. -/
theorem period_mul_addCircleLiftMean_sq_le_integral_sq
    {T : ℝ} [hT : Fact (0 < T)] (f : ℝ → ℝ) (hf : Continuous f) :
    T * addCircleLiftMean (T := T) f ^ 2 ≤
      ∫ x : AddCircle T, AddCircle.liftIoc T 0 (fun r => f r ^ 2) x := by
  have hCauchy := intervalIntegral_sq_le_abs_sub_mul_abs_intervalIntegral_sq
    f 0 T hf
  have hsquareNonneg : 0 ≤ ∫ x in (0 : ℝ)..T, f x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hT.out.le fun _ => sq_nonneg _
  have hCauchy' : (∫ x in (0 : ℝ)..T, f x) ^ 2 ≤
      T * ∫ x in (0 : ℝ)..T, f x ^ 2 := by
    simpa only [sub_zero, abs_of_pos hT.out, abs_of_nonneg hsquareNonneg] using hCauchy
  rw [addCircleLiftMean_eq_intervalMean f]
  unfold intervalMean
  simp only [sub_zero]
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral]
  simp only [zero_add]
  have hidentity : T * ((∫ x in (0 : ℝ)..T, f x) / T) ^ 2 =
      (∫ x in (0 : ℝ)..T, f x) ^ 2 / T := by
    field_simp [hT.out.ne']
  rw [hidentity]
  exact (div_le_iff₀ hT.out).2 (by simpa [mul_comm] using hCauchy')

/-- Conditional coordinate averaging is pointwise contractive after integrating over the
averaged circle. -/
theorem period_mul_torusCoordinateSliceMean_sq_le_integral_sq
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (hf : Continuous (torusCoordinateSliceLift f i y)) :
    ((2 : ℝ) * Real.pi) * torusCoordinateSliceMean f i y ^ 2 ≤
      ∫ a : AddCircle ((2 : ℝ) * Real.pi), torusCoordinateSlice f i y a ^ 2 := by
  have h := period_mul_addCircleLiftMean_sq_le_integral_sq
    (T := (2 : ℝ) * Real.pi) (torusCoordinateSliceLift f i y) hf
  simpa only [torusCoordinateSliceMean, addCircleLiftMean,
    liftIoc_torusCoordinateSliceLift, pow_two, liftIoc_mul] using h

theorem period_mul_torusCoordinateSliceMean_eq_integral
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement) :
    ((2 : ℝ) * Real.pi) * torusCoordinateSliceMean f i y =
      ∫ a : AddCircle ((2 : ℝ) * Real.pi), torusCoordinateSlice f i y a := by
  unfold torusCoordinateSliceMean
  field_simp [mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]

/-- Variance Poincare estimate on an actual coordinate circle of `Torus3`. -/
theorem torusCoordinateSlice_integral_sub_mean_sq_le_period_sq_mul_derivative_sq
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (hf : ContDiff ℝ 1 (torusCoordinateSliceLift f i y)) :
    (∫ a : AddCircle ((2 : ℝ) * Real.pi),
        (torusCoordinateSlice f i y a - torusCoordinateSliceMean f i y) ^ 2) ≤
      ((2 : ℝ) * Real.pi) ^ 2 *
        ∫ a : AddCircle ((2 : ℝ) * Real.pi),
          torusCoordinateSliceDerivative f i y a ^ 2 := by
  have h := addCircle_integral_sub_mean_sq_le_period_sq_mul_deriv_sq
    (T := (2 : ℝ) * Real.pi) (torusCoordinateSliceLift f i y) hf
  simpa only [torusCoordinateSliceMean, addCircleLiftMean,
    liftIoc_torusCoordinateSliceLift, pow_two, liftIoc_mul,
    torusCoordinateSliceDerivative] using h

/-- The conditional coordinate mean, viewed again as a scalar field on `Torus3`. -/
def torusCoordinateMeanField
    (f : Torus3 → ℝ) (i : Fin 3) (x : Torus3) : ℝ :=
  torusCoordinateSliceMean f i (Fin.removeNth i x)

@[simp]
theorem torusCoordinateSlice_removeNth
    (f : Torus3 → ℝ) (i : Fin 3) (x : Torus3)
    (a : AddCircle ((2 : ℝ) * Real.pi)) :
    torusCoordinateSlice f i (Fin.removeNth i x) a = f (Function.update x i a) := by
  simp [torusCoordinateSlice]

theorem torusCoordinateMeanField_eq_integral_update
    (f : Torus3 → ℝ) (i : Fin 3) (x : Torus3) :
    torusCoordinateMeanField f i x =
      (∫ a : AddCircle ((2 : ℝ) * Real.pi), f (Function.update x i a)) /
        ((2 : ℝ) * Real.pi) := by
  simp [torusCoordinateMeanField, torusCoordinateSliceMean]

/-- Coordinate averaging preserves continuity.  Bundling the result as a `ContinuousMap`
makes all later compact-domain integrability obligations automatic. -/
def torusCoordinateMeanContinuous
    (f : C(Torus3, ℝ)) (i : Fin 3) : C(Torus3, ℝ) where
  toFun := torusCoordinateMeanField f i
  continuous_toFun := by
    let F : C(Torus3 × AddCircle ((2 : ℝ) * Real.pi), ℝ) :=
      ⟨fun z => f (Function.update z.1 i z.2), by
        apply f.continuous.comp
        fun_prop⟩
    let Fc : C(Torus3, C(AddCircle ((2 : ℝ) * Real.pi), ℝ)) := F.curry
    have hIntegral : Continuous (fun x : Torus3 =>
        addCircleIntegralCLM ((2 : ℝ) * Real.pi) (Fc x)) :=
      (addCircleIntegralCLM ((2 : ℝ) * Real.pi)).continuous.comp Fc.continuous
    have hMean : Continuous (fun x : Torus3 =>
        addCircleIntegralCLM ((2 : ℝ) * Real.pi) (Fc x) /
          ((2 : ℝ) * Real.pi)) := hIntegral.div_const _
    have hfun : torusCoordinateMeanField f i = fun x : Torus3 =>
        (∫ a : AddCircle ((2 : ℝ) * Real.pi), f (Function.update x i a)) /
          ((2 : ℝ) * Real.pi) := by
      funext x
      exact torusCoordinateMeanField_eq_integral_update f i x
    rw [hfun]
    simpa [Fc, F] using hMean

@[simp]
theorem torusCoordinateMeanContinuous_apply
    (f : C(Torus3, ℝ)) (i : Fin 3) (x : Torus3) :
    torusCoordinateMeanContinuous f i x = torusCoordinateMeanField f i x := rfl

/-- A coordinate line through a torus point, bundled as a continuous function on the
circle. -/
def torusCoordinateUpdateSliceContinuous
    (f : C(Torus3, ℝ)) (i : Fin 3) (x : Torus3) :
    C(AddCircle ((2 : ℝ) * Real.pi), ℝ) where
  toFun a := f (Function.update x i a)
  continuous_toFun := by fun_prop

@[simp]
theorem torusCoordinateUpdateSliceContinuous_apply
    (f : C(Torus3, ℝ)) (i : Fin 3) (x : Torus3)
    (a : AddCircle ((2 : ℝ) * Real.pi)) :
    torusCoordinateUpdateSliceContinuous f i x a =
      f (Function.update x i a) := rfl

/-- Coordinate averaging is linear on continuous scalar torus fields. -/
def torusCoordinateMeanLinearMap (i : Fin 3) :
    C(Torus3, ℝ) →ₗ[ℝ] C(Torus3, ℝ) where
  toFun f := torusCoordinateMeanContinuous f i
  map_add' f g := by
    ext x
    change torusCoordinateMeanContinuous (f + g) i x =
      torusCoordinateMeanContinuous f i x +
        torusCoordinateMeanContinuous g i x
    simp only [torusCoordinateMeanContinuous_apply,
      torusCoordinateMeanField_eq_integral_update]
    change addCircleIntegralCLM ((2 : ℝ) * Real.pi)
        (torusCoordinateUpdateSliceContinuous (f + g) i x) /
          ((2 : ℝ) * Real.pi) =
      addCircleIntegralCLM ((2 : ℝ) * Real.pi)
          (torusCoordinateUpdateSliceContinuous f i x) /
            ((2 : ℝ) * Real.pi) +
        addCircleIntegralCLM ((2 : ℝ) * Real.pi)
          (torusCoordinateUpdateSliceContinuous g i x) /
            ((2 : ℝ) * Real.pi)
    rw [show torusCoordinateUpdateSliceContinuous (f + g) i x =
        torusCoordinateUpdateSliceContinuous f i x +
          torusCoordinateUpdateSliceContinuous g i x by ext; rfl]
    simp only [map_add]
    ring
  map_smul' c f := by
    ext x
    change torusCoordinateMeanContinuous (c • f) i x =
      c * torusCoordinateMeanContinuous f i x
    simp only [torusCoordinateMeanContinuous_apply,
      torusCoordinateMeanField_eq_integral_update]
    change addCircleIntegralCLM ((2 : ℝ) * Real.pi)
        (torusCoordinateUpdateSliceContinuous (c • f) i x) /
          ((2 : ℝ) * Real.pi) =
      c • (addCircleIntegralCLM ((2 : ℝ) * Real.pi)
        (torusCoordinateUpdateSliceContinuous f i x) /
          ((2 : ℝ) * Real.pi))
    rw [show torusCoordinateUpdateSliceContinuous (c • f) i x =
        c • torusCoordinateUpdateSliceContinuous f i x by ext; rfl]
    simp only [map_smul, smul_eq_mul]
    ring

@[simp]
theorem torusCoordinateMeanLinearMap_apply
    (f : C(Torus3, ℝ)) (i : Fin 3) :
    torusCoordinateMeanLinearMap i f = torusCoordinateMeanContinuous f i := rfl

/-- Averaging in two distinct torus coordinates commutes.  This is the Fubini step
needed to regard the three coordinate averages as commuting conditional expectations. -/
theorem torusCoordinateMeanContinuous_comm
    (f : C(Torus3, ℝ)) {i j : Fin 3} (hij : i ≠ j) :
    torusCoordinateMeanContinuous (torusCoordinateMeanContinuous f j) i =
      torusCoordinateMeanContinuous (torusCoordinateMeanContinuous f i) j := by
  ext x
  have hIntegrable : Integrable
      (Function.uncurry fun a b : AddCircle ((2 : ℝ) * Real.pi) =>
        f (Function.update (Function.update x i a) j b))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    have hContinuous : Continuous
        (Function.uncurry fun a b : AddCircle ((2 : ℝ) * Real.pi) =>
          f (Function.update (Function.update x i a) j b)) := by
      fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hContinuous.continuousOn.integrableOn_compact
        (μ := volume)
        (isCompact_univ : IsCompact
          (Set.univ : Set
            (AddCircle ((2 : ℝ) * Real.pi) × AddCircle ((2 : ℝ) * Real.pi))))
  have hSwap :
      (∫ a : AddCircle ((2 : ℝ) * Real.pi),
        ∫ b : AddCircle ((2 : ℝ) * Real.pi),
          f (Function.update (Function.update x i a) j b)) =
        ∫ b : AddCircle ((2 : ℝ) * Real.pi),
          ∫ a : AddCircle ((2 : ℝ) * Real.pi),
            f (Function.update (Function.update x j b) i a) := by
    calc
      _ = ∫ b : AddCircle ((2 : ℝ) * Real.pi),
          ∫ a : AddCircle ((2 : ℝ) * Real.pi),
            f (Function.update (Function.update x i a) j b) :=
        MeasureTheory.integral_integral_swap hIntegrable
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun b => by
          apply integral_congr_ae
          exact Eventually.of_forall fun a => by
            change f (Function.update (Function.update x i a) j b) =
              f (Function.update (Function.update x j b) i a)
            rw [Function.update_comm hij]
  simp only [torusCoordinateMeanContinuous_apply,
    torusCoordinateMeanField_eq_integral_update]
  simp_rw [integral_div]
  rw [hSwap]

@[simp]
theorem torusCoordinateMeanContinuous_sub
    (f g : C(Torus3, ℝ)) (i : Fin 3) :
    torusCoordinateMeanContinuous (f - g) i =
      torusCoordinateMeanContinuous f i - torusCoordinateMeanContinuous g i := by
  simpa only [torusCoordinateMeanLinearMap_apply] using
    (torusCoordinateMeanLinearMap i).map_sub f g

/-- A coordinate average no longer depends on the coordinate that was averaged. -/
theorem torusCoordinateMeanContinuous_update_self
    (f : C(Torus3, ℝ)) (i : Fin 3) (x : Torus3)
    (a : AddCircle ((2 : ℝ) * Real.pi)) :
    torusCoordinateMeanContinuous f i (Function.update x i a) =
      torusCoordinateMeanContinuous f i x := by
  simp only [torusCoordinateMeanContinuous_apply,
    torusCoordinateMeanField_eq_integral_update]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun b => by
    change f (Function.update (Function.update x i a) i b) =
      f (Function.update x i b)
    rw [Function.update_idem]

/-- Average successively over all three physical coordinates. -/
def torusFullMeanContinuous (f : C(Torus3, ℝ)) : C(Torus3, ℝ) :=
  torusCoordinateMeanContinuous
    (torusCoordinateMeanContinuous
      (torusCoordinateMeanContinuous f (0 : Fin 3)) (1 : Fin 3)) (2 : Fin 3)

/-- The full coordinate average is invariant under changing any one coordinate. -/
theorem torusFullMeanContinuous_update
    (f : C(Torus3, ℝ)) (i : Fin 3) (x : Torus3)
    (a : AddCircle ((2 : ℝ) * Real.pi)) :
    torusFullMeanContinuous f (Function.update x i a) =
      torusFullMeanContinuous f x := by
  fin_cases i
  · have h01 := torusCoordinateMeanContinuous_comm f
      (i := (1 : Fin 3)) (j := (0 : Fin 3)) (by decide)
    have h02 := torusCoordinateMeanContinuous_comm
      (torusCoordinateMeanContinuous f (1 : Fin 3))
      (i := (2 : Fin 3)) (j := (0 : Fin 3)) (by decide)
    have hEq : torusFullMeanContinuous f =
        torusCoordinateMeanContinuous
          (torusCoordinateMeanContinuous
            (torusCoordinateMeanContinuous f (1 : Fin 3)) (2 : Fin 3))
          (0 : Fin 3) := by
      unfold torusFullMeanContinuous
      calc
        _ = torusCoordinateMeanContinuous
            (torusCoordinateMeanContinuous
              (torusCoordinateMeanContinuous f (1 : Fin 3)) (0 : Fin 3))
            (2 : Fin 3) := congrArg
              (fun g => torusCoordinateMeanContinuous g (2 : Fin 3)) h01
        _ = _ := h02
    rw [hEq]
    exact torusCoordinateMeanContinuous_update_self _ _ _ _
  · have hEq : torusFullMeanContinuous f =
        torusCoordinateMeanContinuous
          (torusCoordinateMeanContinuous
            (torusCoordinateMeanContinuous f (0 : Fin 3)) (2 : Fin 3))
          (1 : Fin 3) := by
      unfold torusFullMeanContinuous
      exact torusCoordinateMeanContinuous_comm
        (torusCoordinateMeanContinuous f (0 : Fin 3))
        (i := (2 : Fin 3)) (j := (1 : Fin 3)) (by decide)
    rw [hEq]
    exact torusCoordinateMeanContinuous_update_self _ _ _ _
  · exact torusCoordinateMeanContinuous_update_self _ _ _ _

/-- Consequently the full coordinate average is a constant field. -/
theorem torusFullMeanContinuous_eq
    (f : C(Torus3, ℝ)) (x y : Torus3) :
    torusFullMeanContinuous f x = torusFullMeanContinuous f y := by
  let x₀ := Function.update x (0 : Fin 3) (y 0)
  let x₁ := Function.update x₀ (1 : Fin 3) (y 1)
  let x₂ := Function.update x₁ (2 : Fin 3) (y 2)
  have hx₂ : x₂ = y := by
    funext k
    fin_cases k <;> simp [x₂, x₁, x₀]
  calc
    torusFullMeanContinuous f x = torusFullMeanContinuous f x₀ :=
      (torusFullMeanContinuous_update f (0 : Fin 3) x (y 0)).symm
    _ = torusFullMeanContinuous f x₁ :=
      (torusFullMeanContinuous_update f (1 : Fin 3) x₀ (y 1)).symm
    _ = torusFullMeanContinuous f x₂ :=
      (torusFullMeanContinuous_update f (2 : Fin 3) x₁ (y 2)).symm
    _ = torusFullMeanContinuous f y := by rw [hx₂]

/-- A continuous scalar field on the compact physical torus is integrable. -/
theorem continuous_integrable_torus3
    {f : Torus3 → ℝ} (hf : Continuous f) : Integrable f := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hf.continuousOn.integrableOn_compact
      (μ := volume) (isCompact_univ : IsCompact (Set.univ : Set Torus3))

/-- Restricting a continuous torus field to a lifted coordinate line remains continuous. -/
theorem ContinuousMap.continuous_torusCoordinateSliceLift
    (f : C(Torus3, ℝ)) (i : Fin 3) (y : TorusCoordinateComplement) :
    Continuous (torusCoordinateSliceLift f i y) := by
  unfold torusCoordinateSliceLift torusCoordinateSlice
  fun_prop

/-- Conditional coordinate averaging is a global `L²` contraction. -/
theorem integral_torus_coordinateMean_sq_le_integral_sq
    (f : Torus3 → ℝ) (i : Fin 3)
    (hf : ∀ y : TorusCoordinateComplement,
      Continuous (torusCoordinateSliceLift f i y))
    (hmeanSq : Integrable (fun x : Torus3 => torusCoordinateMeanField f i x ^ 2))
    (hfSq : Integrable (fun x : Torus3 => f x ^ 2)) :
    (∫ x : Torus3, torusCoordinateMeanField f i x ^ 2) ≤
      ∫ x : Torus3, f x ^ 2 := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin 3 => AddCircle ((2 : ℝ) * Real.pi)) i
  have he : MeasurePreserving e := torus3_volume_preserving_coordinate_split i
  have hesymm : MeasurePreserving e.symm := MeasurePreserving.symm e he
  have hmeanSq' : Integrable
      ((fun x : Torus3 => torusCoordinateMeanField f i x ^ 2) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hmeanSq
  have hfSq' : Integrable ((fun x : Torus3 => f x ^ 2) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hfSq
  have hmeanOuter : Integrable (fun y : TorusCoordinateComplement =>
      ((2 : ℝ) * Real.pi) * torusCoordinateSliceMean f i y ^ 2) := by
    simpa [e, torusCoordinateMeanField, measureReal_def,
      ENNReal.toReal_ofReal Real.pi_pos.le,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
      hmeanSq'.integral_prod_right
  have hfOuter : Integrable (fun y : TorusCoordinateComplement =>
      ∫ a : AddCircle ((2 : ℝ) * Real.pi), torusCoordinateSlice f i y a ^ 2) := by
    simpa [e, torusCoordinateSlice,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
      hfSq'.integral_prod_right
  have hiterated :
      (∫ y : TorusCoordinateComplement,
        ((2 : ℝ) * Real.pi) * torusCoordinateSliceMean f i y ^ 2) ≤
        ∫ y : TorusCoordinateComplement,
          ∫ a : AddCircle ((2 : ℝ) * Real.pi), torusCoordinateSlice f i y a ^ 2 := by
    exact integral_mono hmeanOuter hfOuter fun y =>
      period_mul_torusCoordinateSliceMean_sq_le_integral_sq f i y (hf y)
  calc
    (∫ x : Torus3, torusCoordinateMeanField f i x ^ 2) =
        ∫ y : TorusCoordinateComplement,
          ((2 : ℝ) * Real.pi) * torusCoordinateSliceMean f i y ^ 2 := by
      calc
        _ = ∫ z : AddCircle ((2 : ℝ) * Real.pi) × TorusCoordinateComplement,
            ((fun x : Torus3 => torusCoordinateMeanField f i x ^ 2) ∘ e.symm) z := by
          symm
          exact hesymm.integral_comp'
            (fun x : Torus3 => torusCoordinateMeanField f i x ^ 2)
        _ = _ := by
          rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hmeanSq']
          simp [e, torusCoordinateMeanField, measureReal_def,
            ENNReal.toReal_ofReal Real.pi_pos.le,
            MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    _ ≤ ∫ y : TorusCoordinateComplement,
          ∫ a : AddCircle ((2 : ℝ) * Real.pi), torusCoordinateSlice f i y a ^ 2 := hiterated
    _ = ∫ x : Torus3, f x ^ 2 := by
      calc
        _ = ∫ z : AddCircle ((2 : ℝ) * Real.pi) × TorusCoordinateComplement,
            ((fun x : Torus3 => f x ^ 2) ∘ e.symm) z := by
          rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hfSq']
          simp [e, torusCoordinateSlice,
            MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        _ = _ := hesymm.integral_comp' (fun x : Torus3 => f x ^ 2)

/-- The global `L²` contraction specialized to bundled continuous fields, with all
integrability and slice-continuity obligations discharged by compactness. -/
theorem integral_torus_coordinateMeanContinuous_sq_le_integral_sq
    (f : C(Torus3, ℝ)) (i : Fin 3) :
    (∫ x : Torus3, torusCoordinateMeanContinuous f i x ^ 2) ≤
      ∫ x : Torus3, f x ^ 2 := by
  have h := integral_torus_coordinateMean_sq_le_integral_sq
    (f := fun x => f x) i
    (fun y => f.continuous_torusCoordinateSliceLift i y)
    (continuous_integrable_torus3
      ((torusCoordinateMeanContinuous f i).continuous.pow 2))
    (continuous_integrable_torus3 (f.continuous.pow 2))
  simpa only [torusCoordinateMeanContinuous_apply] using h

/-- Conditional coordinate averaging preserves the global integral. -/
theorem integral_torusCoordinateMeanField_eq_integral
    (f : Torus3 → ℝ) (i : Fin 3)
    (hmean : Integrable (torusCoordinateMeanField f i))
    (hf : Integrable f) :
    (∫ x : Torus3, torusCoordinateMeanField f i x) = ∫ x : Torus3, f x := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin 3 => AddCircle ((2 : ℝ) * Real.pi)) i
  have he : MeasurePreserving e := torus3_volume_preserving_coordinate_split i
  have hesymm : MeasurePreserving e.symm := MeasurePreserving.symm e he
  have hmean' : Integrable (torusCoordinateMeanField f i ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hmean
  have hf' : Integrable (f ∘ e.symm) := hesymm.integrable_comp_of_integrable hf
  calc
    (∫ x : Torus3, torusCoordinateMeanField f i x) =
        ∫ y : TorusCoordinateComplement,
          ((2 : ℝ) * Real.pi) * torusCoordinateSliceMean f i y := by
      calc
        _ = ∫ z : AddCircle ((2 : ℝ) * Real.pi) × TorusCoordinateComplement,
            (torusCoordinateMeanField f i ∘ e.symm) z := by
          symm
          exact hesymm.integral_comp' (torusCoordinateMeanField f i)
        _ = _ := by
          rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hmean']
          simp [e, torusCoordinateMeanField, measureReal_def,
            ENNReal.toReal_ofReal Real.pi_pos.le,
            MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    _ = ∫ y : TorusCoordinateComplement,
          ∫ a : AddCircle ((2 : ℝ) * Real.pi), torusCoordinateSlice f i y a := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y =>
        period_mul_torusCoordinateSliceMean_eq_integral f i y
    _ = ∫ x : Torus3, f x := by
      calc
        _ = ∫ z : AddCircle ((2 : ℝ) * Real.pi) × TorusCoordinateComplement,
            (f ∘ e.symm) z := by
          rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hf']
          simp [e, torusCoordinateSlice,
            MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        _ = _ := hesymm.integral_comp' f

/-- Integral preservation for bundled continuous fields. -/
theorem integral_torusCoordinateMeanContinuous_eq_integral
    (f : C(Torus3, ℝ)) (i : Fin 3) :
    (∫ x : Torus3, torusCoordinateMeanContinuous f i x) =
      ∫ x : Torus3, f x := by
  exact integral_torusCoordinateMeanField_eq_integral f i
    (continuous_integrable_torus3
      (torusCoordinateMeanContinuous f i).continuous)
    (continuous_integrable_torus3 f.continuous)

/-- A mean-zero field has identically zero full coordinate average. -/
theorem torusFullMeanContinuous_eq_zero_of_integral_eq_zero
    (f : C(Torus3, ℝ)) (hmean : (∫ x : Torus3, f x) = 0) :
    torusFullMeanContinuous f = 0 := by
  have hIntegral : (∫ x : Torus3, torusFullMeanContinuous f x) = 0 := by
    unfold torusFullMeanContinuous
    rw [integral_torusCoordinateMeanContinuous_eq_integral,
      integral_torusCoordinateMeanContinuous_eq_integral,
      integral_torusCoordinateMeanContinuous_eq_integral, hmean]
  ext x
  have hConst : torusFullMeanContinuous f =
      (fun _ : Torus3 => torusFullMeanContinuous f x) := by
    funext y
    exact torusFullMeanContinuous_eq f y x
  rw [hConst, integral_const, smul_eq_mul] at hIntegral
  exact (mul_eq_zero.mp hIntegral).resolve_left measureReal_univ_ne_zero

/-- Elementary three-term Cauchy--Schwarz, stated in the polynomial form used by the
coordinate telescope. -/
theorem sq_add_add_le_three_mul_sum_sq (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- Tensorization of the three coordinate conditional variances.  This is the global
mean-zero `L²` estimate before inserting any derivative bounds. -/
theorem integral_torus_sq_le_three_mul_coordinateVariance_sum
    (f : C(Torus3, ℝ)) (hmean : (∫ x : Torus3, f x) = 0) :
    (∫ x : Torus3, f x ^ 2) ≤
      3 *
        ((∫ x : Torus3,
            (f x - torusCoordinateMeanContinuous f (0 : Fin 3) x) ^ 2) +
          (∫ x : Torus3,
            (f x - torusCoordinateMeanContinuous f (1 : Fin 3) x) ^ 2) +
          ∫ x : Torus3,
            (f x - torusCoordinateMeanContinuous f (2 : Fin 3) x) ^ 2) := by
  let d₀ : C(Torus3, ℝ) :=
    f - torusCoordinateMeanContinuous f (0 : Fin 3)
  let d₁ : C(Torus3, ℝ) :=
    torusCoordinateMeanContinuous f (0 : Fin 3) -
      torusCoordinateMeanContinuous
        (torusCoordinateMeanContinuous f (0 : Fin 3)) (1 : Fin 3)
  let d₂ : C(Torus3, ℝ) :=
    torusCoordinateMeanContinuous
        (torusCoordinateMeanContinuous f (0 : Fin 3)) (1 : Fin 3) -
      torusFullMeanContinuous f
  have hfull := torusFullMeanContinuous_eq_zero_of_integral_eq_zero f hmean
  have hdecomp : ∀ x : Torus3, f x = d₀ x + d₁ x + d₂ x := by
    intro x
    have hfullx : torusFullMeanContinuous f x = 0 := by
      exact DFunLike.congr_fun hfull x
    simp only [d₀, d₁, d₂, ContinuousMap.sub_apply]
    rw [hfullx]
    ring
  have hd₀Int : Integrable (fun x : Torus3 => d₀ x ^ 2) :=
    continuous_integrable_torus3 (d₀.continuous.pow 2)
  have hd₁Int : Integrable (fun x : Torus3 => d₁ x ^ 2) :=
    continuous_integrable_torus3 (d₁.continuous.pow 2)
  have hd₂Int : Integrable (fun x : Torus3 => d₂ x ^ 2) :=
    continuous_integrable_torus3 (d₂.continuous.pow 2)
  have hpointwise : ∀ x : Torus3,
      f x ^ 2 ≤ 3 * (d₀ x ^ 2 + d₁ x ^ 2 + d₂ x ^ 2) := by
    intro x
    rw [hdecomp x]
    exact sq_add_add_le_three_mul_sum_sq _ _ _
  have htel : (∫ x : Torus3, f x ^ 2) ≤
      3 * ((∫ x : Torus3, d₀ x ^ 2) +
        (∫ x : Torus3, d₁ x ^ 2) +
        ∫ x : Torus3, d₂ x ^ 2) := by
    calc
      (∫ x : Torus3, f x ^ 2) ≤
          ∫ x : Torus3, 3 * (d₀ x ^ 2 + d₁ x ^ 2 + d₂ x ^ 2) :=
        integral_mono
          (continuous_integrable_torus3 (f.continuous.pow 2))
          (((hd₀Int.add hd₁Int).add hd₂Int).const_mul 3)
          hpointwise
      _ = 3 * ((∫ x : Torus3, d₀ x ^ 2) +
          (∫ x : Torus3, d₁ x ^ 2) +
          ∫ x : Torus3, d₂ x ^ 2) := by
        have h₀₁ : (∫ x : Torus3, d₀ x ^ 2 + d₁ x ^ 2) =
            (∫ x : Torus3, d₀ x ^ 2) + ∫ x : Torus3, d₁ x ^ 2 := by
          simpa only [Pi.add_apply] using integral_add hd₀Int hd₁Int
        have h₀₁₂ :
            (∫ x : Torus3, d₀ x ^ 2 + d₁ x ^ 2 + d₂ x ^ 2) =
              (∫ x : Torus3, d₀ x ^ 2) +
                (∫ x : Torus3, d₁ x ^ 2) +
                  ∫ x : Torus3, d₂ x ^ 2 := by
          calc
            _ = (∫ x : Torus3, d₀ x ^ 2 + d₁ x ^ 2) +
                ∫ x : Torus3, d₂ x ^ 2 := by
              simpa only [Pi.add_apply] using
                integral_add (hd₀Int.add hd₁Int) hd₂Int
            _ = _ := by rw [h₀₁]
        rw [integral_const_mul]
        rw [h₀₁₂]
  have hd₁Eq : d₁ = torusCoordinateMeanContinuous
      (f - torusCoordinateMeanContinuous f (1 : Fin 3)) (0 : Fin 3) := by
    unfold d₁
    rw [torusCoordinateMeanContinuous_sub,
      torusCoordinateMeanContinuous_comm f
        (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)]
  have hd₁Bound : (∫ x : Torus3, d₁ x ^ 2) ≤
      ∫ x : Torus3,
        (f x - torusCoordinateMeanContinuous f (1 : Fin 3) x) ^ 2 := by
    rw [hd₁Eq]
    exact integral_torus_coordinateMeanContinuous_sq_le_integral_sq
      (f - torusCoordinateMeanContinuous f (1 : Fin 3)) (0 : Fin 3)
  have htriple : torusCoordinateMeanContinuous
        (torusCoordinateMeanContinuous
          (torusCoordinateMeanContinuous f (2 : Fin 3)) (0 : Fin 3))
        (1 : Fin 3) =
      torusFullMeanContinuous f := by
    unfold torusFullMeanContinuous
    calc
      _ = torusCoordinateMeanContinuous
          (torusCoordinateMeanContinuous
            (torusCoordinateMeanContinuous f (0 : Fin 3)) (2 : Fin 3))
          (1 : Fin 3) := congrArg
            (fun g => torusCoordinateMeanContinuous g (1 : Fin 3))
            (torusCoordinateMeanContinuous_comm f
              (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide))
      _ = _ := torusCoordinateMeanContinuous_comm
        (torusCoordinateMeanContinuous f (0 : Fin 3))
        (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  have hd₂Eq : d₂ = torusCoordinateMeanContinuous
      (torusCoordinateMeanContinuous
        (f - torusCoordinateMeanContinuous f (2 : Fin 3)) (0 : Fin 3))
      (1 : Fin 3) := by
    unfold d₂
    rw [torusCoordinateMeanContinuous_sub,
      torusCoordinateMeanContinuous_sub, htriple]
  have hd₂Bound : (∫ x : Torus3, d₂ x ^ 2) ≤
      ∫ x : Torus3,
        (f x - torusCoordinateMeanContinuous f (2 : Fin 3) x) ^ 2 := by
    rw [hd₂Eq]
    exact (integral_torus_coordinateMeanContinuous_sq_le_integral_sq
      (torusCoordinateMeanContinuous
        (f - torusCoordinateMeanContinuous f (2 : Fin 3)) (0 : Fin 3))
      (1 : Fin 3)).trans
        (integral_torus_coordinateMeanContinuous_sq_le_integral_sq
          (f - torusCoordinateMeanContinuous f (2 : Fin 3)) (0 : Fin 3))
  apply htel.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  exact add_le_add (add_le_add le_rfl hd₁Bound) hd₂Bound

/-- Global conditional-variance Poincare inequality on `Torus3`.  This is the tensorization
building block: averaging out one circle costs only the squared period times the energy in
that coordinate derivative. -/
theorem integral_torus_sub_coordinateMean_sq_le_period_sq_mul_derivative_sq
    (f : Torus3 → ℝ) (i : Fin 3)
    (hf : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hleft : Integrable (fun x : Torus3 =>
      (f x - torusCoordinateMeanField f i x) ^ 2))
    (hright : Integrable (fun x : Torus3 => torusCoordinateDerivative f i x ^ 2)) :
    (∫ x : Torus3, (f x - torusCoordinateMeanField f i x) ^ 2) ≤
      ((2 : ℝ) * Real.pi) ^ 2 *
        ∫ x : Torus3, torusCoordinateDerivative f i x ^ 2 := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin 3 => AddCircle ((2 : ℝ) * Real.pi)) i
  have he : MeasurePreserving e := torus3_volume_preserving_coordinate_split i
  have hesymm : MeasurePreserving e.symm := MeasurePreserving.symm e he
  have hleft' : Integrable
      ((fun x : Torus3 => (f x - torusCoordinateMeanField f i x) ^ 2) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hleft
  have hright' : Integrable
      ((fun x : Torus3 => torusCoordinateDerivative f i x ^ 2) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hright
  have hleftOuter : Integrable (fun y : TorusCoordinateComplement =>
      ∫ a : AddCircle ((2 : ℝ) * Real.pi),
        (torusCoordinateSlice f i y a - torusCoordinateSliceMean f i y) ^ 2) := by
    simpa [e, torusCoordinateMeanField, torusCoordinateSlice,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
      hleft'.integral_prod_right
  have hrightOuter : Integrable (fun y : TorusCoordinateComplement =>
      ∫ a : AddCircle ((2 : ℝ) * Real.pi),
        torusCoordinateSliceDerivative f i y a ^ 2) := by
    simpa [e, torusCoordinateDerivative,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
      hright'.integral_prod_right
  have hiterated :
      (∫ y : TorusCoordinateComplement,
        ∫ a : AddCircle ((2 : ℝ) * Real.pi),
          (torusCoordinateSlice f i y a - torusCoordinateSliceMean f i y) ^ 2) ≤
        ∫ y : TorusCoordinateComplement,
          ((2 : ℝ) * Real.pi) ^ 2 *
            ∫ a : AddCircle ((2 : ℝ) * Real.pi),
              torusCoordinateSliceDerivative f i y a ^ 2 := by
    exact integral_mono hleftOuter
      (hrightOuter.const_mul (((2 : ℝ) * Real.pi) ^ 2))
      (fun y =>
        torusCoordinateSlice_integral_sub_mean_sq_le_period_sq_mul_derivative_sq
          f i y (hf y))
  calc
    (∫ x : Torus3, (f x - torusCoordinateMeanField f i x) ^ 2) =
        ∫ y : TorusCoordinateComplement,
          ∫ a : AddCircle ((2 : ℝ) * Real.pi),
            (torusCoordinateSlice f i y a - torusCoordinateSliceMean f i y) ^ 2 := by
      calc
        _ = ∫ z : AddCircle ((2 : ℝ) * Real.pi) × TorusCoordinateComplement,
            ((fun x : Torus3 => (f x - torusCoordinateMeanField f i x) ^ 2) ∘
              e.symm) z := by
          symm
          exact hesymm.integral_comp'
            (fun x : Torus3 => (f x - torusCoordinateMeanField f i x) ^ 2)
        _ = _ := by
          rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hleft']
          simp [e, torusCoordinateMeanField, torusCoordinateSlice,
            MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    _ ≤ ∫ y : TorusCoordinateComplement,
          ((2 : ℝ) * Real.pi) ^ 2 *
            ∫ a : AddCircle ((2 : ℝ) * Real.pi),
              torusCoordinateSliceDerivative f i y a ^ 2 := hiterated
    _ = ((2 : ℝ) * Real.pi) ^ 2 *
        ∫ y : TorusCoordinateComplement,
          ∫ a : AddCircle ((2 : ℝ) * Real.pi),
            torusCoordinateSliceDerivative f i y a ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
    _ = ((2 : ℝ) * Real.pi) ^ 2 *
        ∫ x : Torus3, torusCoordinateDerivative f i x ^ 2 := by
      congr 1
      calc
        _ = ∫ z : AddCircle ((2 : ℝ) * Real.pi) × TorusCoordinateComplement,
            ((fun x : Torus3 => torusCoordinateDerivative f i x ^ 2) ∘ e.symm) z := by
          rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hright']
          simp [e, torusCoordinateDerivative,
            MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        _ = _ := hesymm.integral_comp'
          (fun x : Torus3 => torusCoordinateDerivative f i x ^ 2)

/-- Concrete global Poincare inequality on the physical three-torus.  The constant is
non-sharp (`3 (2π)^2`), but every analytic premise is explicit and the proof is the
tensorization of the three already-proved circle estimates. -/
theorem integral_torus_sq_le_three_mul_period_sq_mul_coordinateDerivative_sum
    (f : C(Torus3, ℝ))
    (hmean : (∫ x : Torus3, f x) = 0)
    (hsmooth : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hderiv : ∀ i : Fin 3,
      Integrable (fun x : Torus3 => torusCoordinateDerivative f i x ^ 2)) :
    (∫ x : Torus3, f x ^ 2) ≤
      3 * ((2 : ℝ) * Real.pi) ^ 2 *
        ((∫ x : Torus3, torusCoordinateDerivative f (0 : Fin 3) x ^ 2) +
          (∫ x : Torus3, torusCoordinateDerivative f (1 : Fin 3) x ^ 2) +
          ∫ x : Torus3, torusCoordinateDerivative f (2 : Fin 3) x ^ 2) := by
  have hvariance := integral_torus_sq_le_three_mul_coordinateVariance_sum f hmean
  have hcoordinate (i : Fin 3) :
      (∫ x : Torus3,
          (f x - torusCoordinateMeanContinuous f i x) ^ 2) ≤
        ((2 : ℝ) * Real.pi) ^ 2 *
          ∫ x : Torus3, torusCoordinateDerivative f i x ^ 2 := by
    exact integral_torus_sub_coordinateMean_sq_le_period_sq_mul_derivative_sq
      f i (hsmooth i)
      (continuous_integrable_torus3
        ((f.continuous.sub
          (torusCoordinateMeanContinuous f i).continuous).pow 2))
      (hderiv i)
  have hsum := add_le_add
    (add_le_add (hcoordinate (0 : Fin 3)) (hcoordinate (1 : Fin 3)))
    (hcoordinate (2 : Fin 3))
  calc
    (∫ x : Torus3, f x ^ 2) ≤
        3 *
          ((∫ x : Torus3,
              (f x - torusCoordinateMeanContinuous f (0 : Fin 3) x) ^ 2) +
            (∫ x : Torus3,
              (f x - torusCoordinateMeanContinuous f (1 : Fin 3) x) ^ 2) +
            ∫ x : Torus3,
              (f x - torusCoordinateMeanContinuous f (2 : Fin 3) x) ^ 2) :=
      hvariance
    _ ≤ 3 *
        (((2 : ℝ) * Real.pi) ^ 2 *
            (∫ x : Torus3, torusCoordinateDerivative f (0 : Fin 3) x ^ 2) +
          ((2 : ℝ) * Real.pi) ^ 2 *
            (∫ x : Torus3, torusCoordinateDerivative f (1 : Fin 3) x ^ 2) +
          ((2 : ℝ) * Real.pi) ^ 2 *
            ∫ x : Torus3, torusCoordinateDerivative f (2 : Fin 3) x ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 3 * ((2 : ℝ) * Real.pi) ^ 2 *
        ((∫ x : Torus3, torusCoordinateDerivative f (0 : Fin 3) x ^ 2) +
          (∫ x : Torus3, torusCoordinateDerivative f (1 : Fin 3) x ^ 2) +
          ∫ x : Torus3, torusCoordinateDerivative f (2 : Fin 3) x ^ 2) := by
      ring

/-- Poincare on an actual coordinate circle of `Torus3`.  Smoothness is imposed only on
the displayed one-dimensional periodic lift. -/
theorem torusCoordinateSlice_integral_sq_le_period_sq_mul_derivative_sq
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (hf : ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hmean : (∫ a : AddCircle ((2 : ℝ) * Real.pi),
      torusCoordinateSlice f i y a) = 0) :
    (∫ a : AddCircle ((2 : ℝ) * Real.pi),
        torusCoordinateSlice f i y a ^ 2) ≤
      ((2 : ℝ) * Real.pi) ^ 2 *
        ∫ a : AddCircle ((2 : ℝ) * Real.pi),
          torusCoordinateSliceDerivative f i y a ^ 2 := by
  have h := addCircle_integral_sq_le_period_sq_mul_deriv_sq_of_mean_zero
    (T := (2 : ℝ) * Real.pi) (torusCoordinateSliceLift f i y) hf
  have hmeanLift :
      (∫ a : AddCircle ((2 : ℝ) * Real.pi),
        AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
          (torusCoordinateSliceLift f i y) a) = 0 := by
    simpa only [liftIoc_torusCoordinateSliceLift] using hmean
  specialize h hmeanLift
  simpa only [pow_two, liftIoc_mul, liftIoc_torusCoordinateSliceLift,
    torusCoordinateSliceDerivative] using h
