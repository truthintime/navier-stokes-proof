import NSFormal.KineticEnergy

/-!
# Concrete quotient continuation bound

This file connects the spatial quotient estimate, the actual enstrophy rate,
the kinetic-energy budget, and the logarithmic continuation argument.  The
coefficient is the zero-safe quotient fraction constructed from the vorticity;
there is no free depletion parameter in the conclusion.
-/

open Filter Function MeasureTheory Set
open scoped Interval

noncomputable section

/-- The scalar rate furnished by the integrated vorticity equation. -/
def torusEnstrophyRate
    (viscosity : ℝ) (u w : C(Torus3, Vec3)) : ℝ :=
  (∫ x : Torus3, torusStretchingProduction u w x) -
    viscosity * torusPalinstrophy w

/-- Squared integral Cauchy--Schwarz for a real inner-product pairing. -/
theorem sq_abs_integral_inner_le_integral_norm_sq_mul_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hproduct : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
    hf.norm.integrable_mul hg.norm
  have hinner : Integrable (fun x => inner ℝ (f x) (g x)) μ := by
    apply hproduct.mono' (hf.1.inner hg.1)
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using abs_real_inner_le_norm (f x) (g x)
  have habs : |∫ x, inner ℝ (f x) (g x) ∂μ| ≤
      ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    calc
      |∫ x, inner ℝ (f x) (g x) ∂μ| ≤
          ∫ x, |inner ℝ (f x) (g x)| ∂μ := by
        simpa only [← Real.norm_eq_abs] using
          (norm_integral_le_integral_norm
            (μ := μ) (fun x => inner ℝ (f x) (g x)))
      _ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
        apply integral_mono_ae hinner.norm hproduct
        exact Eventually.of_forall fun x => abs_real_inner_le_norm (f x) (g x)
  have hproductNonneg : 0 ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ :=
    integral_nonneg fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsquare := (sq_le_sq₀ (abs_nonneg _) hproductNonneg).2 habs
  exact hsquare.trans
    (sq_integral_mul_le_integral_sq_mul_integral_sq
      (Eventually.of_forall fun x => norm_nonneg (f x))
      (Eventually.of_forall fun x => norm_nonneg (g x)) hf.norm hg.norm)

/-- For smooth periodic fields, the Cauchy defect is exactly the quotient mass
times the squared positive-production rigidity residual.  Compactness supplies
all integrability assumptions; only the geometric condition `div w = 0` and
the nonzero quotient branch remain explicit. -/
theorem torus_stretchingCauchyDefect_eq_scaledResidual_of_contDiff
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0) :
    torusVorticitySelfTransportQuotient w *
          periodicVorticityWeightedVelocityVariance u w frame -
        (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 =
      torusVorticitySelfTransportQuotient w *
        ∫ x : Torus3,
          ‖periodicVorticityWeightedCenteredVelocityVector u w frame x +
              (((∫ y : Torus3, torusStretchingProduction u w y) /
                  torusVorticitySelfTransportQuotient w) •
                periodicNormalizedVorticitySelfTransportVector w x)‖ ^ 2 := by
  have hquotient :=
    memLp_sqrt_periodicVorticitySelfTransportQuotientSq_of_contDiff w hw
  have hquotientInt : Integrable
      (periodicVorticitySelfTransportQuotientSq w) := by
    simpa only [Real.sq_sqrt
      (periodicVorticitySelfTransportQuotientSq_nonneg w _)] using
        hquotient.integrable_sq
  have hvarianceInt : Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight w x *
        ‖centeredVelocity u frame x‖ ^ 2) := by
    have hc : Continuous (fun x : Torus3 =>
        periodicVorticityEnergyWeight w x *
          ‖centeredVelocity u frame x‖ ^ 2) := by
      unfold periodicVorticityEnergyWeight centeredVelocity
      fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hcomponents : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight w x * (u x j - frame j) ^ 2) := by
    intro j
    have hc : Continuous (fun x : Torus3 =>
        periodicVorticityEnergyWeight w x * (u x j - frame j) ^ 2) := by
      unfold periodicVorticityEnergyWeight
      fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  exact torus_stretchingCauchyDefect_eq_scaledResidual u w frame
    hquotientInt hvarianceInt
    (integrable_periodicVorticitySelfTransportDensity_centered_of_contDiff
      u w frame hw)
    hcomponents
    (integral_torusStretchingProduction_eq_neg_selfTransport_of_contDiff
      u w frame hu hw hdiv)
    hquotientNe

/-- The exact self-transport factorization is automatic for smooth periodic
fields with divergence-free vorticity.  The proof uses the squared-residual
identity off the zero-quotient set and the underlying zero-safe Cauchy estimate
on the zero-quotient branch. -/
theorem sq_integral_torusStretchingProduction_le_selfTransportQuotient_weightedVariance_of_contDiff
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0) :
    (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
      torusVorticitySelfTransportQuotient w *
        periodicVorticityWeightedVelocityVariance u w frame := by
  let weightedNorm : C(Torus3, ℝ) :=
    ⟨fun x => ‖w x‖ * ‖centeredVelocity u frame x‖, by
      unfold centeredVelocity
      fun_prop⟩
  have hvariance : MemLp (fun x : Torus3 =>
      ‖w x‖ * ‖centeredVelocity u frame x‖) 2 volume := by
    change MemLp (weightedNorm : Torus3 → ℝ) 2 volume
    exact weightedNorm.memLp_torus_volume 2
  have hquotient :=
    memLp_sqrt_periodicVorticitySelfTransportQuotientSq_of_contDiff w hw
  by_cases hquotientZero : torusVorticitySelfTransportQuotient w = 0
  · have hself :=
      sq_abs_integral_periodicVorticitySelfTransportDensity_le_selfTransportQuotient
        (centeredVelocity u frame) w hquotient hvariance
    have hparts :=
      integral_torusStretchingProduction_eq_neg_selfTransport_of_contDiff
        u w frame hu hw hdiv
    have hquotientIntegral :
        (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) = 0 := by
      simpa only [torusVorticitySelfTransportQuotient] using hquotientZero
    rw [hparts]
    simpa only [neg_sq, sq_abs, hquotientZero, hquotientIntegral, zero_mul] using hself
  · apply sub_nonneg.mp
    rw [torus_stretchingCauchyDefect_eq_scaledResidual_of_contDiff
      u w frame hu hw hdiv hquotientZero]
    exact mul_nonneg
      (integral_nonneg fun x =>
        periodicVorticitySelfTransportQuotientSq_nonneg w x)
      (integral_nonneg fun _ => sq_nonneg _)

/-- Saturation of the smooth stretching factorization is equivalent to the
positive-production nonlinear eigen-relation holding almost everywhere. -/
theorem torus_stretchingCauchyDefect_eq_zero_iff_ae_rigidity
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0) :
    torusVorticitySelfTransportQuotient w *
          periodicVorticityWeightedVelocityVariance u w frame -
        (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 = 0 ↔
      (fun x : Torus3 =>
        periodicVorticityWeightedCenteredVelocityVector u w frame x +
          (((∫ y : Torus3, torusStretchingProduction u w y) /
              torusVorticitySelfTransportQuotient w) •
            periodicNormalizedVorticitySelfTransportVector w x)) =ᵐ[volume]
        0 := by
  let f : Torus3 → Vec3 :=
    periodicNormalizedVorticitySelfTransportVector w
  let g : Torus3 → Vec3 :=
    periodicVorticityWeightedCenteredVelocityVector u w frame
  let c : ℝ :=
    (∫ y : Torus3, torusStretchingProduction u w y) /
      torusVorticitySelfTransportQuotient w
  have hquotient :=
    memLp_sqrt_periodicVorticitySelfTransportQuotientSq_of_contDiff w hw
  have hquotientInt : Integrable
      (periodicVorticitySelfTransportQuotientSq w) := by
    simpa only [Real.sq_sqrt
      (periodicVorticitySelfTransportQuotientSq_nonneg w _)] using
        hquotient.integrable_sq
  have hfSq : Integrable (fun x : Torus3 => ‖f x‖ ^ 2) :=
    hquotientInt.congr (Eventually.of_forall fun x =>
      (periodicNormalizedVorticitySelfTransportVector_norm_sq w x).symm)
  have hvarianceInt : Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight w x *
        ‖centeredVelocity u frame x‖ ^ 2) := by
    have hc : Continuous (fun x : Torus3 =>
        periodicVorticityEnergyWeight w x *
          ‖centeredVelocity u frame x‖ ^ 2) := by
      unfold periodicVorticityEnergyWeight centeredVelocity
      fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hgSq : Integrable (fun x : Torus3 => ‖g x‖ ^ 2) :=
    hvarianceInt.congr (Eventually.of_forall fun x =>
      (periodicVorticityWeightedCenteredVelocityVector_norm_sq
        u w frame x).symm)
  have hself :=
    integrable_periodicVorticitySelfTransportDensity_centered_of_contDiff
      u w frame hw
  have hfg : Integrable (fun x : Torus3 => inner ℝ (f x) (g x)) :=
    hself.congr (Eventually.of_forall fun x =>
      (inner_periodicNormalizedSelfTransport_weightedCenteredVelocity
        u w frame x).symm)
  have hresInt : Integrable (fun x : Torus3 => ‖g x + c • f x‖ ^ 2) := by
    have hexpanded : Integrable (fun x : Torus3 =>
        (‖g x‖ ^ 2 + 2 * c * inner ℝ (f x) (g x)) +
          c ^ 2 * ‖f x‖ ^ 2) :=
      (hgSq.add (hfg.const_mul (2 * c))).add (hfSq.const_mul (c ^ 2))
    exact hexpanded.congr (Eventually.of_forall fun x => by
      change (‖g x‖ ^ 2 + 2 * c * inner ℝ (f x) (g x)) +
          c ^ 2 * ‖f x‖ ^ 2 = ‖g x + c • f x‖ ^ 2
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm (g x) (f x)]
      ring)
  have hid := torus_stretchingCauchyDefect_eq_scaledResidual_of_contDiff
    u w frame hu hw hdiv hquotientNe
  constructor
  · intro hzero
    rw [hid] at hzero
    have hintZero : (∫ x : Torus3, ‖g x + c • f x‖ ^ 2) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hquotientNe
    have hscalar : (fun x : Torus3 => ‖g x + c • f x‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hresInt).1
        hintZero
    filter_upwards [hscalar] with x hx
    change g x + c • f x = 0
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · intro hrigid
    have hscalar : (fun x : Torus3 => ‖g x + c • f x‖ ^ 2) =ᵐ[volume] 0 := by
      filter_upwards [hrigid] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      rw [hx, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have hintZero : (∫ x : Torus3, ‖g x + c • f x‖ ^ 2) = 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hresInt).2
        hscalar
    rw [hid, hintZero, mul_zero]

/-- Clearing the zero-safe normalization in the equality case yields the
direct differential rigidity equation
`|w|² (u-frame) + (N/Q) (w·∇)w = 0` almost everywhere. -/
theorem torus_stretchingCauchyDefect_zero_implies_ae_cleared_rigidity
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0)
    (hzero :
      torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 = 0) :
    (fun x : Torus3 =>
      ‖w x‖ ^ 2 • centeredVelocity u frame x +
        (((∫ y : Torus3, torusStretchingProduction u w y) /
            torusVorticitySelfTransportQuotient w) •
          periodicVorticitySelfTransportVector w x)) =ᵐ[volume] 0 := by
  have hrigid :=
    (torus_stretchingCauchyDefect_eq_zero_iff_ae_rigidity
      u w frame hu hw hdiv hquotientNe).1 hzero
  filter_upwards [hrigid] with x hx
  simp only [Pi.zero_apply] at hx ⊢
  have hx' := congrArg (fun z : Vec3 => ‖w x‖ • z) hx
  have hleft :
      ‖w x‖ • periodicVorticityWeightedCenteredVelocityVector u w frame x =
        ‖w x‖ ^ 2 • centeredVelocity u frame x :=
    norm_smul_periodicVorticityWeightedCenteredVelocityVector u w frame x
  have hright :
      ‖w x‖ •
          (((∫ y : Torus3, torusStretchingProduction u w y) /
              torusVorticitySelfTransportQuotient w) •
            periodicNormalizedVorticitySelfTransportVector w x) =
        (((∫ y : Torus3, torusStretchingProduction u w y) /
            torusVorticitySelfTransportQuotient w) •
          periodicVorticitySelfTransportVector w x) := by
    rw [smul_smul, mul_comm, ← smul_smul,
      norm_smul_periodicNormalizedVorticitySelfTransportVector]
  rw [smul_add, hleft, hright, smul_zero] at hx'
  exact hx'

/-- Saturation splits almost everywhere into a scalar balance along vorticity
and a vector balance in the plane normal to vorticity. -/
theorem torus_stretchingCauchyDefect_zero_implies_ae_parallel_projected_rigidity
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0)
    (hzero :
      torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 = 0) :
    ((fun x : Torus3 =>
        ‖w x‖ ^ 2 * inner ℝ (w x) (centeredVelocity u frame x) +
          ((∫ y : Torus3, torusStretchingProduction u w y) /
              torusVorticitySelfTransportQuotient w) *
            inner ℝ (w x) (periodicVorticitySelfTransportVector w x))
        =ᵐ[volume] 0) ∧
      ((fun x : Torus3 =>
        ‖w x‖ ^ 2 •
            vorticityDirectionProjection (w x) (centeredVelocity u frame x) +
          ((∫ y : Torus3, torusStretchingProduction u w y) /
              torusVorticitySelfTransportQuotient w) •
            vorticityDirectionProjection (w x)
              (periodicVorticitySelfTransportVector w x)) =ᵐ[volume] 0) := by
  have hcleared :=
    torus_stretchingCauchyDefect_zero_implies_ae_cleared_rigidity
      u w frame hu hw hdiv hquotientNe hzero
  constructor
  · filter_upwards [hcleared] with x hx
    exact cleared_vorticity_rigidity_parallel_balance
      (w x) (centeredVelocity u frame x)
      (periodicVorticitySelfTransportVector w x)
      ((∫ y : Torus3, torusStretchingProduction u w y) /
        torusVorticitySelfTransportQuotient w) hx
  · filter_upwards [hcleared] with x hx
    exact cleared_vorticity_rigidity_projected_balance
      (w x) (centeredVelocity u frame x)
      (periodicVorticitySelfTransportVector w x)
      ((∫ y : Torus3, torusStretchingProduction u w y) /
        torusVorticitySelfTransportQuotient w) hx

/-- A positive-vorticity cutoff tests the normalized Cauchy residual while
the self-transport term cancels by logarithmic periodic transport.  Since the
test vector has norm at most one, this gives a regularized helicity-to-residual
estimate with the exact torus-volume factor. -/
theorem regularized_centered_helicity_sq_le_stretchingResidual
    (u w : C(Torus3, Vec3)) (frame : Vec3) (epsilon : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hepsilon : 0 < epsilon) :
    (∫ x : Torus3,
      (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
        inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
      (∫ _x : Torus3, (1 : ℝ)) *
        ∫ x : Torus3,
          ‖periodicVorticityWeightedCenteredVelocityVector u w frame x +
              (((∫ y : Torus3, torusStretchingProduction u w y) /
                  torusVorticitySelfTransportQuotient w) •
                periodicNormalizedVorticitySelfTransportVector w x)‖ ^ 2 := by
  let f : Torus3 → Vec3 := periodicNormalizedVorticitySelfTransportVector w
  let g : Torus3 → Vec3 :=
    periodicVorticityWeightedCenteredVelocityVector u w frame
  let c : ℝ :=
    (∫ y : Torus3, torusStretchingProduction u w y) /
      torusVorticitySelfTransportQuotient w
  let residual : Torus3 → Vec3 := fun x => g x + c • f x
  let psiMap : C(Torus3, Vec3) :=
    ⟨fun x => (‖w x‖ / (‖w x‖ ^ 2 + 2 * epsilon)) • w x, by
      have hscalar : Continuous
          (fun x : Torus3 => ‖w x‖ / (‖w x‖ ^ 2 + 2 * epsilon)) := by
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro x
          exact (by positivity : ‖w x‖ ^ 2 + 2 * epsilon ≠ 0)
      exact hscalar.smul w.continuous⟩
  have hquotient :=
    memLp_sqrt_periodicVorticitySelfTransportQuotientSq_of_contDiff w hw
  have hquotientInt : Integrable
      (periodicVorticitySelfTransportQuotientSq w) := by
    simpa only [Real.sq_sqrt
      (periodicVorticitySelfTransportQuotientSq_nonneg w _)] using
        hquotient.integrable_sq
  have hfSq : Integrable (fun x : Torus3 => ‖f x‖ ^ 2) :=
    hquotientInt.congr (Eventually.of_forall fun x =>
      (periodicNormalizedVorticitySelfTransportVector_norm_sq w x).symm)
  have hfMeas : AEStronglyMeasurable f volume := by
    exact (measurable_periodicNormalizedVorticitySelfTransportVector_of_contDiff
      w hw).aestronglyMeasurable
  have hfLp : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq_norm hfMeas).2 hfSq
  let gMap : C(Torus3, Vec3) := ⟨g, by
    dsimp [g]
    unfold periodicVorticityWeightedCenteredVelocityVector centeredVelocity
    fun_prop⟩
  have hgLp : MemLp g 2 volume := by
    change MemLp (gMap : Torus3 → Vec3) 2 volume
    exact gMap.memLp_torus_volume 2
  have hresidualLp : MemLp residual 2 volume := by
    exact hgLp.add (hfLp.const_smul c)
  have hpsiLp : MemLp (psiMap : Torus3 → Vec3) 2 volume :=
    psiMap.memLp_torus_volume 2
  have hpsiSqLe : (∫ x : Torus3, ‖psiMap x‖ ^ 2) ≤
      ∫ _x : Torus3, (1 : ℝ) := by
    apply integral_mono hpsiLp.norm.integrable_sq (integrable_const (1 : ℝ))
    intro x
    have hratioNonneg :
        0 ≤ ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon) := by positivity
    have hratioLe :
        ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith
    have hnorm : ‖psiMap x‖ =
        ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon) := by
      dsimp [psiMap]
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      ring
    change ‖psiMap x‖ ^ 2 ≤ 1
    rw [hnorm]
    nlinarith [sq_nonneg
      (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon) - 1)]
  have hpairPoint : ∀ x : Torus3,
      inner ℝ (psiMap x) (residual x) =
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
            inner ℝ (w x) (centeredVelocity u frame x) +
          (c / 2) *
            (torusVorticityTransportProduction w w x /
              (vorticityEnergyField w x + epsilon)) := by
    intro x
    by_cases hnormZero : ‖w x‖ = 0
    · have hwx : w x = 0 := norm_eq_zero.mp hnormZero
      have hself : periodicVorticitySelfTransportVector w x = 0 := by
        ext i
        simp [periodicVorticitySelfTransportVector, torusScalarTransport, hwx]
      simp [psiMap, residual, f, g,
        periodicNormalizedVorticitySelfTransportVector,
        periodicVorticityWeightedCenteredVelocityVector,
        hwx, hself, torusVorticityTransportProduction]
    · have hdenom : ‖w x‖ ^ 2 + 2 * epsilon ≠ 0 := by positivity
      have henergy : vorticityEnergyField w x + epsilon ≠ 0 := by
        exact (add_pos_of_nonneg_of_pos
          (vorticityEnergyField_nonneg w x) hepsilon).ne'
      dsimp [psiMap, residual, f, g]
      unfold periodicNormalizedVorticitySelfTransportVector
        periodicVorticityWeightedCenteredVelocityVector
      rw [real_inner_smul_left, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, real_inner_smul_right,
        inner_periodicVorticitySelfTransportVector_eq_torusVorticityTransportProduction
          w x hw]
      simp only [centeredVelocity_apply, vorticityEnergy]
      field_simp [hnormZero, hdenom, henergy]
  have hweightedInt : Integrable (fun x : Torus3 =>
      (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
        inner ℝ (w x) (centeredVelocity u frame x)) := by
    have hc : Continuous (fun x : Torus3 =>
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
          inner ℝ (w x) (centeredVelocity u frame x)) := by
      apply Continuous.mul
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · intro x
          exact (by positivity : ‖w x‖ ^ 2 + 2 * epsilon ≠ 0)
      · change Continuous (fun x : Torus3 => inner ℝ (w x) (u x - frame))
        fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hregularizedInt :=
    integrable_regularized_torusVorticityTransportProduction_div_of_contDiff
      w epsilon hw hepsilon
  have hpairIntegral : (∫ x : Torus3, inner ℝ (psiMap x) (residual x)) =
      ∫ x : Torus3,
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
          inner ℝ (w x) (centeredVelocity u frame x) := by
    calc
      (∫ x : Torus3, inner ℝ (psiMap x) (residual x)) =
          ∫ x : Torus3,
            (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
                inner ℝ (w x) (centeredVelocity u frame x) +
              (c / 2) *
                (torusVorticityTransportProduction w w x /
                  (vorticityEnergyField w x + epsilon)) := by
        exact integral_congr_ae (Eventually.of_forall hpairPoint)
      _ = (∫ x : Torus3,
            (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
              inner ℝ (w x) (centeredVelocity u frame x)) +
          ∫ x : Torus3, (c / 2) *
            (torusVorticityTransportProduction w w x /
              (vorticityEnergyField w x + epsilon)) := by
        rw [integral_add hweightedInt (hregularizedInt.const_mul (c / 2))]
      _ = (∫ x : Torus3,
            (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
              inner ℝ (w x) (centeredVelocity u frame x)) +
          (c / 2) * (∫ x : Torus3,
            torusVorticityTransportProduction w w x /
              (vorticityEnergyField w x + epsilon)) := by
        rw [integral_const_mul]
      _ = ∫ x : Torus3,
            (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
              inner ℝ (w x) (centeredVelocity u frame x) := by
        rw [integral_regularized_torusVorticityTransportProduction_div_eq_zero_of_contDiff
          w epsilon hw hdiv hepsilon, mul_zero, add_zero]
  have hcs :=
    sq_abs_integral_inner_le_integral_norm_sq_mul_integral_norm_sq
      hpsiLp hresidualLp
  rw [hpairIntegral, sq_abs] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hpsiSqLe
    (integral_nonneg fun _ => sq_nonneg _))

/-- For every continuous localization weight, the weighted cutoff helicity
plus its explicit normalized self-transport correction is controlled by the
Cauchy residual.  No invariance hypothesis on the weight is used here. -/
theorem regularized_weighted_centered_helicity_plus_selfTransport_sq_le_stretchingResidual
    (u w : C(Torus3, Vec3)) (frame : Vec3) (phi : C(Torus3, ℝ))
    (epsilon : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w))
    (hepsilon : 0 < epsilon) :
    ((∫ x : Torus3, phi x *
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
          inner ℝ (w x) (centeredVelocity u frame x)) +
      (((∫ y : Torus3, torusStretchingProduction u w y) /
          torusVorticitySelfTransportQuotient w) / 2) *
        (∫ x : Torus3, phi x *
          (torusVorticityTransportProduction w w x /
            (vorticityEnergyField w x + epsilon)))) ^ 2 ≤
      (∫ x : Torus3, phi x ^ 2) *
        ∫ x : Torus3,
          ‖periodicVorticityWeightedCenteredVelocityVector u w frame x +
              (((∫ y : Torus3, torusStretchingProduction u w y) /
                  torusVorticitySelfTransportQuotient w) •
                periodicNormalizedVorticitySelfTransportVector w x)‖ ^ 2 := by
  let f : Torus3 → Vec3 := periodicNormalizedVorticitySelfTransportVector w
  let g : Torus3 → Vec3 :=
    periodicVorticityWeightedCenteredVelocityVector u w frame
  let c : ℝ :=
    (∫ y : Torus3, torusStretchingProduction u w y) /
      torusVorticitySelfTransportQuotient w
  let residual : Torus3 → Vec3 := fun x => g x + c • f x
  let psiMap : C(Torus3, Vec3) :=
    ⟨fun x =>
        (phi x * (‖w x‖ / (‖w x‖ ^ 2 + 2 * epsilon))) • w x, by
      have hscalar : Continuous (fun x : Torus3 =>
          phi x * (‖w x‖ / (‖w x‖ ^ 2 + 2 * epsilon))) := by
        apply phi.continuous.mul
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro x
          exact (by positivity : ‖w x‖ ^ 2 + 2 * epsilon ≠ 0)
      exact hscalar.smul w.continuous⟩
  have hquotient :=
    memLp_sqrt_periodicVorticitySelfTransportQuotientSq_of_contDiff w hw
  have hquotientInt : Integrable
      (periodicVorticitySelfTransportQuotientSq w) := by
    simpa only [Real.sq_sqrt
      (periodicVorticitySelfTransportQuotientSq_nonneg w _)] using
        hquotient.integrable_sq
  have hfSq : Integrable (fun x : Torus3 => ‖f x‖ ^ 2) :=
    hquotientInt.congr (Eventually.of_forall fun x =>
      (periodicNormalizedVorticitySelfTransportVector_norm_sq w x).symm)
  have hfMeas : AEStronglyMeasurable f volume := by
    exact (measurable_periodicNormalizedVorticitySelfTransportVector_of_contDiff
      w hw).aestronglyMeasurable
  have hfLp : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq_norm hfMeas).2 hfSq
  let gMap : C(Torus3, Vec3) := ⟨g, by
    dsimp [g]
    unfold periodicVorticityWeightedCenteredVelocityVector centeredVelocity
    fun_prop⟩
  have hgLp : MemLp g 2 volume := by
    change MemLp (gMap : Torus3 → Vec3) 2 volume
    exact gMap.memLp_torus_volume 2
  have hresidualLp : MemLp residual 2 volume := by
    exact hgLp.add (hfLp.const_smul c)
  have hpsiLp : MemLp (psiMap : Torus3 → Vec3) 2 volume :=
    psiMap.memLp_torus_volume 2
  have hpsiSqLe : (∫ x : Torus3, ‖psiMap x‖ ^ 2) ≤
      ∫ x : Torus3, phi x ^ 2 := by
    have hphiSqInt : Integrable (fun x : Torus3 => phi x ^ 2) := by
      have hc : Continuous (fun x : Torus3 => phi x ^ 2) := by fun_prop
      simpa only [IntegrableOn, Measure.restrict_univ] using
        hc.continuousOn.integrableOn_compact
          (μ := (volume : Measure Torus3))
          (isCompact_univ : IsCompact (Set.univ : Set Torus3))
    apply integral_mono hpsiLp.norm.integrable_sq hphiSqInt
    intro x
    have hratioNonneg :
        0 ≤ ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon) := by positivity
    have hratioLe :
        ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith
    have hratioSqLe :
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) ^ 2 ≤ 1 := by
      nlinarith
    have hnorm : ‖psiMap x‖ =
        |phi x| * (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) := by
      have hscalarNonneg :
          0 ≤ ‖w x‖ / (‖w x‖ ^ 2 + 2 * epsilon) := by positivity
      dsimp [psiMap]
      rw [norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hscalarNonneg]
      ring
    change ‖psiMap x‖ ^ 2 ≤ phi x ^ 2
    rw [hnorm, mul_pow, sq_abs]
    simpa using mul_le_mul_of_nonneg_left hratioSqLe (sq_nonneg (phi x))
  have hpairPoint : ∀ x : Torus3,
      inner ℝ (psiMap x) (residual x) =
        phi x *
            (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
              inner ℝ (w x) (centeredVelocity u frame x) +
          (c / 2) * (phi x *
            (torusVorticityTransportProduction w w x /
              (vorticityEnergyField w x + epsilon))) := by
    intro x
    by_cases hnormZero : ‖w x‖ = 0
    · have hwx : w x = 0 := norm_eq_zero.mp hnormZero
      have hself : periodicVorticitySelfTransportVector w x = 0 := by
        ext i
        simp [periodicVorticitySelfTransportVector, torusScalarTransport, hwx]
      simp [psiMap, residual, f, g,
        periodicNormalizedVorticitySelfTransportVector,
        periodicVorticityWeightedCenteredVelocityVector,
        hwx, hself, torusVorticityTransportProduction]
    · have hdenom : ‖w x‖ ^ 2 + 2 * epsilon ≠ 0 := by positivity
      have henergy : vorticityEnergyField w x + epsilon ≠ 0 := by
        exact (add_pos_of_nonneg_of_pos
          (vorticityEnergyField_nonneg w x) hepsilon).ne'
      dsimp [psiMap, residual, f, g]
      unfold periodicNormalizedVorticitySelfTransportVector
        periodicVorticityWeightedCenteredVelocityVector
      rw [real_inner_smul_left, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, real_inner_smul_right,
        inner_periodicVorticitySelfTransportVector_eq_torusVorticityTransportProduction
          w x hw]
      simp only [centeredVelocity_apply, vorticityEnergy]
      field_simp [hnormZero, hdenom, henergy]
  have hweightedInt : Integrable (fun x : Torus3 => phi x *
      (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
        inner ℝ (w x) (centeredVelocity u frame x)) := by
    have hc : Continuous (fun x : Torus3 => phi x *
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
          inner ℝ (w x) (centeredVelocity u frame x)) := by
      apply Continuous.mul
      · apply phi.continuous.mul
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro x
          exact (by positivity : ‖w x‖ ^ 2 + 2 * epsilon ≠ 0)
      · change Continuous (fun x : Torus3 => inner ℝ (w x) (u x - frame))
        fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hregularizedInt :=
    integrable_regularized_torusVorticityTransportProduction_div_of_contDiff
      w epsilon hw hepsilon
  have hphiRegularizedInt : Integrable (fun x : Torus3 => phi x *
      (torusVorticityTransportProduction w w x /
        (vorticityEnergyField w x + epsilon))) := by
    have hmul := hregularizedInt.mul_bdd
      phi.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm phi x)
    simpa only [mul_comm] using hmul
  have hpairIntegral : (∫ x : Torus3, inner ℝ (psiMap x) (residual x)) =
      (∫ x : Torus3, phi x *
          (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
            inner ℝ (w x) (centeredVelocity u frame x)) +
        (c / 2) * (∫ x : Torus3, phi x *
          (torusVorticityTransportProduction w w x /
            (vorticityEnergyField w x + epsilon))) := by
    calc
      (∫ x : Torus3, inner ℝ (psiMap x) (residual x)) =
          ∫ x : Torus3,
            phi x *
                (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
                  inner ℝ (w x) (centeredVelocity u frame x) +
              (c / 2) * (phi x *
                (torusVorticityTransportProduction w w x /
                  (vorticityEnergyField w x + epsilon))) := by
        exact integral_congr_ae (Eventually.of_forall hpairPoint)
      _ = (∫ x : Torus3, phi x *
              (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
                inner ℝ (w x) (centeredVelocity u frame x)) +
          ∫ x : Torus3, (c / 2) * (phi x *
            (torusVorticityTransportProduction w w x /
              (vorticityEnergyField w x + epsilon))) := by
        rw [integral_add hweightedInt (hphiRegularizedInt.const_mul (c / 2))]
      _ = (∫ x : Torus3, phi x *
              (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
                inner ℝ (w x) (centeredVelocity u frame x)) +
          (c / 2) * (∫ x : Torus3, phi x *
            (torusVorticityTransportProduction w w x /
              (vorticityEnergyField w x + epsilon))) := by
        rw [integral_const_mul]
  have hcs :=
    sq_abs_integral_inner_le_integral_norm_sq_mul_integral_norm_sq
      hpsiLp hresidualLp
  rw [hpairIntegral, sq_abs] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hpsiSqLe
    (integral_nonneg fun _ => sq_nonneg _))

/-- Quantitative approximate-localization form.  The only price for a weight
that is not exactly constant on vorticity lines is its transport paired with
the regularized logarithmic vorticity energy. -/
theorem regularized_weighted_centered_helicity_sub_transportLog_sq_le_stretchingResidual
    (u w : C(Torus3, Vec3)) (frame : Vec3) (phi : C(Torus3, ℝ))
    (epsilon : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w))
    (hphi : ContDiff ℝ 1 (torusLift phi))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hepsilon : 0 < epsilon) :
    ((∫ x : Torus3, phi x *
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
          inner ℝ (w x) (centeredVelocity u frame x)) -
      (((∫ y : Torus3, torusStretchingProduction u w y) /
          torusVorticitySelfTransportQuotient w) / 2) *
        (∫ x : Torus3, torusScalarTransport w phi x *
          regularizedLogVorticityEnergyField w epsilon hepsilon x)) ^ 2 ≤
      (∫ x : Torus3, phi x ^ 2) *
        ∫ x : Torus3,
          ‖periodicVorticityWeightedCenteredVelocityVector u w frame x +
              (((∫ y : Torus3, torusStretchingProduction u w y) /
                  torusVorticitySelfTransportQuotient w) •
                periodicNormalizedVorticitySelfTransportVector w x)‖ ^ 2 := by
  have hbase :=
    regularized_weighted_centered_helicity_plus_selfTransport_sq_le_stretchingResidual
      u w frame phi epsilon hw hepsilon
  rw [integral_mul_regularized_torusVorticityTransportProduction_div_eq_neg_transport_log
    w phi epsilon hw hphi hdiv hepsilon, mul_neg] at hbase
  simpa only [sub_eq_add_neg] using hbase

/-- A smooth first integral of the vorticity flow localizes the helicity test
to invariant vortex regions.  The logarithmic correction cancels exactly,
while the test-vector mass is the explicit weight `integral phi^2`. -/
theorem regularized_firstIntegralWeighted_centered_helicity_sq_le_stretchingResidual
    (u w : C(Torus3, Vec3)) (frame : Vec3) (phi : C(Torus3, ℝ))
    (epsilon : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w))
    (hphi : ContDiff ℝ 1 (torusLift phi))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hfirst : ∀ x : Torus3, torusScalarTransport w phi x = 0)
    (hepsilon : 0 < epsilon) :
    (∫ x : Torus3, phi x *
      (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
        inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
      (∫ x : Torus3, phi x ^ 2) *
        ∫ x : Torus3,
          ‖periodicVorticityWeightedCenteredVelocityVector u w frame x +
              (((∫ y : Torus3, torusStretchingProduction u w y) /
                  torusVorticitySelfTransportQuotient w) •
                periodicNormalizedVorticitySelfTransportVector w x)‖ ^ 2 := by
  have hbase :=
    regularized_weighted_centered_helicity_plus_selfTransport_sq_le_stretchingResidual
      u w frame phi epsilon hw hepsilon
  rw [integral_mul_regularized_torusVorticityTransportProduction_div_eq_zero_of_firstIntegral
    w phi epsilon hw hphi hdiv hfirst hepsilon, mul_zero, add_zero] at hbase
  exact hbase

/-- The zero-safe vortex-set cutoffs converge in integral to centered
helicity.  This is a dominated-convergence fact requiring only continuity of
the two torus fields. -/
theorem tendsto_integral_vorticityCutoff_centeredHelicity
    (u w : C(Torus3, Vec3)) (frame : Vec3) :
    Tendsto (fun n : ℕ => ∫ x : Torus3,
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * (1 / ((n : ℝ) + 1)))) *
          inner ℝ (w x) (centeredVelocity u frame x)) atTop
      (nhds (∫ x : Torus3,
        inner ℝ (w x) (centeredVelocity u frame x))) := by
  let epsilon : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let F : ℕ → Torus3 → ℝ := fun n x =>
    (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n)) *
      inner ℝ (w x) (centeredVelocity u frame x)
  let target : Torus3 → ℝ := fun x =>
    inner ℝ (w x) (centeredVelocity u frame x)
  let bound : Torus3 → ℝ := fun x => ‖target x‖
  have hepsilonPos : ∀ n : ℕ, 0 < epsilon n := by
    intro n
    dsimp [epsilon]
    positivity
  have hFcontinuous : ∀ n : ℕ, Continuous (F n) := by
    intro n
    dsimp [F]
    apply Continuous.mul
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        exact (by positivity : ‖w x‖ ^ 2 + 2 * epsilon n ≠ 0)
    · fun_prop
  have hboundContinuous : Continuous bound := by
    dsimp [bound, target]
    fun_prop
  have hboundIntegrable : Integrable bound := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hboundContinuous.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hdominated : ∀ n : ℕ, ∀ᵐ x : Torus3 ∂volume, ‖F n x‖ ≤ bound x := by
    intro n
    exact Eventually.of_forall fun x => by
      have hratioNonneg :
          0 ≤ ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n) := by
        positivity
      have hratioLe :
          ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        linarith [hepsilonPos n]
      dsimp [F, bound, target]
      rw [abs_mul, abs_of_nonneg hratioNonneg]
      exact mul_le_of_le_one_left (abs_nonneg _) hratioLe
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hpointwise : ∀ᵐ x : Torus3 ∂volume,
      Tendsto (fun n => F n x) atTop (nhds (target x)) := by
    exact Eventually.of_forall fun x => by
      by_cases hr : ‖w x‖ ^ 2 = 0
      · have hwx : w x = 0 := by
          exact norm_eq_zero.mp (sq_eq_zero_iff.mp hr)
        simp only [F, target, hwx, norm_zero, mul_zero, inner_zero_left]
        exact tendsto_const_nhds (x := (0 : ℝ))
      · have hdenom : Tendsto
            (fun n => ‖w x‖ ^ 2 + 2 * epsilon n) atTop
            (nhds (‖w x‖ ^ 2)) := by
          have hconst : Tendsto (fun _ : ℕ => ‖w x‖ ^ 2) atTop
              (nhds (‖w x‖ ^ 2)) := tendsto_const_nhds
          have htwo : Tendsto (fun n : ℕ => 2 * epsilon n) atTop (nhds 0) := by
            simpa using
              (tendsto_const_nhds (x := (2 : ℝ))).mul hepsilonZero
          simpa using hconst.add htwo
        have hratio : Tendsto
            (fun n => ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n)) atTop
            (nhds 1) := by
          have hconst : Tendsto (fun _ : ℕ => ‖w x‖ ^ 2) atTop
              (nhds (‖w x‖ ^ 2)) := tendsto_const_nhds
          have hraw := hconst.div hdenom hr
          change Tendsto
            (fun n : ℕ => ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n)) atTop
            (nhds (‖w x‖ ^ 2 / ‖w x‖ ^ 2)) at hraw
          simpa [div_self hr] using hraw
        dsimp [F, target]
        have hinner : Tendsto
            (fun _ : ℕ => inner ℝ (w x) (centeredVelocity u frame x)) atTop
            (nhds (inner ℝ (w x) (centeredVelocity u frame x))) :=
          tendsto_const_nhds
        simpa using hratio.mul hinner
  have hlimit : Tendsto (fun n => ∫ x : Torus3, F n x) atTop
      (nhds (∫ x : Torus3, target x)) :=
    tendsto_integral_of_dominated_convergence bound
      (fun n => (hFcontinuous n).aestronglyMeasurable)
      hboundIntegrable hdominated hpointwise
  simpa [epsilon, F, target] using hlimit

/-- The zero-safe vortex-set cutoffs also converge after multiplication by
an arbitrary continuous scalar weight.  In the first-integral application,
this weight separates helicity carried by distinct invariant vortex regions. -/
theorem tendsto_integral_vorticityCutoff_weighted_centeredHelicity
    (u w : C(Torus3, Vec3)) (frame : Vec3) (phi : C(Torus3, ℝ)) :
    Tendsto (fun n : ℕ => ∫ x : Torus3, phi x *
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * (1 / ((n : ℝ) + 1)))) *
          inner ℝ (w x) (centeredVelocity u frame x)) atTop
      (nhds (∫ x : Torus3, phi x *
        inner ℝ (w x) (centeredVelocity u frame x))) := by
  let epsilon : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let target : Torus3 → ℝ := fun x =>
    phi x * inner ℝ (w x) (centeredVelocity u frame x)
  let F : ℕ → Torus3 → ℝ := fun n x =>
    (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n)) * target x
  let bound : Torus3 → ℝ := fun x => ‖target x‖
  have hepsilonPos : ∀ n : ℕ, 0 < epsilon n := by
    intro n
    dsimp [epsilon]
    positivity
  have hFcontinuous : ∀ n : ℕ, Continuous (F n) := by
    intro n
    dsimp [F, target]
    apply Continuous.mul
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        exact (by positivity : ‖w x‖ ^ 2 + 2 * epsilon n ≠ 0)
    · fun_prop
  have hboundContinuous : Continuous bound := by
    dsimp [bound, target]
    fun_prop
  have hboundIntegrable : Integrable bound := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hboundContinuous.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hdominated : ∀ n : ℕ, ∀ᵐ x : Torus3 ∂volume, ‖F n x‖ ≤ bound x := by
    intro n
    exact Eventually.of_forall fun x => by
      have hratioNonneg :
          0 ≤ ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n) := by
        positivity
      have hratioLe :
          ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        linarith [hepsilonPos n]
      dsimp [F, bound]
      rw [abs_mul, abs_of_nonneg hratioNonneg]
      exact mul_le_of_le_one_left (abs_nonneg _) hratioLe
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hpointwise : ∀ᵐ x : Torus3 ∂volume,
      Tendsto (fun n => F n x) atTop (nhds (target x)) := by
    exact Eventually.of_forall fun x => by
      by_cases hr : ‖w x‖ ^ 2 = 0
      · have hwx : w x = 0 := by
          exact norm_eq_zero.mp (sq_eq_zero_iff.mp hr)
        simp only [F, target, hwx, norm_zero, mul_zero, inner_zero_left]
        exact tendsto_const_nhds (x := (0 : ℝ))
      · have hdenom : Tendsto
            (fun n => ‖w x‖ ^ 2 + 2 * epsilon n) atTop
            (nhds (‖w x‖ ^ 2)) := by
          have hconst : Tendsto (fun _ : ℕ => ‖w x‖ ^ 2) atTop
              (nhds (‖w x‖ ^ 2)) := tendsto_const_nhds
          have htwo : Tendsto (fun n : ℕ => 2 * epsilon n) atTop (nhds 0) := by
            simpa using
              (tendsto_const_nhds (x := (2 : ℝ))).mul hepsilonZero
          simpa using hconst.add htwo
        have hratio : Tendsto
            (fun n => ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n)) atTop
            (nhds 1) := by
          have hconst : Tendsto (fun _ : ℕ => ‖w x‖ ^ 2) atTop
              (nhds (‖w x‖ ^ 2)) := tendsto_const_nhds
          have hraw := hconst.div hdenom hr
          change Tendsto
            (fun n : ℕ => ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n)) atTop
            (nhds (‖w x‖ ^ 2 / ‖w x‖ ^ 2)) at hraw
          simpa [div_self hr] using hraw
        dsimp [F]
        simpa using hratio.mul (tendsto_const_nhds (x := target x))
  have hlimit : Tendsto (fun n => ∫ x : Torus3, F n x) atTop
      (nhds (∫ x : Torus3, target x)) :=
    tendsto_integral_of_dominated_convergence bound
      (fun n => (hFcontinuous n).aestronglyMeasurable)
      hboundIntegrable hdominated hpointwise
  simpa [epsilon, F, target, mul_assoc, mul_left_comm, mul_comm] using hlimit

/-- Quantitative rigidity: centered helicity gives an explicit lower bound on
the Cauchy defect.  Equivalently, any nonzero-helicity slice with nonzero
self-transport quotient is uniformly separated from exact factorization
saturation by `Q H² / volume(T³)`. -/
theorem torus_stretchingCauchyDefect_centered_helicity_lower_bound
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0) :
    torusVorticitySelfTransportQuotient w *
        (∫ x : Torus3,
          inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
      (∫ _x : Torus3, (1 : ℝ)) *
        (torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2) := by
  let residual : Torus3 → Vec3 := fun x =>
    periodicVorticityWeightedCenteredVelocityVector u w frame x +
      (((∫ y : Torus3, torusStretchingProduction u w y) /
          torusVorticitySelfTransportQuotient w) •
        periodicNormalizedVorticitySelfTransportVector w x)
  have hlimit :=
    tendsto_integral_vorticityCutoff_centeredHelicity u w frame
  have hlimitSq := hlimit.pow 2
  have hregularized : ∀ n : ℕ,
      (∫ x : Torus3,
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * (1 / ((n : ℝ) + 1)))) *
          inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
        (∫ _x : Torus3, (1 : ℝ)) *
          ∫ x : Torus3, ‖residual x‖ ^ 2 := by
    intro n
    exact regularized_centered_helicity_sq_le_stretchingResidual
      u w frame (1 / ((n : ℝ) + 1)) hw hdiv (by positivity)
  have hlimitBound :
      (∫ x : Torus3,
        inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
        (∫ _x : Torus3, (1 : ℝ)) *
          ∫ x : Torus3, ‖residual x‖ ^ 2 :=
    le_of_tendsto hlimitSq (Eventually.of_forall hregularized)
  have hquotientNonneg : 0 ≤ torusVorticitySelfTransportQuotient w :=
    integral_nonneg fun x => periodicVorticitySelfTransportQuotientSq_nonneg w x
  have hscaled := mul_le_mul_of_nonneg_left hlimitBound hquotientNonneg
  have hresidualIdentity :=
    torus_stretchingCauchyDefect_eq_scaledResidual_of_contDiff
      u w frame hu hw hdiv hquotientNe
  calc
    torusVorticitySelfTransportQuotient w *
          (∫ x : Torus3,
            inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
        torusVorticitySelfTransportQuotient w *
          ((∫ _x : Torus3, (1 : ℝ)) *
            ∫ x : Torus3, ‖residual x‖ ^ 2) := hscaled
    _ = (∫ _x : Torus3, (1 : ℝ)) *
        (torusVorticitySelfTransportQuotient w *
          ∫ x : Torus3, ‖residual x‖ ^ 2) := by ring
    _ = (∫ _x : Torus3, (1 : ℝ)) *
        (torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2) := by
      rw [hresidualIdentity]

/-- First-integral localization of the quantitative helicity gap.  If `phi`
is transported exactly by the divergence-free vorticity field, then weighted
helicity on its invariant vortex regions controls the global Cauchy defect. -/
theorem torus_stretchingCauchyDefect_firstIntegralWeighted_centered_helicity_lower_bound
    (u w : C(Torus3, Vec3)) (frame : Vec3) (phi : C(Torus3, ℝ))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hphi : ContDiff ℝ 1 (torusLift phi))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hfirst : ∀ x : Torus3, torusScalarTransport w phi x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0) :
    torusVorticitySelfTransportQuotient w *
        (∫ x : Torus3, phi x *
          inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
      (∫ x : Torus3, phi x ^ 2) *
        (torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2) := by
  let residual : Torus3 → Vec3 := fun x =>
    periodicVorticityWeightedCenteredVelocityVector u w frame x +
      (((∫ y : Torus3, torusStretchingProduction u w y) /
          torusVorticitySelfTransportQuotient w) •
        periodicNormalizedVorticitySelfTransportVector w x)
  have hlimit :=
    tendsto_integral_vorticityCutoff_weighted_centeredHelicity
      u w frame phi
  have hlimitSq := hlimit.pow 2
  have hregularized : ∀ n : ℕ,
      (∫ x : Torus3, phi x *
        (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * (1 / ((n : ℝ) + 1)))) *
          inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
        (∫ x : Torus3, phi x ^ 2) *
          ∫ x : Torus3, ‖residual x‖ ^ 2 := by
    intro n
    exact
      regularized_firstIntegralWeighted_centered_helicity_sq_le_stretchingResidual
        u w frame phi (1 / ((n : ℝ) + 1)) hw hphi hdiv hfirst
          (by positivity)
  have hlimitBound :
      (∫ x : Torus3, phi x *
        inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
        (∫ x : Torus3, phi x ^ 2) *
          ∫ x : Torus3, ‖residual x‖ ^ 2 :=
    le_of_tendsto hlimitSq (Eventually.of_forall hregularized)
  have hquotientNonneg : 0 ≤ torusVorticitySelfTransportQuotient w :=
    integral_nonneg fun x => periodicVorticitySelfTransportQuotientSq_nonneg w x
  have hscaled := mul_le_mul_of_nonneg_left hlimitBound hquotientNonneg
  have hresidualIdentity :=
    torus_stretchingCauchyDefect_eq_scaledResidual_of_contDiff
      u w frame hu hw hdiv hquotientNe
  calc
    torusVorticitySelfTransportQuotient w *
          (∫ x : Torus3, phi x *
            inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 ≤
        torusVorticitySelfTransportQuotient w *
          ((∫ x : Torus3, phi x ^ 2) *
            ∫ x : Torus3, ‖residual x‖ ^ 2) := hscaled
    _ = (∫ x : Torus3, phi x ^ 2) *
        (torusVorticitySelfTransportQuotient w *
          ∫ x : Torus3, ‖residual x‖ ^ 2) := by ring
    _ = (∫ x : Torus3, phi x ^ 2) *
        (torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2) := by
      rw [hresidualIdentity]

/-- Robust localized defect gap for an approximately invariant vortex-tube
weight.  Localized helicity remains coercive after paying the `L¹` transport
of the weight times a freely centered logarithmic-energy oscillation. -/
theorem torus_stretchingCauchyDefect_approxFirstIntegralWeighted_regularized_lower_bound
    (u w : C(Torus3, Vec3)) (frame : Vec3) (phi : C(Torus3, ℝ))
    (epsilon k : ℝ)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hphi : ContDiff ℝ 1 (torusLift phi))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0)
    (hepsilon : 0 < epsilon) :
    torusVorticitySelfTransportQuotient w *
        (max
          (|∫ x : Torus3, phi x *
              (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
                inner ℝ (w x) (centeredVelocity u frame x)| -
            |((∫ y : Torus3, torusStretchingProduction u w y) /
                torusVorticitySelfTransportQuotient w) / 2| *
              ((∫ x : Torus3, |torusScalarTransport w phi x|) *
                ‖regularizedLogVorticityEnergyField w epsilon hepsilon -
                  ContinuousMap.const Torus3 k‖)) 0) ^ 2 ≤
      (∫ x : Torus3, phi x ^ 2) *
        (torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2) := by
  let Q : ℝ := torusVorticitySelfTransportQuotient w
  let N : ℝ := ∫ x : Torus3, torusStretchingProduction u w x
  let A : ℝ := ∫ x : Torus3, phi x ^ 2
  let D : ℝ :=
    Q * periodicVorticityWeightedVelocityVariance u w frame - N ^ 2
  let H : ℝ := ∫ x : Torus3, phi x *
    (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
      inner ℝ (w x) (centeredVelocity u frame x)
  let J : ℝ := ∫ x : Torus3, torusScalarTransport w phi x *
    regularizedLogVorticityEnergyField w epsilon hepsilon x
  let c : ℝ := N / Q / 2
  let B : ℝ :=
    (∫ x : Torus3, |torusScalarTransport w phi x|) *
      ‖regularizedLogVorticityEnergyField w epsilon hepsilon -
        ContinuousMap.const Torus3 k‖
  let residual : Torus3 → Vec3 := fun x =>
    periodicVorticityWeightedCenteredVelocityVector u w frame x +
      ((N / Q) • periodicNormalizedVorticitySelfTransportVector w x)
  have hregularized :
      (H - c * J) ^ 2 ≤ A *
        ∫ x : Torus3, ‖residual x‖ ^ 2 := by
    simpa [H, c, J, A, N, Q, residual] using
      (regularized_weighted_centered_helicity_sub_transportLog_sq_le_stretchingResidual
        u w frame phi epsilon hw hphi hdiv hepsilon)
  have hquotientNonneg : 0 ≤ Q := by
    dsimp [Q]
    exact integral_nonneg fun x =>
      periodicVorticitySelfTransportQuotientSq_nonneg w x
  have hscaled :=
    mul_le_mul_of_nonneg_left hregularized hquotientNonneg
  have hresidualIdentity : D = Q *
      ∫ x : Torus3, ‖residual x‖ ^ 2 := by
    simpa [D, Q, N, residual] using
      (torus_stretchingCauchyDefect_eq_scaledResidual_of_contDiff
        u w frame hu hw hdiv hquotientNe)
  have hcorrected : Q * (H - c * J) ^ 2 ≤ A * D := by
    calc
      Q * (H - c * J) ^ 2 ≤
          Q * (A * ∫ x : Torus3, ‖residual x‖ ^ 2) := hscaled
      _ = A * (Q * ∫ x : Torus3, ‖residual x‖ ^ 2) := by ring
      _ = A * D := by rw [← hresidualIdentity]
  have herror : |J| ≤ B := by
    dsimp [J, B]
    exact abs_integral_transport_mul_regularizedLog_le_centeredSup
      w phi epsilon k hw hphi hdiv hepsilon
  have hrobust := robustLocalizedDefectGap_of_transportError
    Q A D H c J B hquotientNonneg hcorrected herror
  simpa [Q, N, A, D, H, c, B] using hrobust

/-- Exact quotient saturation annihilates every smooth first-integral-weighted
centered helicity, not merely the globally averaged helicity. -/
theorem torus_stretchingCauchyDefect_zero_implies_firstIntegralWeighted_centered_helicity_eq_zero
    (u w : C(Torus3, Vec3)) (frame : Vec3) (phi : C(Torus3, ℝ))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hphi : ContDiff ℝ 1 (torusLift phi))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hfirst : ∀ x : Torus3, torusScalarTransport w phi x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0)
    (hzero :
      torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 = 0) :
    (∫ x : Torus3, phi x *
      inner ℝ (w x) (centeredVelocity u frame x)) = 0 := by
  have hgap :=
    torus_stretchingCauchyDefect_firstIntegralWeighted_centered_helicity_lower_bound
      u w frame phi hu hw hphi hdiv hfirst hquotientNe
  rw [hzero, mul_zero] at hgap
  have hquotientNonneg : 0 ≤ torusVorticitySelfTransportQuotient w :=
    integral_nonneg fun x => periodicVorticitySelfTransportQuotientSq_nonneg w x
  have hquotientPos : 0 < torusVorticitySelfTransportQuotient w :=
    lt_of_le_of_ne hquotientNonneg (Ne.symm hquotientNe)
  have hsquare :
      (∫ x : Torus3, phi x *
        inner ℝ (w x) (centeredVelocity u frame x)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (∫ x : Torus3, phi x *
      inner ℝ (w x) (centeredVelocity u frame x))]
  exact sq_eq_zero_iff.mp hsquare

/-- At every positive regularization scale, saturation forces the centered
helicity to vanish after multiplication by the zero-safe vortex-set cutoff
`|w|² / (|w|² + 2 epsilon)`. -/
theorem torus_stretchingCauchyDefect_zero_implies_regularized_centered_helicity
    (u w : C(Torus3, Vec3)) (frame : Vec3) (epsilon : ℝ)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0)
    (hzero :
      torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 = 0)
    (hepsilon : 0 < epsilon) :
    (∫ x : Torus3,
      (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
        inner ℝ (w x) (centeredVelocity u frame x)) = 0 := by
  let c : ℝ :=
    (∫ y : Torus3, torusStretchingProduction u w y) /
      torusVorticitySelfTransportQuotient w
  have hparallel :=
    (torus_stretchingCauchyDefect_zero_implies_ae_parallel_projected_rigidity
      u w frame hu hw hdiv hquotientNe hzero).1
  have hpoint : (fun x : Torus3 =>
      (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
        inner ℝ (w x) (centeredVelocity u frame x)) =ᵐ[volume]
      (fun x : Torus3 =>
        -(c / 2) *
          (torusVorticityTransportProduction w w x /
            (vorticityEnergyField w x + epsilon))) := by
    filter_upwards [hparallel] with x hx
    simp only [Pi.zero_apply] at hx
    change ‖w x‖ ^ 2 * inner ℝ (w x) (centeredVelocity u frame x) +
        c * inner ℝ (w x) (periodicVorticitySelfTransportVector w x) = 0 at hx
    rw [inner_periodicVorticitySelfTransportVector_eq_torusVorticityTransportProduction
      w x hw] at hx
    have hdenomPos : 0 < ‖w x‖ ^ 2 + 2 * epsilon := by positivity
    have henergyPos : 0 < vorticityEnergyField w x + epsilon := by
      exact add_pos_of_nonneg_of_pos (vorticityEnergyField_nonneg w x) hepsilon
    simp only [vorticityEnergyField_apply, vorticityEnergy]
    field_simp [hdenomPos.ne', henergyPos.ne']
    nlinarith
  calc
    (∫ x : Torus3,
      (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon)) *
        inner ℝ (w x) (centeredVelocity u frame x)) =
        ∫ x : Torus3,
          -(c / 2) *
            (torusVorticityTransportProduction w w x /
              (vorticityEnergyField w x + epsilon)) :=
      integral_congr_ae hpoint
    _ = -(c / 2) *
        (∫ x : Torus3,
          torusVorticityTransportProduction w w x /
            (vorticityEnergyField w x + epsilon)) := by
      rw [integral_const_mul]
    _ = 0 := by
      rw [integral_regularized_torusVorticityTransportProduction_div_eq_zero_of_contDiff
        w epsilon hw hdiv hepsilon, mul_zero]

/-- Exact saturation of the smooth quotient factorization forces zero total
centered helicity.  The proof sends the regularized vortex-set cutoff to one
by dominated convergence; the zero-vorticity set is harmless because the
helicity density itself vanishes there. -/
theorem torus_stretchingCauchyDefect_zero_implies_centered_helicity_eq_zero
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0)
    (hzero :
      torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 = 0) :
    (∫ x : Torus3, inner ℝ (w x) (centeredVelocity u frame x)) = 0 := by
  let epsilon : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let F : ℕ → Torus3 → ℝ := fun n x =>
    (‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n)) *
      inner ℝ (w x) (centeredVelocity u frame x)
  let target : Torus3 → ℝ := fun x =>
    inner ℝ (w x) (centeredVelocity u frame x)
  let bound : Torus3 → ℝ := fun x => ‖target x‖
  have hepsilonPos : ∀ n : ℕ, 0 < epsilon n := by
    intro n
    dsimp [epsilon]
    positivity
  have hFcontinuous : ∀ n : ℕ, Continuous (F n) := by
    intro n
    dsimp [F]
    apply Continuous.mul
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        exact (by positivity : ‖w x‖ ^ 2 + 2 * epsilon n ≠ 0)
    · fun_prop
  have hboundContinuous : Continuous bound := by
    dsimp [bound, target]
    fun_prop
  have hboundIntegrable : Integrable bound := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hboundContinuous.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hdominated : ∀ n : ℕ, ∀ᵐ x : Torus3 ∂volume, ‖F n x‖ ≤ bound x := by
    intro n
    exact Eventually.of_forall fun x => by
      have hratioNonneg :
          0 ≤ ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n) := by
        positivity
      have hratioLe :
          ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        linarith [hepsilonPos n]
      dsimp [F, bound, target]
      rw [abs_mul, abs_of_nonneg hratioNonneg]
      exact mul_le_of_le_one_left (abs_nonneg _) hratioLe
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hpointwise : ∀ᵐ x : Torus3 ∂volume,
      Tendsto (fun n => F n x) atTop (nhds (target x)) := by
    exact Eventually.of_forall fun x => by
      by_cases hr : ‖w x‖ ^ 2 = 0
      · have hwx : w x = 0 := by
          exact norm_eq_zero.mp (sq_eq_zero_iff.mp hr)
        simp only [F, target, hwx, norm_zero, mul_zero, inner_zero_left]
        exact tendsto_const_nhds (x := (0 : ℝ))
      · have hdenom : Tendsto
            (fun n => ‖w x‖ ^ 2 + 2 * epsilon n) atTop
            (nhds (‖w x‖ ^ 2)) := by
          have hconst : Tendsto (fun _ : ℕ => ‖w x‖ ^ 2) atTop
              (nhds (‖w x‖ ^ 2)) := tendsto_const_nhds
          have htwo : Tendsto (fun n : ℕ => 2 * epsilon n) atTop (nhds 0) := by
            simpa using
              (tendsto_const_nhds (x := (2 : ℝ))).mul hepsilonZero
          simpa using hconst.add htwo
        have hratio : Tendsto
            (fun n => ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n)) atTop
            (nhds 1) := by
          have hconst : Tendsto (fun _ : ℕ => ‖w x‖ ^ 2) atTop
              (nhds (‖w x‖ ^ 2)) := tendsto_const_nhds
          have hraw := hconst.div hdenom hr
          change Tendsto
            (fun n : ℕ => ‖w x‖ ^ 2 / (‖w x‖ ^ 2 + 2 * epsilon n)) atTop
            (nhds (‖w x‖ ^ 2 / ‖w x‖ ^ 2)) at hraw
          simpa [div_self hr] using hraw
        dsimp [F, target]
        have hinner : Tendsto
            (fun _ : ℕ => inner ℝ (w x) (centeredVelocity u frame x)) atTop
            (nhds (inner ℝ (w x) (centeredVelocity u frame x))) :=
          tendsto_const_nhds
        simpa using hratio.mul hinner
  have hintegralLimit : Tendsto (fun n => ∫ x : Torus3, F n x) atTop
      (nhds (∫ x : Torus3, target x)) :=
    tendsto_integral_of_dominated_convergence bound
      (fun n => (hFcontinuous n).aestronglyMeasurable)
      hboundIntegrable hdominated hpointwise
  have hintegralZero : Tendsto (fun n => ∫ x : Torus3, F n x) atTop
      (nhds 0) := by
    have heq : (fun n => ∫ x : Torus3, F n x) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact torus_stretchingCauchyDefect_zero_implies_regularized_centered_helicity
        u w frame (epsilon n) hu hw hdiv hquotientNe hzero (hepsilonPos n)
    rw [heq]
    exact tendsto_const_nhds
  have hunique := tendsto_nhds_unique hintegralZero hintegralLimit
  simpa [target] using hunique.symm

/-- A constant Galilean frame does not change integrated helicity when the
vorticity field has zero mean in each component. -/
theorem integral_inner_centeredVelocity_eq_of_mean_zero
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hmean : ∀ i : Fin 3, (∫ x : Torus3, w x i) = 0) :
    (∫ x : Torus3, inner ℝ (w x) (centeredVelocity u frame x)) =
      ∫ x : Torus3, inner ℝ (w x) (u x) := by
  have huncenteredInt : Integrable (fun x : Torus3 => inner ℝ (w x) (u x)) := by
    have hc : Continuous (fun x : Torus3 => inner ℝ (w x) (u x)) := by fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hframeInt : Integrable (fun x : Torus3 => inner ℝ (w x) frame) := by
    have hc : Continuous (fun x : Torus3 => inner ℝ (w x) frame) := by fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hframeZero : (∫ x : Torus3, inner ℝ (w x) frame) = 0 := by
    simp only [PiLp.inner_apply, Real.inner_apply]
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro i _hi
      rw [integral_mul_const, hmean i, zero_mul]
    · intro i _hi
      have hc : Continuous (fun x : Torus3 => w x i * frame i) := by fun_prop
      simpa only [IntegrableOn, Measure.restrict_univ] using
        hc.continuousOn.integrableOn_compact
          (μ := (volume : Measure Torus3))
          (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  calc
    (∫ x : Torus3, inner ℝ (w x) (centeredVelocity u frame x)) =
        ∫ x : Torus3, inner ℝ (w x) (u x) - inner ℝ (w x) frame := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change inner ℝ (w x) (u x - frame) = _
        rw [inner_sub_right]
    _ = (∫ x : Torus3, inner ℝ (w x) (u x)) -
        ∫ x : Torus3, inner ℝ (w x) frame := by
      rw [integral_sub huncenteredInt hframeInt]
    _ = ∫ x : Torus3, inner ℝ (w x) (u x) := by rw [hframeZero, sub_zero]

/-- Saturation forces zero ordinary helicity whenever the vorticity has zero
spatial mean. -/
theorem torus_stretchingCauchyDefect_zero_implies_helicity_eq_zero_of_mean_zero
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hmean : ∀ i : Fin 3, (∫ x : Torus3, w x i) = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0)
    (hzero :
      torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 = 0) :
    (∫ x : Torus3, inner ℝ (w x) (u x)) = 0 := by
  rw [← integral_inner_centeredVelocity_eq_of_mean_zero u w frame hmean]
  exact torus_stretchingCauchyDefect_zero_implies_centered_helicity_eq_zero
    u w frame hu hw hdiv hquotientNe hzero

/-- For a genuine periodic curl field, componentwise zero mean is automatic;
therefore exact quotient saturation forces zero total fluid helicity. -/
theorem torus_stretchingCauchyDefect_zero_implies_helicity_eq_zero_of_eq_torusCurl
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hcurl : ∀ x : Torus3, w x = torusCurl u x)
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0)
    (hzero :
      torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 = 0) :
    (∫ x : Torus3, inner ℝ (w x) (u x)) = 0 := by
  have hmean : ∀ i : Fin 3, (∫ x : Torus3, w x i) = 0 :=
    torusCurlField_mean_zero u w hcurl hu
      (fun i k y =>
        contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
          u i k y hu)
      (fun i k => integrable_periodicFirstDerivative_sq_of_contDiff u i k hu)
  exact
    torus_stretchingCauchyDefect_zero_implies_helicity_eq_zero_of_mean_zero
      u w frame hu hw hdiv hmean hquotientNe hzero

/-- Quantitative ordinary-helicity gap for a genuine periodic curl field.
The mean-zero curl identity removes the Galilean frame from the centered
helicity lower bound. -/
theorem torus_stretchingCauchyDefect_helicity_lower_bound_of_eq_torusCurl
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hcurl : ∀ x : Torus3, w x = torusCurl u x)
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotientNe : torusVorticitySelfTransportQuotient w ≠ 0) :
    torusVorticitySelfTransportQuotient w *
        (∫ x : Torus3, inner ℝ (w x) (u x)) ^ 2 ≤
      (∫ _x : Torus3, (1 : ℝ)) *
        (torusVorticitySelfTransportQuotient w *
            periodicVorticityWeightedVelocityVariance u w frame -
          (∫ x : Torus3, torusStretchingProduction u w x) ^ 2) := by
  have hmean : ∀ i : Fin 3, (∫ x : Torus3, w x i) = 0 :=
    torusCurlField_mean_zero u w hcurl hu
      (fun i k y =>
        contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
          u i k y hu)
      (fun i k => integrable_periodicFirstDerivative_sq_of_contDiff u i k hu)
  rw [← integral_inner_centeredVelocity_eq_of_mean_zero u w frame hmean]
  exact torus_stretchingCauchyDefect_centered_helicity_lower_bound
    u w frame hu hw hdiv hquotientNe

/-- Rewrite the integral form of the enstrophy balance as the named scalar rate. -/
theorem hasDerivAt_torusEnstrophyRate_of_balance
    {viscosity t : ℝ} {u w : C(Torus3, Vec3)} {E : ℝ → ℝ}
    (hbalance : HasDerivAt E
      (∫ x : Torus3,
        torusStretchingProduction u w x -
          viscosity * torusPalinstrophyDensity w x) t)
    (hS : Integrable (torusStretchingProduction u w))
    (hP : Integrable (torusPalinstrophyDensity w)) :
    HasDerivAt E (torusEnstrophyRate viscosity u w) t := by
  apply hbalance.congr_deriv
  unfold torusEnstrophyRate torusPalinstrophy
  calc
    (∫ x : Torus3,
        torusStretchingProduction u w x -
          viscosity * torusPalinstrophyDensity w x) =
        (∫ x : Torus3, torusStretchingProduction u w x) -
          (∫ x : Torus3, viscosity * torusPalinstrophyDensity w x) := by
      exact MeasureTheory.integral_sub hS (hP.const_mul viscosity)
    _ = (∫ x : Torus3, torusStretchingProduction u w x) -
        viscosity * (∫ x : Torus3, torusPalinstrophyDensity w x) := by
      rw [MeasureTheory.integral_const_mul]

/-- The named scalar rate is obtained from the actual classical
Navier--Stokes/vorticity predicates and concrete periodic integration by parts. -/
theorem hasDerivAt_torusEnstrophyRate_of_classicalNavierStokes
    {viscosity a b : ℝ}
    {u uTime w wTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsClassicalNavierStokesOn viscosity a b u uTime p)
    (hwEquation : IsClassicalVorticityEquationOn
      viscosity a b u w wTime)
    {t : ℝ} (ht : t ∈ Ico a b)
    (hS : Integrable (torusStretchingProduction (u t) (w t)))
    (hL : Integrable
      (torusScalarLaplacian (vorticityEnergyField (w t))))
    (hP : Integrable (torusPalinstrophyDensity (w t)))
    (hT : Integrable (torusVorticityTransportProduction (u t) (w t)))
    (henergySlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 2
        (torusCoordinateSliceLift (vorticityEnergyField (w t)) i y))
    (hsecond : ∀ i : Fin 3, Integrable
      (torusCoordinateSecondDerivative (vorticityEnergyField (w t)) i))
    (huSlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u t x i) i y))
    (htransportLeft : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      (((1 : ℝ) * u t x i) *
        torusCoordinateDerivative (vorticityEnergyField (w t)) i x)))
    (htransportRight : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => (1 : ℝ) * u t z i) i x *
        vorticityEnergyField (w t) x)) :
    HasDerivAt (fun r => torusEnstrophy (w r))
      (torusEnstrophyRate viscosity (u t) (w t)) t := by
  apply hasDerivAt_torusEnstrophyRate_of_balance
    (hasDerivAt_torusEnstrophy_balance_of_classicalNavierStokes
      hNS hwEquation ht hS hL hP hT henergySlices hsecond huSlices
      htransportLeft htransportRight) hS hP

/-- Streamlined extraction of the enstrophy rate from the concrete PDEs.
Compactness and smoothness discharge every coordinate-slice and integrability
premise, including the descended second derivatives of `|w|²/2`. -/
theorem hasDerivAt_torusEnstrophyRate_of_classicalNavierStokes_smooth
    {viscosity a b : ℝ}
    {u uTime w wTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsClassicalNavierStokesOn viscosity a b u uTime p)
    (hwEquation : IsClassicalVorticityEquationOn
      viscosity a b u w wTime)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivAt (fun r => torusEnstrophy (w r))
      (torusEnstrophyRate viscosity (u t) (w t)) t := by
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have hu1 : ContDiff ℝ 1 (torusLift (u t)) :=
    (hNS.2.2.2.1 t htcc).of_le (by norm_num)
  have hw2 : ContDiff ℝ 2 (torusLift (w t)) :=
    hwEquation.2.2.2.1 t htcc
  have hw1 : ContDiff ℝ 1 (torusLift (w t)) :=
    hw2.of_le (by norm_num)
  have henergy2 : ContDiff ℝ 2
      (torusLift (vorticityEnergyField (w t))) :=
    contDiff_torusLift_vorticityEnergyField (w t) hw2
  have hsecond : ∀ i : Fin 3, Integrable
      (torusCoordinateSecondDerivative (vorticityEnergyField (w t)) i) :=
    fun i => integrable_torusCoordinateSecondDerivative_of_contDiff
      (vorticityEnergyField (w t)) i henergy2
  have henergySlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 2
        (torusCoordinateSliceLift (vorticityEnergyField (w t)) i y) :=
    fun i y => contDiff_torusCoordinateSliceLift_of_contDiff_torusLift
      (vorticityEnergyField (w t)) i y henergy2
  have hL : Integrable
      (torusScalarLaplacian (vorticityEnergyField (w t))) := by
    have hsum : Integrable (fun x : Torus3 =>
        ∑ i : Fin 3,
          torusCoordinateSecondDerivative (vorticityEnergyField (w t)) i x) :=
      MeasureTheory.integrable_finsetSum Finset.univ fun i _ => hsecond i
    exact hsum.congr (Eventually.of_forall fun x =>
      (torusScalarLaplacian_eq_sum_coordinateSecondDerivative
        (vorticityEnergyField (w t)) x).symm)
  have hS : Integrable (torusStretchingProduction (u t) (w t)) :=
    integrable_torusStretchingProduction_of_contDiff (u t) (w t) hu1
  have hP : Integrable (torusPalinstrophyDensity (w t)) :=
    integrable_torusPalinstrophyDensity_of_contDiff (w t) hw1
  have hT : Integrable
      (torusVorticityTransportProduction (u t) (w t)) :=
    integrable_torusVorticityTransportProduction_of_contDiff (u t) (w t) hw1
  apply hasDerivAt_torusEnstrophyRate_of_balance
    (hwEquation.hasDerivAt_torusEnstrophy_balance ht hS hL hP hT
      (integral_torusScalarLaplacian_eq_zero
        (vorticityEnergyField (w t)) henergySlices hsecond)
      (integral_torusVorticityTransportProduction_eq_zero_of_contDiff
        (u t) (w t) hu1 hw1
        (fun x => hNS.torusCoordinateDivergence_eq_zero htcc x))) hS hP

/-- The fully concrete quotient fraction bounds the actual scalar enstrophy rate. -/
theorem torusEnstrophyRate_le_concrete_fraction_cubic
    (B viscosity : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u w : C(Torus3, Vec3))
    (hviscosity : 0 < viscosity)
    (hfactorization :
      (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
        (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) *
          periodicVorticityWeightedVelocityVariance u w 0)
    (humean : ∀ j : Fin 3, (∫ x : Torus3, u x j) = 0)
    (huSlice : ∀ (j i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (huSq : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2))
    (huLift : ContDiff ℝ 1 (torusLift u))
    (hwCurl : ∀ x : Torus3, w x = torusCurl u x)
    (hwSlice : ∀ (j i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => w x j) i y))
    (hwSq : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative w i j x ^ 2))
    (hwLift : ContDiff ℝ 1 (torusLift w))
    (hquotient : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq w x)) 2 volume)
    (hdivCurl : torusGradientEnergy u = torusVectorSecondMoment w) :
    torusEnstrophyRate viscosity u w ≤
      (27 * torusVectorSobolevMomentConstant B / (4 * viscosity ^ 3)) *
        torusVorticitySelfTransportFraction w ^ 2 * torusEnstrophy w ^ 3 := by
  have hproduction :=
    integral_torusStretchingProduction_le_cubic_remainder_of_concrete_fraction
      B viscosity hB u w hviscosity hfactorization humean huSlice huSq
      huLift hwCurl hwSlice hwSq hwLift hquotient hdivCurl
  have hproduction' :
      (∫ x : Torus3, torusStretchingProduction u w x) ≤
        (viscosity / 2) * torusPalinstrophy w +
          ((27 * torusVectorSobolevMomentConstant B /
              (4 * viscosity ^ 3)) *
            torusVorticitySelfTransportFraction w ^ 2) *
              torusEnstrophy w ^ 3 := by
    convert hproduction using 1
    ring
  have hrate := torus_enstrophy_rate_le_cubic_of_production_remainder
    hviscosity.le (torusPalinstrophy_nonneg w) hproduction'
  simpa only [torusEnstrophyRate, mul_assoc] using hrate

/-- Streamlined rate bound: all slice, square-integrability, and quotient
`L²` premises follow from ordinary smoothness of the two periodic lifts. -/
theorem torusEnstrophyRate_le_concrete_fraction_cubic_of_smooth
    (B viscosity : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u w : C(Torus3, Vec3))
    (hviscosity : 0 < viscosity)
    (hfactorization :
      (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
        (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) *
          periodicVorticityWeightedVelocityVariance u w 0)
    (humean : ∀ j : Fin 3, (∫ x : Torus3, u x j) = 0)
    (huLift : ContDiff ℝ 1 (torusLift u))
    (hwCurl : ∀ x : Torus3, w x = torusCurl u x)
    (hwLift : ContDiff ℝ 1 (torusLift w))
    (hdivCurl : torusGradientEnergy u = torusVectorSecondMoment w) :
    torusEnstrophyRate viscosity u w ≤
      (27 * torusVectorSobolevMomentConstant B / (4 * viscosity ^ 3)) *
        torusVorticitySelfTransportFraction w ^ 2 * torusEnstrophy w ^ 3 := by
  exact torusEnstrophyRate_le_concrete_fraction_cubic
    B viscosity hB u w hviscosity hfactorization humean
    (fun j i y =>
      contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
        u i j y huLift)
    (fun i j => integrable_periodicFirstDerivative_sq_of_contDiff u i j huLift)
    huLift hwCurl
    (fun j i y =>
      contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
        w i j y hwLift)
    (fun i j => integrable_periodicFirstDerivative_sq_of_contDiff w i j hwLift)
    hwLift
    (memLp_sqrt_periodicVorticitySelfTransportQuotientSq_of_contDiff w hwLift)
    hdivCurl

/-- Concrete zero-safe positive-production correlation for the actual periodic fields. -/
def torusPositiveStretchingCorrelation
    (u w : C(Torus3, Vec3)) : ℝ :=
  positiveProductionCorrelation
    (∫ x : Torus3, torusStretchingProduction u w x)
    (torusVorticitySelfTransportQuotient w)
    (periodicVorticityWeightedVelocityVariance u w 0)

/-- The signed-correlation refinement of the actual scalar enstrophy rate.  Exact total
production cancellation is retained before the quotient interpolation and Young remainder. -/
theorem torusEnstrophyRate_le_correlated_concrete_fraction_cubic_of_smooth
    (B viscosity : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u w : C(Torus3, Vec3))
    (hviscosity : 0 < viscosity)
    (hfactorization :
      (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
        (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) *
          periodicVorticityWeightedVelocityVariance u w 0)
    (humean : ∀ j : Fin 3, (∫ x : Torus3, u x j) = 0)
    (huLift : ContDiff ℝ 1 (torusLift u))
    (hwCurl : ∀ x : Torus3, w x = torusCurl u x)
    (hwLift : ContDiff ℝ 1 (torusLift w))
    (hdivCurl : torusGradientEnergy u = torusVectorSecondMoment w) :
    torusEnstrophyRate viscosity u w ≤
      (27 * torusVectorSobolevMomentConstant B / (4 * viscosity ^ 3)) *
        (torusPositiveStretchingCorrelation u w *
          torusVorticitySelfTransportFraction w) ^ 2 *
        torusEnstrophy w ^ 3 := by
  have hproduction :=
    integral_torusStretchingProduction_le_correlated_cubic_remainder_of_concrete_fraction
      B viscosity hB u w hviscosity hfactorization humean
      (fun j i y =>
        contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
          u i j y huLift)
      (fun i j => integrable_periodicFirstDerivative_sq_of_contDiff u i j huLift)
      huLift hwCurl
      (fun j i y =>
        contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
          w i j y hwLift)
      (fun i j => integrable_periodicFirstDerivative_sq_of_contDiff w i j hwLift)
      hwLift
      (memLp_sqrt_periodicVorticitySelfTransportQuotientSq_of_contDiff w hwLift)
      hdivCurl
  have hproduction' :
      (∫ x : Torus3, torusStretchingProduction u w x) ≤
        (viscosity / 2) * torusPalinstrophy w +
          ((27 * torusVectorSobolevMomentConstant B /
              (4 * viscosity ^ 3)) *
            (torusPositiveStretchingCorrelation u w *
              torusVorticitySelfTransportFraction w) ^ 2) *
              torusEnstrophy w ^ 3 := by
    unfold torusPositiveStretchingCorrelation
    convert hproduction using 1 <;> ring
  have hrate := torus_enstrophy_rate_le_cubic_of_production_remainder
    hviscosity.le (torusPalinstrophy_nonneg w) hproduction'
  simpa only [torusEnstrophyRate, mul_assoc] using hrate

/-- Quotient-free characterization of the concrete signed critical factor.  The
self-transport quotient used to obtain the Cauchy factorization cancels from the final
ratio, including every zero-denominator branch. -/
theorem torus_correlatedCriticalFactor_eq_positiveProduction_ratio_of_smooth
    (u w : C(Torus3, Vec3))
    (hfactorization :
      (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
        torusVorticitySelfTransportQuotient w *
          periodicVorticityWeightedVelocityVariance u w 0)
    (hwLift : ContDiff ℝ 1 (torusLift w)) :
    (torusPositiveStretchingCorrelation u w *
        torusVorticitySelfTransportFraction w) ^ 2 * torusEnstrophy w =
      (max (∫ x : Torus3, torusStretchingProduction u w x) 0) ^ 4 *
          torusEnstrophy w /
        (torusPalinstrophy w *
          periodicVorticityWeightedVelocityVariance u w 0) ^ 2 := by
  have hquotient0 : 0 ≤ torusVorticitySelfTransportQuotient w :=
    integral_nonneg fun x =>
      periodicVorticitySelfTransportQuotientSq_nonneg w x
  have hquotient : torusVorticitySelfTransportQuotient w ≤
      torusPalinstrophy w :=
    integral_periodicVorticitySelfTransportQuotientSq_le_torusPalinstrophy
      w hwLift
      (fun i j => integrable_periodicFirstDerivative_sq_of_contDiff w i j hwLift)
      (memLp_sqrt_periodicVorticitySelfTransportQuotientSq_of_contDiff w hwLift)
  have hratio := correlatedCriticalDepletionFactor_eq_positiveProduction_ratio
    (production := ∫ x : Torus3, torusStretchingProduction u w x)
    (quotient := torusVorticitySelfTransportQuotient w)
    (variance := periodicVorticityWeightedVelocityVariance u w 0)
    (palinstrophy := torusPalinstrophy w)
    (enstrophy := torusEnstrophy w)
    hfactorization hquotient0 hquotient
  unfold correlatedCriticalDepletionFactor at hratio
  simpa [torusPositiveStretchingCorrelation,
    torusVorticitySelfTransportFraction, mul_pow] using hratio

/-- Time-dependent continuation estimate obtained by combining the concrete
fractional rate with the kinetic-energy-paid enstrophy budget.  The two
derivative hypotheses are precisely the outputs of the concrete momentum and
vorticity balance theorems in `KineticEnergy.lean` and `Enstrophy.lean`. -/
theorem concrete_quotient_enstrophy_bound_of_energy_balance
    {B viscosity a t M : ℝ}
    {u w : ℝ → C(Torus3, Vec3)}
    (hviscosity : 0 < viscosity) (hat : a ≤ t) (hM : 0 ≤ M)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (huCont : ContinuousOn u (Icc a t))
    (hEpos : ∀ s ∈ Icc a t, 0 < torusEnstrophy (w s))
    (hEcont : ContinuousOn (fun s => torusEnstrophy (w s)) (Icc a t))
    (hEint : IntegrableOn (fun s => torusEnstrophy (w s)) (Icc a t))
    (hEnstrophyRate : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusEnstrophy (w r))
        (torusEnstrophyRate viscosity (u s) (w s)) s)
    (hKineticBalance : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusKineticEnergy (u r))
        (-viscosity * torusPalinstrophy (u s)) s)
    (hPalinstrophyInt : IntervalIntegrable
      (fun s => torusPalinstrophy (u s)) volume a t)
    (hfactorization : ∀ s ∈ Ioo a t,
      (∫ x : Torus3, torusStretchingProduction (u s) (w s) x) ^ 2 ≤
        (∫ x : Torus3,
          periodicVorticitySelfTransportQuotientSq (w s) x) *
          periodicVorticityWeightedVelocityVariance (u s) (w s) 0)
    (humean : ∀ s ∈ Ioo a t, ∀ j : Fin 3,
      (∫ x : Torus3, u s x j) = 0)
    (huLift : ∀ s ∈ Ioo a t, ContDiff ℝ 1 (torusLift (u s)))
    (hwCurl : ∀ s ∈ Ioo a t, ∀ x : Torus3,
      w s x = torusCurl (u s) x)
    (hwLift : ∀ s ∈ Ioo a t, ContDiff ℝ 1 (torusLift (w s)))
    (hdivCurl : ∀ s ∈ Ioo a t,
      torusGradientEnergy (u s) = torusVectorSecondMoment (w s))
    (hcritical : ∀ s ∈ Ioo a t,
      torusVorticitySelfTransportFraction (w s) ^ 2 *
        torusEnstrophy (w s) ≤ M) :
    torusEnstrophy (w t) ≤ torusEnstrophy (w a) *
      Real.exp
        ((27 * torusVectorSobolevMomentConstant B /
            (4 * viscosity ^ 3)) * M *
          (torusKineticEnergy (u a) / (2 * viscosity))) := by
  let C : ℝ :=
    27 * torusVectorSobolevMomentConstant B / (4 * viscosity ^ 3)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg
      (mul_nonneg (by norm_num) (torusVectorSobolevMomentConstant_nonneg B))
      (mul_nonneg (by norm_num) (pow_nonneg hviscosity.le 3))
  have hcubic : ∀ s ∈ Ioo a t,
      torusEnstrophyRate viscosity (u s) (w s) ≤
        C * torusVorticitySelfTransportFraction (w s) ^ 2 *
          torusEnstrophy (w s) ^ 3 := by
    intro s hs
    exact torusEnstrophyRate_le_concrete_fraction_cubic_of_smooth
      B viscosity hB (u s) (w s) hviscosity
      (hfactorization s hs) (humean s hs) (huLift s hs) (hwCurl s hs)
      (hwLift s hs) (hdivCurl s hs)
  have hcurlEnergy : ∀ s ∈ Ioo a t,
      torusPalinstrophy (u s) = 2 * torusEnstrophy (w s) := by
    intro s hs
    calc
      torusPalinstrophy (u s) = torusGradientEnergy (u s) :=
        torusPalinstrophy_eq_torusGradientEnergy (u s) (huLift s hs)
      _ = torusVectorSecondMoment (w s) := hdivCurl s hs
      _ = 2 * torusEnstrophy (w s) :=
        torusVectorSecondMoment_eq_two_torusEnstrophy (w s)
  have hbudget :
      (∫ s in a..t, torusEnstrophy (w s)) ≤
        torusKineticEnergy (u a) / (2 * viscosity) :=
    torusEnstrophy_budget_of_curl_energy hviscosity hat huCont
      hKineticBalance hPalinstrophyInt hcurlEnergy
  exact quotient_cubic_rate_bounded_of_energy_budget
    hat hC hM hEpos hEcont hEnstrophyRate hcubic hcritical hEint hbudget

/-- Signed, quotient-free continuation estimate.  The critical hypothesis is stated
directly through positive total stretching, palinstrophy, and weighted velocity variance;
the auxiliary self-transport quotient cancels from it exactly. -/
theorem concrete_signed_enstrophy_bound_of_energy_balance
    {B viscosity a t M : ℝ}
    {u w : ℝ → C(Torus3, Vec3)}
    (hviscosity : 0 < viscosity) (hat : a ≤ t) (hM : 0 ≤ M)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (huCont : ContinuousOn u (Icc a t))
    (hEpos : ∀ s ∈ Icc a t, 0 < torusEnstrophy (w s))
    (hEcont : ContinuousOn (fun s => torusEnstrophy (w s)) (Icc a t))
    (hEint : IntegrableOn (fun s => torusEnstrophy (w s)) (Icc a t))
    (hEnstrophyRate : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusEnstrophy (w r))
        (torusEnstrophyRate viscosity (u s) (w s)) s)
    (hKineticBalance : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusKineticEnergy (u r))
        (-viscosity * torusPalinstrophy (u s)) s)
    (hPalinstrophyInt : IntervalIntegrable
      (fun s => torusPalinstrophy (u s)) volume a t)
    (hfactorization : ∀ s ∈ Ioo a t,
      (∫ x : Torus3, torusStretchingProduction (u s) (w s) x) ^ 2 ≤
        torusVorticitySelfTransportQuotient (w s) *
          periodicVorticityWeightedVelocityVariance (u s) (w s) 0)
    (humean : ∀ s ∈ Ioo a t, ∀ j : Fin 3,
      (∫ x : Torus3, u s x j) = 0)
    (huLift : ∀ s ∈ Ioo a t, ContDiff ℝ 1 (torusLift (u s)))
    (hwCurl : ∀ s ∈ Ioo a t, ∀ x : Torus3,
      w s x = torusCurl (u s) x)
    (hwLift : ∀ s ∈ Ioo a t, ContDiff ℝ 1 (torusLift (w s)))
    (hdivCurl : ∀ s ∈ Ioo a t,
      torusGradientEnergy (u s) = torusVectorSecondMoment (w s))
    (hcritical : ∀ s ∈ Ioo a t,
      (max (∫ x : Torus3,
          torusStretchingProduction (u s) (w s) x) 0) ^ 4 *
            torusEnstrophy (w s) /
          (torusPalinstrophy (w s) *
            periodicVorticityWeightedVelocityVariance (u s) (w s) 0) ^ 2 ≤ M) :
    torusEnstrophy (w t) ≤ torusEnstrophy (w a) *
      Real.exp
        ((27 * torusVectorSobolevMomentConstant B /
            (4 * viscosity ^ 3)) * M *
          (torusKineticEnergy (u a) / (2 * viscosity))) := by
  let C : ℝ :=
    27 * torusVectorSobolevMomentConstant B / (4 * viscosity ^ 3)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg
      (mul_nonneg (by norm_num) (torusVectorSobolevMomentConstant_nonneg B))
      (mul_nonneg (by norm_num) (pow_nonneg hviscosity.le 3))
  have hcubic : ∀ s ∈ Ioo a t,
      torusEnstrophyRate viscosity (u s) (w s) ≤
        C * (torusPositiveStretchingCorrelation (u s) (w s) *
          torusVorticitySelfTransportFraction (w s)) ^ 2 *
          torusEnstrophy (w s) ^ 3 := by
    intro s hs
    exact torusEnstrophyRate_le_correlated_concrete_fraction_cubic_of_smooth
      B viscosity hB (u s) (w s) hviscosity
      (hfactorization s hs) (humean s hs) (huLift s hs) (hwCurl s hs)
      (hwLift s hs) (hdivCurl s hs)
  have hcritical' : ∀ s ∈ Ioo a t,
      (torusPositiveStretchingCorrelation (u s) (w s) *
        torusVorticitySelfTransportFraction (w s)) ^ 2 *
          torusEnstrophy (w s) ≤ M := by
    intro s hs
    rw [torus_correlatedCriticalFactor_eq_positiveProduction_ratio_of_smooth
      (u s) (w s) (hfactorization s hs) (hwLift s hs)]
    exact hcritical s hs
  have hcurlEnergy : ∀ s ∈ Ioo a t,
      torusPalinstrophy (u s) = 2 * torusEnstrophy (w s) := by
    intro s hs
    calc
      torusPalinstrophy (u s) = torusGradientEnergy (u s) :=
        torusPalinstrophy_eq_torusGradientEnergy (u s) (huLift s hs)
      _ = torusVectorSecondMoment (w s) := hdivCurl s hs
      _ = 2 * torusEnstrophy (w s) :=
        torusVectorSecondMoment_eq_two_torusEnstrophy (w s)
  have hbudget :
      (∫ s in a..t, torusEnstrophy (w s)) ≤
        torusKineticEnergy (u a) / (2 * viscosity) :=
    torusEnstrophy_budget_of_curl_energy hviscosity hat huCont
      hKineticBalance hPalinstrophyInt hcurlEnergy
  exact correlated_quotient_cubic_rate_bounded_of_energy_budget
    hat hC hM hEpos hEcont hEnstrophyRate hcubic hcritical' hEint hbudget

/-- Direct classical-solution form of the concrete continuation estimate.
The time derivatives, energy budget, temporal integrability, and all
first-order spatial side conditions are derived inside the proof from the
actual Navier--Stokes and vorticity predicates. -/
theorem concrete_quotient_enstrophy_bound_of_classicalNavierStokes
    {B viscosity a b t M : ℝ}
    {u uTime w wTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsClassicalNavierStokesOn viscosity a b u uTime p)
    (hwEquation : IsClassicalVorticityEquationOn
      viscosity a b u w wTime)
    (hwOfU : IsVorticityOfOn a b u w)
    (hat : a ≤ t) (htb : t ≤ b) (hM : 0 ≤ M)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (hEpos : ∀ s ∈ Icc a t, 0 < torusEnstrophy (w s))
    (humean : ∀ s ∈ Ioo a t, ∀ j : Fin 3,
      (∫ x : Torus3, u s x j) = 0)
    (hcritical : ∀ s ∈ Ioo a t,
      torusVorticitySelfTransportFraction (w s) ^ 2 *
        torusEnstrophy (w s) ≤ M) :
    torusEnstrophy (w t) ≤ torusEnstrophy (w a) *
      Real.exp
        ((27 * torusVectorSobolevMomentConstant B /
            (4 * viscosity ^ 3)) * M *
          (torusKineticEnergy (u a) / (2 * viscosity))) := by
  have hviscosity : 0 < viscosity := hNS.1
  have hsub : Icc a t ⊆ Icc a b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans htb⟩
  have huCont : ContinuousOn u (Icc a t) := hNS.2.1.mono hsub
  have hwCont : ContinuousOn w (Icc a t) := hwEquation.2.1.mono hsub
  have hEfunctional : Continuous
      (torusEnstrophy : C(Torus3, Vec3) → ℝ) := by
    change Continuous (torusKineticEnergy : C(Torus3, Vec3) → ℝ)
    exact continuous_torusKineticEnergy
  have hEcont : ContinuousOn (fun s => torusEnstrophy (w s)) (Icc a t) :=
    hEfunctional.comp_continuousOn hwCont
  have hEint : IntegrableOn (fun s => torusEnstrophy (w s)) (Icc a t) :=
    hEcont.integrableOn_Icc
  have hIco : ∀ s ∈ Ioo a t, s ∈ Ico a b := by
    intro s hs
    exact ⟨hs.1.le, hs.2.trans_le htb⟩
  have huLift2 : ∀ s ∈ Ioo a t, ContDiff ℝ 2 (torusLift (u s)) := by
    intro s hs
    exact hNS.2.2.2.1 s ⟨hs.1.le, (hs.2.le.trans htb)⟩
  have huLift : ∀ s ∈ Ioo a t, ContDiff ℝ 1 (torusLift (u s)) :=
    fun s hs => (huLift2 s hs).of_le (by norm_num)
  have hwLift : ∀ s ∈ Ioo a t, ContDiff ℝ 1 (torusLift (w s)) := by
    intro s hs
    exact (hwEquation.2.2.2.1 s ⟨hs.1.le, (hs.2.le.trans htb)⟩).of_le
      (by norm_num)
  have hwCurl : ∀ s ∈ Ioo a t, ∀ x : Torus3,
      w s x = torusCurl (u s) x := by
    intro s hs x
    exact hwOfU s ⟨hs.1.le, hs.2.le.trans htb⟩ x
  have hfactorization : ∀ s ∈ Ioo a t,
      (∫ x : Torus3, torusStretchingProduction (u s) (w s) x) ^ 2 ≤
        (∫ x : Torus3,
          periodicVorticitySelfTransportQuotientSq (w s) x) *
          periodicVorticityWeightedVelocityVariance (u s) (w s) 0 := by
    intro s hs
    have hdiv : ∀ x : Torus3,
        torusCoordinateDivergence (w s) x = 0 := fun x =>
      torusCoordinateDivergence_eq_zero_of_eq_torusCurl
        (u s) (w s) (huLift2 s hs) (hwLift s hs) (hwCurl s hs) x
    simpa only [torusVorticitySelfTransportQuotient] using
      sq_integral_torusStretchingProduction_le_selfTransportQuotient_weightedVariance_of_contDiff
        (u s) (w s) 0 (huLift s hs) (hwLift s hs) hdiv
  have hdivCurl : ∀ s ∈ Ioo a t,
      torusGradientEnergy (u s) = torusVectorSecondMoment (w s) := by
    intro s hs
    exact torusGradientEnergy_eq_torusVectorSecondMoment_of_curl_of_contDiff
      (u s) (w s) (huLift2 s hs) (hwCurl s hs)
      (fun x => hNS.torusCoordinateDivergence_eq_zero
        ⟨hs.1.le, hs.2.le.trans htb⟩ x)
  have hEnstrophyRate : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusEnstrophy (w r))
        (torusEnstrophyRate viscosity (u s) (w s)) s := by
    intro s hs
    exact hasDerivAt_torusEnstrophyRate_of_classicalNavierStokes_smooth
      hNS hwEquation (hIco s hs)
  have hKineticBalance : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusKineticEnergy (u r))
        (-viscosity * torusPalinstrophy (u s)) s := by
    intro s hs
    exact hasDerivAt_torusKineticEnergy_balance_of_classicalNavierStokes_smooth
      hNS (hIco s hs)
  have hcurlEnergy : ∀ s ∈ Ioo a t,
      torusPalinstrophy (u s) = 2 * torusEnstrophy (w s) := by
    intro s hs
    calc
      torusPalinstrophy (u s) = torusGradientEnergy (u s) :=
        torusPalinstrophy_eq_torusGradientEnergy (u s) (huLift s hs)
      _ = torusVectorSecondMoment (w s) := hdivCurl s hs
      _ = 2 * torusEnstrophy (w s) :=
        torusVectorSecondMoment_eq_two_torusEnstrophy (w s)
  have hPalinstrophyInt : IntervalIntegrable
      (fun s => torusPalinstrophy (u s)) volume a t := by
    have hEcontU : ContinuousOn (fun s => torusEnstrophy (w s)) [[a, t]] := by
      simpa [uIcc_of_le hat] using hEcont
    have h2E : IntervalIntegrable
        (fun s => 2 * torusEnstrophy (w s)) volume a t :=
      hEcontU.intervalIntegrable.const_mul 2
    apply h2E.congr_uIoo
    intro s hs
    rw [uIoo_of_le hat] at hs
    exact (hcurlEnergy s hs).symm
  exact concrete_quotient_enstrophy_bound_of_energy_balance
    hviscosity hat hM hB huCont hEpos hEcont hEint hEnstrophyRate
      hKineticBalance hPalinstrophyInt hfactorization humean huLift hwCurl
      hwLift hdivCurl hcritical

/-- Direct classical-solution form of the signed quotient-free continuation theorem.
The only new dynamical premise is a uniform bound on positive stretching relative to
palinstrophy and weighted velocity variance; exact signed cancellation is preserved. -/
theorem concrete_signed_enstrophy_bound_of_classicalNavierStokes
    {B viscosity a b t M : ℝ}
    {u uTime w wTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsClassicalNavierStokesOn viscosity a b u uTime p)
    (hwEquation : IsClassicalVorticityEquationOn
      viscosity a b u w wTime)
    (hwOfU : IsVorticityOfOn a b u w)
    (hat : a ≤ t) (htb : t ≤ b) (hM : 0 ≤ M)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (hEpos : ∀ s ∈ Icc a t, 0 < torusEnstrophy (w s))
    (humean : ∀ s ∈ Ioo a t, ∀ j : Fin 3,
      (∫ x : Torus3, u s x j) = 0)
    (hcritical : ∀ s ∈ Ioo a t,
      (max (∫ x : Torus3,
          torusStretchingProduction (u s) (w s) x) 0) ^ 4 *
            torusEnstrophy (w s) /
          (torusPalinstrophy (w s) *
            periodicVorticityWeightedVelocityVariance (u s) (w s) 0) ^ 2 ≤ M) :
    torusEnstrophy (w t) ≤ torusEnstrophy (w a) *
      Real.exp
        ((27 * torusVectorSobolevMomentConstant B /
            (4 * viscosity ^ 3)) * M *
          (torusKineticEnergy (u a) / (2 * viscosity))) := by
  have hviscosity : 0 < viscosity := hNS.1
  have hsub : Icc a t ⊆ Icc a b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans htb⟩
  have huCont : ContinuousOn u (Icc a t) := hNS.2.1.mono hsub
  have hwCont : ContinuousOn w (Icc a t) := hwEquation.2.1.mono hsub
  have hEfunctional : Continuous
      (torusEnstrophy : C(Torus3, Vec3) → ℝ) := by
    change Continuous (torusKineticEnergy : C(Torus3, Vec3) → ℝ)
    exact continuous_torusKineticEnergy
  have hEcont : ContinuousOn (fun s => torusEnstrophy (w s)) (Icc a t) :=
    hEfunctional.comp_continuousOn hwCont
  have hEint : IntegrableOn (fun s => torusEnstrophy (w s)) (Icc a t) :=
    hEcont.integrableOn_Icc
  have hIco : ∀ s ∈ Ioo a t, s ∈ Ico a b := by
    intro s hs
    exact ⟨hs.1.le, hs.2.trans_le htb⟩
  have huLift2 : ∀ s ∈ Ioo a t, ContDiff ℝ 2 (torusLift (u s)) := by
    intro s hs
    exact hNS.2.2.2.1 s ⟨hs.1.le, (hs.2.le.trans htb)⟩
  have huLift : ∀ s ∈ Ioo a t, ContDiff ℝ 1 (torusLift (u s)) :=
    fun s hs => (huLift2 s hs).of_le (by norm_num)
  have hwLift : ∀ s ∈ Ioo a t, ContDiff ℝ 1 (torusLift (w s)) := by
    intro s hs
    exact (hwEquation.2.2.2.1 s ⟨hs.1.le, (hs.2.le.trans htb)⟩).of_le
      (by norm_num)
  have hwCurl : ∀ s ∈ Ioo a t, ∀ x : Torus3,
      w s x = torusCurl (u s) x := by
    intro s hs x
    exact hwOfU s ⟨hs.1.le, hs.2.le.trans htb⟩ x
  have hfactorization : ∀ s ∈ Ioo a t,
      (∫ x : Torus3, torusStretchingProduction (u s) (w s) x) ^ 2 ≤
        torusVorticitySelfTransportQuotient (w s) *
          periodicVorticityWeightedVelocityVariance (u s) (w s) 0 := by
    intro s hs
    have hdiv : ∀ x : Torus3,
        torusCoordinateDivergence (w s) x = 0 := fun x =>
      torusCoordinateDivergence_eq_zero_of_eq_torusCurl
        (u s) (w s) (huLift2 s hs) (hwLift s hs) (hwCurl s hs) x
    exact
      sq_integral_torusStretchingProduction_le_selfTransportQuotient_weightedVariance_of_contDiff
        (u s) (w s) 0 (huLift s hs) (hwLift s hs) hdiv
  have hdivCurl : ∀ s ∈ Ioo a t,
      torusGradientEnergy (u s) = torusVectorSecondMoment (w s) := by
    intro s hs
    exact torusGradientEnergy_eq_torusVectorSecondMoment_of_curl_of_contDiff
      (u s) (w s) (huLift2 s hs) (hwCurl s hs)
      (fun x => hNS.torusCoordinateDivergence_eq_zero
        ⟨hs.1.le, hs.2.le.trans htb⟩ x)
  have hEnstrophyRate : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusEnstrophy (w r))
        (torusEnstrophyRate viscosity (u s) (w s)) s := by
    intro s hs
    exact hasDerivAt_torusEnstrophyRate_of_classicalNavierStokes_smooth
      hNS hwEquation (hIco s hs)
  have hKineticBalance : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusKineticEnergy (u r))
        (-viscosity * torusPalinstrophy (u s)) s := by
    intro s hs
    exact hasDerivAt_torusKineticEnergy_balance_of_classicalNavierStokes_smooth
      hNS (hIco s hs)
  have hcurlEnergy : ∀ s ∈ Ioo a t,
      torusPalinstrophy (u s) = 2 * torusEnstrophy (w s) := by
    intro s hs
    calc
      torusPalinstrophy (u s) = torusGradientEnergy (u s) :=
        torusPalinstrophy_eq_torusGradientEnergy (u s) (huLift s hs)
      _ = torusVectorSecondMoment (w s) := hdivCurl s hs
      _ = 2 * torusEnstrophy (w s) :=
        torusVectorSecondMoment_eq_two_torusEnstrophy (w s)
  have hPalinstrophyInt : IntervalIntegrable
      (fun s => torusPalinstrophy (u s)) volume a t := by
    have hEcontU : ContinuousOn (fun s => torusEnstrophy (w s)) [[a, t]] := by
      simpa [uIcc_of_le hat] using hEcont
    have h2E : IntervalIntegrable
        (fun s => 2 * torusEnstrophy (w s)) volume a t :=
      hEcontU.intervalIntegrable.const_mul 2
    apply h2E.congr_uIoo
    intro s hs
    rw [uIoo_of_le hat] at hs
    exact (hcurlEnergy s hs).symm
  exact concrete_signed_enstrophy_bound_of_energy_balance
    hviscosity hat hM hB huCont hEpos hEcont hEint hEnstrophyRate
      hKineticBalance hPalinstrophyInt hfactorization humean huLift hwCurl
      hwLift hdivCurl hcritical
