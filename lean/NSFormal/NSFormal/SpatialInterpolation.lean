import NSFormal.Enstrophy
import NSFormal.NewProofAlgebra
import NSFormal.DivCurl
import NSFormal.PeriodicSobolevEuclidean
import NSFormal.DynamicCriterion

/-!
# Root-free spatial interpolation ledger on the periodic three-torus

This file separates the elementary measure-theoretic part of the weighted-variance
interpolation from the two genuinely spatial Sobolev estimates.  All Hölder steps are
written as ordinary `L²` Cauchy inequalities and combined at integer powers.
-/

open Filter Function MeasureTheory Set

noncomputable section

/-- Mixed norm moment `∫ |u|ᵃ |ω|ᵇ` on the concrete Haar three-torus. -/
def torusMixedVelocityVorticityMoment
    (u w : C(Torus3, Vec3)) (velocityPower vorticityPower : ℕ) : ℝ :=
  ∫ x : Torus3, ‖u x‖ ^ velocityPower * ‖w x‖ ^ vorticityPower

theorem torusMixedVelocityVorticityMoment_nonneg
    (u w : C(Torus3, Vec3)) (velocityPower vorticityPower : ℕ) :
    0 ≤ torusMixedVelocityVorticityMoment u w velocityPower vorticityPower :=
  integral_nonneg fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (pow_nonneg (norm_nonneg _) _)

/-- Every mixed moment of continuous torus fields belongs to every finite or infinite `Lᵖ`. -/
theorem torusMixedVelocityVorticityMoment_memLp
    (u w : C(Torus3, Vec3)) (velocityPower vorticityPower : ℕ)
    (p : ENNReal) :
    MemLp (fun x : Torus3 =>
      ‖u x‖ ^ velocityPower * ‖w x‖ ^ vorticityPower) p := by
  apply MemLp.of_bound
    ((u.continuous.norm.pow velocityPower).mul
      (w.continuous.norm.pow vorticityPower)).aestronglyMeasurable
    (‖u‖ ^ velocityPower * ‖w‖ ^ vorticityPower)
  exact Eventually.of_forall fun x => by
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
      (pow_nonneg (norm_nonneg _) _))]
    exact mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm u x) _)
      (pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm w x) _)
      (pow_nonneg (norm_nonneg _) _)
      (pow_nonneg (norm_nonneg u) _)

/-- First Cauchy link: `(∫ |u|²|ω|²)² ≤ (∫ |u|⁴|ω|²)(∫ |ω|²)`. -/
theorem torus_weightedMoment_sq_le_mixedFour_mul_vorticitySecond
    (u w : C(Torus3, Vec3)) :
    torusMixedVelocityVorticityMoment u w 2 2 ^ 2 ≤
      torusMixedVelocityVorticityMoment u w 4 2 *
        torusMixedVelocityVorticityMoment u w 0 2 := by
  have h := sq_integral_mul_le_integral_sq_mul_integral_sq
    (μ := (volume : Measure Torus3))
    (f := fun x => ‖u x‖ ^ 2 * ‖w x‖)
    (g := fun x => ‖w x‖)
    (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (norm_nonneg _))
    (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa using torusMixedVelocityVorticityMoment_memLp u w 2 1 2)
    (by simpa using torusMixedVelocityVorticityMoment_memLp u w 0 1 2)
  unfold torusMixedVelocityVorticityMoment
  ring_nf at h ⊢
  exact h

/-- Second Cauchy link: `(∫ |u|⁴|ω|²)² ≤ (∫ |u|⁶)(∫ |u|²|ω|⁴)`. -/
theorem torus_mixedFour_sq_le_velocitySixth_mul_mixedVorticityFour
    (u w : C(Torus3, Vec3)) :
    torusMixedVelocityVorticityMoment u w 4 2 ^ 2 ≤
      torusMixedVelocityVorticityMoment u w 6 0 *
        torusMixedVelocityVorticityMoment u w 2 4 := by
  have h := sq_integral_mul_le_integral_sq_mul_integral_sq
    (μ := (volume : Measure Torus3))
    (f := fun x => ‖u x‖ ^ 3)
    (g := fun x => ‖u x‖ * ‖w x‖ ^ 2)
    (Eventually.of_forall fun _ => pow_nonneg (norm_nonneg _) _)
    (Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    (by simpa using torusMixedVelocityVorticityMoment_memLp u w 3 0 2)
    (by simpa using torusMixedVelocityVorticityMoment_memLp u w 1 2 2)
  unfold torusMixedVelocityVorticityMoment
  ring_nf at h ⊢
  exact h

/-- Third Cauchy link: `(∫ |u|²|ω|⁴)² ≤ (∫ |u|⁴|ω|²)(∫ |ω|⁶)`. -/
theorem torus_mixedVorticityFour_sq_le_mixedFour_mul_vorticitySixth
    (u w : C(Torus3, Vec3)) :
    torusMixedVelocityVorticityMoment u w 2 4 ^ 2 ≤
      torusMixedVelocityVorticityMoment u w 4 2 *
        torusMixedVelocityVorticityMoment u w 0 6 := by
  have h := sq_integral_mul_le_integral_sq_mul_integral_sq
    (μ := (volume : Measure Torus3))
    (f := fun x => ‖u x‖ ^ 2 * ‖w x‖)
    (g := fun x => ‖w x‖ ^ 3)
    (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (norm_nonneg _))
    (Eventually.of_forall fun _ => pow_nonneg (norm_nonneg _) _)
    (by simpa using torusMixedVelocityVorticityMoment_memLp u w 2 1 2)
    (by simpa using torusMixedVelocityVorticityMoment_memLp u w 0 3 2)
  unfold torusMixedVelocityVorticityMoment
  ring_nf at h ⊢
  exact h

/-- At the zero Galilean frame, the existing vorticity-weighted velocity variance is exactly
the `(2,2)` mixed norm moment. -/
theorem periodicVorticityWeightedVelocityVariance_zero_eq_mixedMoment
    (u w : C(Torus3, Vec3)) :
    periodicVorticityWeightedVelocityVariance u w 0 =
      torusMixedVelocityVorticityMoment u w 2 2 := by
  have hcomponents : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight w x * (u x j - (0 : Vec3) j) ^ 2) := by
    intro j
    have hcontinuous : Continuous (fun x : Torus3 =>
        periodicVorticityEnergyWeight w x * (u x j - (0 : Vec3) j) ^ 2) := by
      unfold periodicVorticityEnergyWeight
      fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hcontinuous.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  rw [periodicVorticityWeightedVelocityVariance_eq_integral_norm_sq
    u w 0 hcomponents]
  unfold torusMixedVelocityVorticityMoment
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change periodicVorticityEnergyWeight w x *
        ‖centeredVelocity u 0 x‖ ^ 2 = ‖u x‖ ^ 2 * ‖w x‖ ^ 2
    unfold periodicVorticityEnergyWeight
    rw [← EuclideanSpace.real_norm_sq_eq (w x)]
    simp only [centeredVelocity_apply, sub_zero]
    ring

/-- The concrete three Cauchy links give the sixth-power weighted-variance bound on the
actual torus moments. -/
theorem periodicVorticityWeightedVelocityVariance_zero_sixth_le
    (u w : C(Torus3, Vec3)) :
    periodicVorticityWeightedVelocityVariance u w 0 ^ 6 ≤
      torusMixedVelocityVorticityMoment u w 6 0 ^ 2 *
        torusMixedVelocityVorticityMoment u w 0 6 *
          torusMixedVelocityVorticityMoment u w 0 2 ^ 3 := by
  rw [periodicVorticityWeightedVelocityVariance_zero_eq_mixedMoment]
  exact weighted_variance_sixth_moment_ledger
    (torusMixedVelocityVorticityMoment_nonneg u w 4 2)
    (torusMixedVelocityVorticityMoment_nonneg u w 2 4)
    (torusMixedVelocityVorticityMoment_nonneg u w 6 0)
    (torusMixedVelocityVorticityMoment_nonneg u w 0 2)
    (torusMixedVelocityVorticityMoment_nonneg u w 0 6)
    (torus_weightedMoment_sq_le_mixedFour_mul_vorticitySecond u w)
    (torus_mixedFour_sq_le_velocitySixth_mul_mixedVorticityFour u w)
    (torus_mixedVorticityFour_sq_le_mixedFour_mul_vorticitySixth u w)

/-- Global palinstrophy in the same concrete coordinate convention as the enstrophy balance. -/
def torusPalinstrophy (w : C(Torus3, Vec3)) : ℝ :=
  ∫ x : Torus3, torusPalinstrophyDensity w x

theorem torusPalinstrophy_nonneg (w : C(Torus3, Vec3)) :
    0 ≤ torusPalinstrophy w :=
  integral_nonneg fun x => torusLiftGradientSq_nonneg w (torus3Representative x)

/-- Palinstrophy is exactly the integrated coordinate-gradient energy.  The equality is no
longer an interface assumption: it follows from the pointwise compatibility between the lifted
coordinate-line derivative and the descended periodic derivative. -/
theorem torusPalinstrophy_eq_torusGradientEnergy
    (w : C(Torus3, Vec3))
    (hw : ContDiff ℝ 1 (torusLift w)) :
    torusPalinstrophy w = torusGradientEnergy w := by
  unfold torusPalinstrophy torusGradientEnergy
  apply integral_congr_ae
  exact Eventually.of_forall fun x =>
    torusPalinstrophyDensity_eq_periodicGradientFrobeniusSq w x hw

/-- The exact self-transport quotient occupies at most all of palinstrophy.  This gives the
canonical unconditional quotient fraction `1`; any fraction below `1` is genuine geometric
depletion rather than a normalization artifact. -/
theorem integral_periodicVorticitySelfTransportQuotientSq_le_torusPalinstrophy
    (w : C(Torus3, Vec3))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative w i j x ^ 2))
    (hquotient : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq w x)) 2 volume) :
    (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) ≤
      torusPalinstrophy w := by
  have hquotientInt : Integrable (fun x : Torus3 =>
      periodicVorticitySelfTransportQuotientSq w x) := by
    simpa only [Real.sq_sqrt
      (periodicVorticitySelfTransportQuotientSq_nonneg w _)] using
        hquotient.integrable_sq
  have hgradientInt : Integrable (fun x : Torus3 =>
      periodicGradientFrobeniusSq w x) := by
    unfold periodicGradientFrobeniusSq
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun j _ => hderiv i j
  rw [torusPalinstrophy_eq_torusGradientEnergy w hw]
  unfold torusGradientEnergy
  exact integral_mono hquotientInt hgradientInt fun x =>
    periodicVorticitySelfTransportQuotientSq_le_gradientFrobeniusSq w x

/-- Integrated self-transport quotient in the concrete periodic PDE convention. -/
def torusVorticitySelfTransportQuotient (w : C(Torus3, Vec3)) : ℝ :=
  ∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x

/-- Zero-safe fraction of concrete palinstrophy carried by differentiation along vorticity. -/
def torusVorticitySelfTransportFraction (w : C(Torus3, Vec3)) : ℝ :=
  quotientPalinstrophyFraction
    (torusVorticitySelfTransportQuotient w) (torusPalinstrophy w)

theorem torusVorticitySelfTransportFraction_nonneg (w : C(Torus3, Vec3)) :
    0 ≤ torusVorticitySelfTransportFraction w := by
  exact quotientPalinstrophyFraction_nonneg _ _
    (integral_nonneg fun x =>
      periodicVorticitySelfTransportQuotientSq_nonneg w x)
    (torusPalinstrophy_nonneg w)

theorem torusVorticitySelfTransportFraction_le_one
    (w : C(Torus3, Vec3))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative w i j x ^ 2))
    (hquotient : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq w x)) 2 volume) :
    torusVorticitySelfTransportFraction w ≤ 1 := by
  apply quotientPalinstrophyFraction_le_one
    (torusVorticitySelfTransportQuotient w) (torusPalinstrophy w)
    (torusPalinstrophy_nonneg w)
  exact integral_periodicVorticitySelfTransportQuotientSq_le_torusPalinstrophy
    w hw hderiv hquotient

/-- The concrete fraction is not merely bounded: multiplied by palinstrophy it exactly
reconstructs the integrated quotient, including when palinstrophy vanishes. -/
theorem torusVorticitySelfTransportFraction_mul_palinstrophy
    (w : C(Torus3, Vec3))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative w i j x ^ 2))
    (hquotient : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq w x)) 2 volume) :
    torusVorticitySelfTransportFraction w * torusPalinstrophy w =
      torusVorticitySelfTransportQuotient w := by
  apply quotientPalinstrophyFraction_mul_eq_quotient
  · exact integral_nonneg fun x =>
      periodicVorticitySelfTransportQuotientSq_nonneg w x
  · exact integral_periodicVorticitySelfTransportQuotientSq_le_torusPalinstrophy
      w hw hderiv hquotient

/-- Exact concrete rigidity identity behind the signed stretching factorization.
The Cauchy defect is the quotient mass times the squared residual from the
positive-production nonlinear eigen-relation. -/
theorem torus_stretchingCauchyDefect_eq_scaledResidual
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hquotientInt : Integrable
      (periodicVorticitySelfTransportQuotientSq w))
    (hvarianceInt : Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight w x *
        ‖centeredVelocity u frame x‖ ^ 2))
    (hselfInt : Integrable
      (periodicVorticitySelfTransportDensity (centeredVelocity u frame) w))
    (hcomponents : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight w x * (u x j - frame j) ^ 2))
    (hparts :
      (∫ x : Torus3, torusStretchingProduction u w x) =
        -∫ x : Torus3,
          periodicVorticitySelfTransportDensity (centeredVelocity u frame) w x)
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
  let f : Torus3 → Vec3 :=
    periodicNormalizedVorticitySelfTransportVector w
  let g : Torus3 → Vec3 :=
    periodicVorticityWeightedCenteredVelocityVector u w frame
  let Q : ℝ := torusVorticitySelfTransportQuotient w
  let N : ℝ := ∫ x : Torus3, torusStretchingProduction u w x
  have hfSq : Integrable (fun x : Torus3 => ‖f x‖ ^ 2) :=
    hquotientInt.congr (Eventually.of_forall fun x =>
      (periodicNormalizedVorticitySelfTransportVector_norm_sq w x).symm)
  have hgSq : Integrable (fun x : Torus3 => ‖g x‖ ^ 2) :=
    hvarianceInt.congr (Eventually.of_forall fun x =>
      (periodicVorticityWeightedCenteredVelocityVector_norm_sq
        u w frame x).symm)
  have hfg : Integrable (fun x : Torus3 => inner ℝ (f x) (g x)) :=
    hselfInt.congr (Eventually.of_forall fun x =>
      (inner_periodicNormalizedSelfTransport_weightedCenteredVelocity
        u w frame x).symm)
  have hFIntegral : (∫ x : Torus3, ‖f x‖ ^ 2) = Q := by
    unfold f Q torusVorticitySelfTransportQuotient
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      periodicNormalizedVorticitySelfTransportVector_norm_sq w x
  have hGIntegral : (∫ x : Torus3, ‖g x‖ ^ 2) =
      periodicVorticityWeightedVelocityVariance u w frame := by
    calc
      (∫ x : Torus3, ‖g x‖ ^ 2) =
          ∫ x : Torus3, periodicVorticityEnergyWeight w x *
            ‖centeredVelocity u frame x‖ ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          periodicVorticityWeightedCenteredVelocityVector_norm_sq
            u w frame x
      _ = periodicVorticityWeightedVelocityVariance u w frame :=
        (periodicVorticityWeightedVelocityVariance_eq_integral_norm_sq
          u w frame hcomponents).symm
  have hInnerIntegral : (∫ x : Torus3, inner ℝ (f x) (g x)) = -N := by
    calc
      (∫ x : Torus3, inner ℝ (f x) (g x)) =
          ∫ x : Torus3,
            periodicVorticitySelfTransportDensity
              (centeredVelocity u frame) w x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          inner_periodicNormalizedSelfTransport_weightedCenteredVelocity
            u w frame x
      _ = -N := by dsimp [N]; linarith
  have hrigidity := integral_cauchy_defect_eq_scaled_projection_residual
    f g hfSq hgSq hfg (by simpa [hFIntegral, Q] using hquotientNe)
  rw [hFIntegral, hGIntegral, hInnerIntegral] at hrigidity
  change Q * periodicVorticityWeightedVelocityVariance u w frame - N ^ 2 =
    Q * ∫ x : Torus3, ‖g x + (N / Q) • f x‖ ^ 2
  calc
    Q * periodicVorticityWeightedVelocityVariance u w frame - N ^ 2 =
        Q * periodicVorticityWeightedVelocityVariance u w frame - (-N) ^ 2 := by
      ring
    _ = Q * ∫ x : Torus3, ‖g x - (-N / Q) • f x‖ ^ 2 :=
      hrigidity.symm
    _ = Q * ∫ x : Torus3, ‖g x + (N / Q) • f x‖ ^ 2 := by
      apply congrArg (fun z : ℝ => Q * z)
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        apply congrArg (fun z : Vec3 => ‖z‖ ^ 2)
        module

/-- The Euclidean-transfer Sobolev theorem supplies the velocity sixth-moment premise used
by the root-free interpolation ledger. -/
theorem torus_velocitySixthMoment_le_gradientEnergy_cubic
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u w : C(Torus3, Vec3))
    (hmean : ∀ j : Fin 3, (∫ x : Torus3, u x j) = 0)
    (hsmooth : ∀ (j i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2))
    (hu : ContDiff ℝ 1 (torusLift u)) :
    torusMixedVelocityVorticityMoment u w 6 0 ≤
      torusVectorSobolevMomentConstant B * torusGradientEnergy u ^ 3 := by
  simpa [torusMixedVelocityVorticityMoment] using
    integral_torus_vector_norm_pow_six_le_gradientEnergy_cubic
      B hB u hmean hsmooth hderiv hu

/-- The same proved Sobolev estimate applied to vorticity gives the second sixth-moment
premise, now in the enstrophy file's palinstrophy convention. -/
theorem torus_vorticitySixthMoment_le_palinstrophy_cubic
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u w : C(Torus3, Vec3))
    (hmean : ∀ j : Fin 3, (∫ x : Torus3, w x j) = 0)
    (hsmooth : ∀ (j i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => w x j) i y))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative w i j x ^ 2))
    (hw : ContDiff ℝ 1 (torusLift w)) :
    torusMixedVelocityVorticityMoment u w 0 6 ≤
      torusVectorSobolevMomentConstant B * torusPalinstrophy w ^ 3 := by
  rw [torusPalinstrophy_eq_torusGradientEnergy w hw]
  simpa [torusMixedVelocityVorticityMoment] using
    integral_torus_vector_norm_pow_six_le_gradientEnergy_cubic
      B hB w hmean hsmooth hderiv hw

/-- The second vorticity moment is exactly twice the half-enstrophy used by the PDE balance. -/
theorem torus_vorticitySecondMoment_eq_two_enstrophy (w : C(Torus3, Vec3)) :
    torusMixedVelocityVorticityMoment 0 w 0 2 = 2 * torusEnstrophy w := by
  unfold torusMixedVelocityVorticityMoment torusEnstrophy
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [vorticityEnergyField_apply, vorticityEnergy]
    ring

/-- The `(0,2)` mixed moment is the vector second moment used by the div--curl file;
the dummy velocity argument disappears definitionally. -/
theorem torusMixedVelocityVorticityMoment_zero_two_eq_vectorSecondMoment
    (u w : C(Torus3, Vec3)) :
    torusMixedVelocityVorticityMoment u w 0 2 = torusVectorSecondMoment w := by
  unfold torusMixedVelocityVorticityMoment torusVectorSecondMoment
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp

/-- Once the two periodic `L⁶` Sobolev estimates are supplied, all Hölder and exponent
bookkeeping is discharged and the actual zero-frame variance has the required cubic bound.
The factor `8` converts the second moment to the half-enstrophy convention. -/
theorem periodicVorticityWeightedVelocityVariance_zero_sq_le_enstrophy_cubic
    (u w : C(Torus3, Vec3))
    (interpolationConstant velocitySobolevConstant
      vorticitySobolevConstant : ℝ)
    (hinterpolationConstant0 : 0 ≤ interpolationConstant)
    (hvelocityConstant0 : 0 ≤ velocitySobolevConstant)
    (hvorticityConstant0 : 0 ≤ vorticitySobolevConstant)
    (hvelocitySobolev : torusMixedVelocityVorticityMoment u w 6 0 ≤
      velocitySobolevConstant *
        torusMixedVelocityVorticityMoment u w 0 2 ^ 3)
    (hvorticitySobolev : torusMixedVelocityVorticityMoment u w 0 6 ≤
      vorticitySobolevConstant * torusPalinstrophy w ^ 3)
    (hconstants : velocitySobolevConstant ^ 2 * vorticitySobolevConstant ≤
      interpolationConstant ^ 3) :
    periodicVorticityWeightedVelocityVariance u w 0 ^ 2 ≤
      8 * interpolationConstant * torusEnstrophy w ^ 3 * torusPalinstrophy w := by
  have hinterpolation := weighted_variance_interpolation_of_sobolev_moments
    (torusMixedVelocityVorticityMoment_nonneg u w 4 2)
    (torusMixedVelocityVorticityMoment_nonneg u w 2 4)
    (torusMixedVelocityVorticityMoment_nonneg u w 6 0)
    (torusMixedVelocityVorticityMoment_nonneg u w 0 2)
    (torusMixedVelocityVorticityMoment_nonneg u w 0 6)
    (torusPalinstrophy_nonneg w)
    hinterpolationConstant0 hvelocityConstant0 hvorticityConstant0
    (torus_weightedMoment_sq_le_mixedFour_mul_vorticitySecond u w)
    (torus_mixedFour_sq_le_velocitySixth_mul_mixedVorticityFour u w)
    (torus_mixedVorticityFour_sq_le_mixedFour_mul_vorticitySixth u w)
    hvelocitySobolev hvorticitySobolev hconstants
  rw [periodicVorticityWeightedVelocityVariance_zero_eq_mixedMoment]
  rw [show torusMixedVelocityVorticityMoment u w 0 2 =
      torusMixedVelocityVorticityMoment 0 w 0 2 by rfl] at hinterpolation
  rw [torus_vorticitySecondMoment_eq_two_enstrophy] at hinterpolation
  nlinarith

/-- Common-constant form: a single periodic Sobolev constant for the velocity and vorticity
sixth moments is enough. -/
theorem periodicVorticityWeightedVelocityVariance_zero_sq_le_of_common_sobolev
    (u w : C(Torus3, Vec3)) (sobolevConstant : ℝ)
    (hsobolevConstant0 : 0 ≤ sobolevConstant)
    (hvelocitySobolev : torusMixedVelocityVorticityMoment u w 6 0 ≤
      sobolevConstant * torusMixedVelocityVorticityMoment u w 0 2 ^ 3)
    (hvorticitySobolev : torusMixedVelocityVorticityMoment u w 0 6 ≤
      sobolevConstant * torusPalinstrophy w ^ 3) :
    periodicVorticityWeightedVelocityVariance u w 0 ^ 2 ≤
      8 * sobolevConstant * torusEnstrophy w ^ 3 * torusPalinstrophy w := by
  apply periodicVorticityWeightedVelocityVariance_zero_sq_le_enstrophy_cubic
    u w sobolevConstant sobolevConstant sobolevConstant hsobolevConstant0
    hsobolevConstant0 hsobolevConstant0 hvelocitySobolev hvorticitySobolev
  exact le_rfl

/-- Replace the velocity sixth-moment hypothesis by a periodic Sobolev estimate in velocity
gradient energy plus the concrete div--curl identity.  Thus the same domain Sobolev theorem
can be applied to both `u` and `ω`. -/
theorem periodicVorticityWeightedVelocityVariance_zero_sq_le_of_sobolev_divCurl
    (u w : C(Torus3, Vec3)) (sobolevConstant : ℝ)
    (hsobolevConstant0 : 0 ≤ sobolevConstant)
    (hvelocityPeriodicSobolev :
      torusMixedVelocityVorticityMoment u w 6 0 ≤
        sobolevConstant * torusGradientEnergy u ^ 3)
    (hdivCurl : torusGradientEnergy u = torusVectorSecondMoment w)
    (hvorticityPeriodicSobolev :
      torusMixedVelocityVorticityMoment u w 0 6 ≤
        sobolevConstant * torusPalinstrophy w ^ 3) :
    periodicVorticityWeightedVelocityVariance u w 0 ^ 2 ≤
      8 * sobolevConstant * torusEnstrophy w ^ 3 * torusPalinstrophy w := by
  apply periodicVorticityWeightedVelocityVariance_zero_sq_le_of_common_sobolev
    u w sobolevConstant hsobolevConstant0
  · rw [hdivCurl] at hvelocityPeriodicSobolev
    rw [torusMixedVelocityVorticityMoment_zero_two_eq_vectorSecondMoment]
    exact hvelocityPeriodicSobolev
  · exact hvorticityPeriodicSobolev

/-- Application-ready form of the preceding estimate.  The div--curl equality is derived from
ordinary incompressibility and mixed-partial commutation rather than supplied as an equality
hypothesis. -/
theorem periodicVorticityWeightedVelocityVariance_zero_sq_le_of_sobolev_divergence_mixed
    (u w : C(Torus3, Vec3)) (sobolevConstant : ℝ)
    (hsobolevConstant0 : 0 ≤ sobolevConstant)
    (hvelocityPeriodicSobolev :
      torusMixedVelocityVorticityMoment u w 6 0 ≤
        sobolevConstant * torusGradientEnergy u ^ 3)
    (hvorticityPeriodicSobolev :
      torusMixedVelocityVorticityMoment u w 0 6 ≤
        sobolevConstant * torusPalinstrophy w ^ 3)
    (huLift : ContDiff ℝ 1 (torusLift u))
    (hw : ∀ x : Torus3, w x = torusCurl u x)
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hfirst : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => periodicFirstDerivative u k j x) i y))
    (hcross : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x * periodicFirstDerivative u j i x))
    (hsecond : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      u x j * periodicSecondDerivative u i j i x))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0)
    (hmixed : ∀ (i k j : Fin 3) (x : Torus3),
      periodicSecondDerivative u i k j x = periodicSecondDerivative u k i j x)
    (hcurl : Integrable (fun x : Torus3 => ‖periodicCoordinateCurl u x‖ ^ 2)) :
    periodicVorticityWeightedVelocityVariance u w 0 ^ 2 ≤
      8 * sobolevConstant * torusEnstrophy w ^ 3 * torusPalinstrophy w := by
  apply periodicVorticityWeightedVelocityVariance_zero_sq_le_of_sobolev_divCurl
    u w sobolevConstant hsobolevConstant0 hvelocityPeriodicSobolev
  · exact torusGradientEnergy_eq_torusVectorSecondMoment_of_curl_divergence_mixed
      u w huLift hw hu hfirst hcross hsecond hdiv hmixed hcurl
  · exact hvorticityPeriodicSobolev

/-- Fully discharged spatial-interpolation estimate.  Both sixth-moment Sobolev premises are
now consequences of the Euclidean transfer theorem; the vorticity mean-zero normalization is
itself derived from `w = curl u`.  What remains explicit is ordinary smoothness,
square-integrability, incompressibility, and the mixed-partial data needed by div--curl. -/
theorem periodicVorticityWeightedVelocityVariance_zero_sq_le_of_euclidean_sobolev
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u w : C(Torus3, Vec3))
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
    (hfirst : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => periodicFirstDerivative u k j x) i y))
    (hcross : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x * periodicFirstDerivative u j i x))
    (hsecond : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      u x j * periodicSecondDerivative u i j i x))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0)
    (hmixed : ∀ (i k j : Fin 3) (x : Torus3),
      periodicSecondDerivative u i k j x = periodicSecondDerivative u k i j x)
    (hcurl : Integrable (fun x : Torus3 => ‖periodicCoordinateCurl u x‖ ^ 2)) :
    periodicVorticityWeightedVelocityVariance u w 0 ^ 2 ≤
      8 * torusVectorSobolevMomentConstant B *
        torusEnstrophy w ^ 3 * torusPalinstrophy w := by
  apply
    periodicVorticityWeightedVelocityVariance_zero_sq_le_of_sobolev_divergence_mixed
      u w (torusVectorSobolevMomentConstant B)
      (torusVectorSobolevMomentConstant_nonneg B)
  · exact torus_velocitySixthMoment_le_gradientEnergy_cubic
      B hB u w humean huSlice huSq huLift
  · exact torus_vorticitySixthMoment_le_palinstrophy_cubic
      B hB u w
        (torusCurlField_mean_zero u w hwCurl huLift
          (fun i j y => huSlice j i y) huSq)
        hwSlice hwSq hwLift
  · exact huLift
  · exact hwCurl
  · exact fun i j y => huSlice j i y
  · exact hfirst
  · exact hcross
  · exact hsecond
  · exact hdiv
  · exact hmixed
  · exact hcurl

/-- Correlation-refined root-free quotient remainder.  On the positive-production branch,
the exact normalized correlation replaces `Q` by `correlation * Q`; this retains signed
cancellation before Young's inequality instead of estimating the absolute Cauchy ledger. -/
theorem correlated_quotient_variance_cubic_remainder
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
      27 * (interpolationConstant *
        (positiveProductionCorrelation production quotient weightedVariance *
          quotientFraction) ^ 2 * enstrophy ^ 3) /
        (32 * viscosity ^ 3) := by
  let correlation :=
    positiveProductionCorrelation production quotient weightedVariance
  have hcorrelation0 : 0 ≤ correlation :=
    positiveProductionCorrelation_nonneg production quotient weightedVariance
      hquotient0 hvariance0
  have hcorrelationExact :
      correlation * (quotient * weightedVariance) = production ^ 2 := by
    have hexact := positiveProductionCorrelation_mul_eq_positivePart_sq hproduction
    simpa [correlation, max_eq_left hproduction0] using hexact
  have hproduction' :
      production ^ 2 ≤ (correlation * quotient) * weightedVariance := by
    nlinarith [hcorrelationExact]
  have hquotient' :
      correlation * quotient ≤
        (correlation * quotientFraction) * palinstrophy := by
    calc
      correlation * quotient ≤ correlation * (quotientFraction * palinstrophy) :=
        mul_le_mul_of_nonneg_left hquotient hcorrelation0
      _ = (correlation * quotientFraction) * palinstrophy := by ring
  exact quotient_variance_cubic_remainder hproduction0 hproduction'
    (mul_nonneg hcorrelation0 hquotient0) hvariance0
    (mul_nonneg hcorrelation0 hfraction0) henstrophy0 hpalinstrophy0
    hconstant0 hviscosity hquotient' hvariance

/-- The actual signed stretching production satisfies the standard viscous cubic remainder
once (i) the quotient factorization proved in `Enstrophy.lean`, (ii) a quotient-fraction
bound, and (iii) the two periodic sixth-moment Sobolev estimates are supplied.  Negative
production is handled without any sign hypothesis. -/
theorem integral_torusStretchingProduction_le_cubic_remainder
    (u w : C(Torus3, Vec3))
    (viscosity quotientFraction interpolationConstant
      velocitySobolevConstant vorticitySobolevConstant : ℝ)
    (hviscosity : 0 < viscosity)
    (hquotientFraction0 : 0 ≤ quotientFraction)
    (hinterpolationConstant0 : 0 ≤ interpolationConstant)
    (hvelocityConstant0 : 0 ≤ velocitySobolevConstant)
    (hvorticityConstant0 : 0 ≤ vorticitySobolevConstant)
    (hfactorization :
      (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
        (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) *
          periodicVorticityWeightedVelocityVariance u w 0)
    (hquotient :
      (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) ≤
        quotientFraction * torusPalinstrophy w)
    (hvelocitySobolev : torusMixedVelocityVorticityMoment u w 6 0 ≤
      velocitySobolevConstant *
        torusMixedVelocityVorticityMoment u w 0 2 ^ 3)
    (hvorticitySobolev : torusMixedVelocityVorticityMoment u w 0 6 ≤
      vorticitySobolevConstant * torusPalinstrophy w ^ 3)
    (hconstants : velocitySobolevConstant ^ 2 * vorticitySobolevConstant ≤
      interpolationConstant ^ 3) :
    (∫ x : Torus3, torusStretchingProduction u w x) ≤
      (viscosity / 2) * torusPalinstrophy w +
        27 * interpolationConstant * quotientFraction ^ 2 * torusEnstrophy w ^ 3 /
          (4 * viscosity ^ 3) := by
  let production : ℝ := ∫ x : Torus3, torusStretchingProduction u w x
  let quotient : ℝ :=
    ∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x
  let variance : ℝ := periodicVorticityWeightedVelocityVariance u w 0
  have hquotient0 : 0 ≤ quotient := by
    dsimp [quotient]
    exact integral_nonneg fun x =>
      periodicVorticitySelfTransportQuotientSq_nonneg w x
  have hvariance0 : 0 ≤ variance := by
    dsimp [variance]
    rw [periodicVorticityWeightedVelocityVariance_zero_eq_mixedMoment]
    exact torusMixedVelocityVorticityMoment_nonneg u w 2 2
  have henstrophy0 : 0 ≤ torusEnstrophy w :=
    integral_nonneg fun x => vorticityEnergyField_nonneg w x
  have hvarianceInterpolation : variance ^ 2 ≤
      8 * interpolationConstant * torusEnstrophy w ^ 3 * torusPalinstrophy w := by
    dsimp [variance]
    exact periodicVorticityWeightedVelocityVariance_zero_sq_le_enstrophy_cubic
      u w interpolationConstant velocitySobolevConstant vorticitySobolevConstant
      hinterpolationConstant0 hvelocityConstant0 hvorticityConstant0
      hvelocitySobolev hvorticitySobolev hconstants
  by_cases hproduction0 : 0 ≤ production
  · have hcubic := quotient_variance_cubic_remainder
      (production := production) (quotient := quotient)
      (quotientFraction := quotientFraction) (weightedVariance := variance)
      (enstrophy := torusEnstrophy w) (palinstrophy := torusPalinstrophy w)
      (interpolationConstant := 8 * interpolationConstant)
      (viscosity := viscosity)
      hproduction0 (by simpa [production, quotient, variance] using hfactorization)
      hquotient0 hvariance0 hquotientFraction0 henstrophy0
      (torusPalinstrophy_nonneg w) (by positivity) hviscosity
      (by simpa [quotient] using hquotient) hvarianceInterpolation
    dsimp [production] at hcubic
    convert hcubic using 1
    all_goals ring
  · have hright0 : 0 ≤
        (viscosity / 2) * torusPalinstrophy w +
          27 * interpolationConstant * quotientFraction ^ 2 * torusEnstrophy w ^ 3 /
            (4 * viscosity ^ 3) := by
      apply add_nonneg
      · exact mul_nonneg (div_nonneg hviscosity.le (by norm_num))
          (torusPalinstrophy_nonneg w)
      · apply div_nonneg
        · exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) hinterpolationConstant0)
              (sq_nonneg quotientFraction))
            (pow_nonneg henstrophy0 3)
        · positivity
    dsimp [production] at hproduction0
    linarith

/-- Signed-correlation refinement of the concrete stretching remainder.  The coefficient
vanishes for exact spatial cancellation (for example a periodic Beltrami production with
zero integral) even when the absolute self-transport quotient is nonzero. -/
theorem integral_torusStretchingProduction_le_correlated_cubic_remainder
    (u w : C(Torus3, Vec3))
    (viscosity quotientFraction interpolationConstant
      velocitySobolevConstant vorticitySobolevConstant : ℝ)
    (hviscosity : 0 < viscosity)
    (hquotientFraction0 : 0 ≤ quotientFraction)
    (hinterpolationConstant0 : 0 ≤ interpolationConstant)
    (hvelocityConstant0 : 0 ≤ velocitySobolevConstant)
    (hvorticityConstant0 : 0 ≤ vorticitySobolevConstant)
    (hfactorization :
      (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
        (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) *
          periodicVorticityWeightedVelocityVariance u w 0)
    (hquotient :
      (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) ≤
        quotientFraction * torusPalinstrophy w)
    (hvelocitySobolev : torusMixedVelocityVorticityMoment u w 6 0 ≤
      velocitySobolevConstant *
        torusMixedVelocityVorticityMoment u w 0 2 ^ 3)
    (hvorticitySobolev : torusMixedVelocityVorticityMoment u w 0 6 ≤
      vorticitySobolevConstant * torusPalinstrophy w ^ 3)
    (hconstants : velocitySobolevConstant ^ 2 * vorticitySobolevConstant ≤
      interpolationConstant ^ 3) :
    (∫ x : Torus3, torusStretchingProduction u w x) ≤
      (viscosity / 2) * torusPalinstrophy w +
        27 * interpolationConstant *
            (positiveProductionCorrelation
              (∫ x : Torus3, torusStretchingProduction u w x)
              (∫ x : Torus3,
                periodicVorticitySelfTransportQuotientSq w x)
              (periodicVorticityWeightedVelocityVariance u w 0) *
              quotientFraction) ^ 2 * torusEnstrophy w ^ 3 /
          (4 * viscosity ^ 3) := by
  let production : ℝ := ∫ x : Torus3, torusStretchingProduction u w x
  let quotient : ℝ :=
    ∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x
  let variance : ℝ := periodicVorticityWeightedVelocityVariance u w 0
  let correlation : ℝ :=
    positiveProductionCorrelation production quotient variance
  have hquotient0 : 0 ≤ quotient := by
    dsimp [quotient]
    exact integral_nonneg fun x =>
      periodicVorticitySelfTransportQuotientSq_nonneg w x
  have hvariance0 : 0 ≤ variance := by
    dsimp [variance]
    rw [periodicVorticityWeightedVelocityVariance_zero_eq_mixedMoment]
    exact torusMixedVelocityVorticityMoment_nonneg u w 2 2
  have henstrophy0 : 0 ≤ torusEnstrophy w :=
    integral_nonneg fun x => vorticityEnergyField_nonneg w x
  have hvarianceInterpolation : variance ^ 2 ≤
      8 * interpolationConstant * torusEnstrophy w ^ 3 * torusPalinstrophy w := by
    dsimp [variance]
    exact periodicVorticityWeightedVelocityVariance_zero_sq_le_enstrophy_cubic
      u w interpolationConstant velocitySobolevConstant vorticitySobolevConstant
      hinterpolationConstant0 hvelocityConstant0 hvorticityConstant0
      hvelocitySobolev hvorticitySobolev hconstants
  by_cases hproduction0 : 0 ≤ production
  · have hcubic := correlated_quotient_variance_cubic_remainder
      (production := production) (quotient := quotient)
      (quotientFraction := quotientFraction) (weightedVariance := variance)
      (enstrophy := torusEnstrophy w) (palinstrophy := torusPalinstrophy w)
      (interpolationConstant := 8 * interpolationConstant)
      (viscosity := viscosity)
      hproduction0 (by simpa [production, quotient, variance] using hfactorization)
      hquotient0 hvariance0 hquotientFraction0 henstrophy0
      (torusPalinstrophy_nonneg w) (by positivity) hviscosity
      (by simpa [quotient] using hquotient) hvarianceInterpolation
    dsimp [production, quotient, variance, correlation] at hcubic ⊢
    convert hcubic using 1
    all_goals ring
  · have hright0 : 0 ≤
        (viscosity / 2) * torusPalinstrophy w +
          27 * interpolationConstant *
              (positiveProductionCorrelation production quotient variance *
                quotientFraction) ^ 2 * torusEnstrophy w ^ 3 /
            (4 * viscosity ^ 3) := by
      apply add_nonneg
      · exact mul_nonneg (div_nonneg hviscosity.le (by norm_num))
          (torusPalinstrophy_nonneg w)
      · apply div_nonneg
        · exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) hinterpolationConstant0)
              (sq_nonneg _))
            (pow_nonneg henstrophy0 3)
        · positivity
    dsimp [production, quotient, variance, correlation] at hproduction0 ⊢
    dsimp [production, quotient, variance] at hright0
    linarith

/-- Production-level endpoint with all standard Sobolev inputs discharged.  The only
nonstandard analytic premise left is the genuinely dynamical quotient depletion
`Q ≤ quotientFraction · P`; the factorization itself is an earlier exact kinematic theorem.
The div--curl equality can be supplied by `DivCurl.lean` from ordinary incompressibility. -/
theorem integral_torusStretchingProduction_le_cubic_remainder_of_euclidean_sobolev
    (B viscosity quotientFraction : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u w : C(Torus3, Vec3))
    (hviscosity : 0 < viscosity)
    (hquotientFraction0 : 0 ≤ quotientFraction)
    (hfactorization :
      (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
        (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) *
          periodicVorticityWeightedVelocityVariance u w 0)
    (hquotient :
      (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) ≤
        quotientFraction * torusPalinstrophy w)
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
    (hdivCurl : torusGradientEnergy u = torusVectorSecondMoment w) :
    (∫ x : Torus3, torusStretchingProduction u w x) ≤
      (viscosity / 2) * torusPalinstrophy w +
        27 * torusVectorSobolevMomentConstant B * quotientFraction ^ 2 *
          torusEnstrophy w ^ 3 / (4 * viscosity ^ 3) := by
  apply integral_torusStretchingProduction_le_cubic_remainder
    u w viscosity quotientFraction
      (torusVectorSobolevMomentConstant B)
      (torusVectorSobolevMomentConstant B)
      (torusVectorSobolevMomentConstant B)
      hviscosity hquotientFraction0
      (torusVectorSobolevMomentConstant_nonneg B)
      (torusVectorSobolevMomentConstant_nonneg B)
      (torusVectorSobolevMomentConstant_nonneg B)
      hfactorization hquotient
  · have hvelocity := torus_velocitySixthMoment_le_gradientEnergy_cubic
      B hB u w humean huSlice huSq huLift
    rw [hdivCurl] at hvelocity
    rw [torusMixedVelocityVorticityMoment_zero_two_eq_vectorSecondMoment]
    exact hvelocity
  · exact torus_vorticitySixthMoment_le_palinstrophy_cubic
      B hB u w
        (torusCurlField_mean_zero u w hwCurl huLift
          (fun i j y => huSlice j i y) huSq)
        hwSlice hwSq hwLift
  · ring_nf
    exact le_rfl

/-- Fully concrete production endpoint.  The quotient fraction is no longer a free scalar:
it is the zero-safe ratio constructed from the actual vorticity field and proved above to
reconstruct its self-transport quotient exactly. -/
theorem integral_torusStretchingProduction_le_cubic_remainder_of_concrete_fraction
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
    (∫ x : Torus3, torusStretchingProduction u w x) ≤
      (viscosity / 2) * torusPalinstrophy w +
        27 * torusVectorSobolevMomentConstant B *
          torusVorticitySelfTransportFraction w ^ 2 * torusEnstrophy w ^ 3 /
            (4 * viscosity ^ 3) := by
  apply
    integral_torusStretchingProduction_le_cubic_remainder_of_euclidean_sobolev
      B viscosity (torusVorticitySelfTransportFraction w) hB u w
      hviscosity (torusVorticitySelfTransportFraction_nonneg w)
      hfactorization
  · change torusVorticitySelfTransportQuotient w ≤
      torusVorticitySelfTransportFraction w * torusPalinstrophy w
    rw [torusVorticitySelfTransportFraction_mul_palinstrophy
      w hwLift hwSq hquotient]
  · exact humean
  · exact huSlice
  · exact huSq
  · exact huLift
  · exact hwCurl
  · exact hwSlice
  · exact hwSq
  · exact hwLift
  · exact hdivCurl

/-- Correlation-refined endpoint with the periodic Sobolev inputs discharged. -/
theorem integral_torusStretchingProduction_le_correlated_cubic_remainder_of_euclidean_sobolev
    (B viscosity quotientFraction : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u w : C(Torus3, Vec3))
    (hviscosity : 0 < viscosity)
    (hquotientFraction0 : 0 ≤ quotientFraction)
    (hfactorization :
      (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
        (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) *
          periodicVorticityWeightedVelocityVariance u w 0)
    (hquotient :
      (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) ≤
        quotientFraction * torusPalinstrophy w)
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
    (hdivCurl : torusGradientEnergy u = torusVectorSecondMoment w) :
    (∫ x : Torus3, torusStretchingProduction u w x) ≤
      (viscosity / 2) * torusPalinstrophy w +
        27 * torusVectorSobolevMomentConstant B *
            (positiveProductionCorrelation
              (∫ x : Torus3, torusStretchingProduction u w x)
              (∫ x : Torus3,
                periodicVorticitySelfTransportQuotientSq w x)
              (periodicVorticityWeightedVelocityVariance u w 0) *
              quotientFraction) ^ 2 * torusEnstrophy w ^ 3 /
          (4 * viscosity ^ 3) := by
  apply integral_torusStretchingProduction_le_correlated_cubic_remainder
    u w viscosity quotientFraction
      (torusVectorSobolevMomentConstant B)
      (torusVectorSobolevMomentConstant B)
      (torusVectorSobolevMomentConstant B)
      hviscosity hquotientFraction0
      (torusVectorSobolevMomentConstant_nonneg B)
      (torusVectorSobolevMomentConstant_nonneg B)
      (torusVectorSobolevMomentConstant_nonneg B)
      hfactorization hquotient
  · have hvelocity := torus_velocitySixthMoment_le_gradientEnergy_cubic
      B hB u w humean huSlice huSq huLift
    rw [hdivCurl] at hvelocity
    rw [torusMixedVelocityVorticityMoment_zero_two_eq_vectorSecondMoment]
    exact hvelocity
  · exact torus_vorticitySixthMoment_le_palinstrophy_cubic
      B hB u w
        (torusCurlField_mean_zero u w hwCurl huLift
          (fun i j y => huSlice j i y) huSq)
        hwSlice hwSq hwLift
  · ring_nf
    exact le_rfl

/-- Fully concrete signed endpoint.  Both the quotient fraction and the production
correlation are the zero-safe values constructed from the actual periodic fields. -/
theorem integral_torusStretchingProduction_le_correlated_cubic_remainder_of_concrete_fraction
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
    (∫ x : Torus3, torusStretchingProduction u w x) ≤
      (viscosity / 2) * torusPalinstrophy w +
        27 * torusVectorSobolevMomentConstant B *
            (positiveProductionCorrelation
              (∫ x : Torus3, torusStretchingProduction u w x)
              (torusVorticitySelfTransportQuotient w)
              (periodicVorticityWeightedVelocityVariance u w 0) *
              torusVorticitySelfTransportFraction w) ^ 2 *
            torusEnstrophy w ^ 3 /
          (4 * viscosity ^ 3) := by
  apply
    integral_torusStretchingProduction_le_correlated_cubic_remainder_of_euclidean_sobolev
      B viscosity (torusVorticitySelfTransportFraction w) hB u w
      hviscosity (torusVorticitySelfTransportFraction_nonneg w)
      hfactorization
  · change torusVorticitySelfTransportQuotient w ≤
      torusVorticitySelfTransportFraction w * torusPalinstrophy w
    rw [torusVorticitySelfTransportFraction_mul_palinstrophy
      w hwLift hwSq hquotient]
  · exact humean
  · exact huSlice
  · exact huSq
  · exact huLift
  · exact hwCurl
  · exact hwSlice
  · exact hwSq
  · exact hwLift
  · exact hdivCurl

/-- Subtracting the viscous term from the production remainder gives the exact pointwise
rate used by the logarithmic continuation criterion. -/
theorem torus_enstrophy_rate_le_cubic_of_production_remainder
    {production viscosity palinstrophy coefficient enstrophy : ℝ}
    (hviscosity0 : 0 ≤ viscosity) (hpalinstrophy0 : 0 ≤ palinstrophy)
    (hproduction : production ≤
      (viscosity / 2) * palinstrophy + coefficient * enstrophy ^ 3) :
    production - viscosity * palinstrophy ≤
      coefficient * enstrophy ^ 3 := by
  nlinarith
