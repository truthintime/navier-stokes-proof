import NSFormal.AnisotropicIntegration
import NSFormal.NewProofAlgebra

/-!
# Concrete periodic anisotropic strain ledger

This file removes the remaining finite-dimensional abstraction from the variable-direction
criterion.  Starting from the concrete coordinate derivatives on `Torus3`, it constructs the
gradient, transpose-gradient, strain, curl, and cross-product actions and proves the exact
pointwise identity used before periodic integration by parts.
-/

open Filter Function MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

/-- Coordinate form of `(e · ∇)u`. -/
def periodicGradientAction
    (u e : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  WithLp.toLp 2 fun j =>
    ∑ i : Fin 3, e x i * periodicFirstDerivative u i j x

/-- Coordinate form of `(∇u)ᵀ e`. -/
def periodicTransposeGradientAction
    (u e : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  WithLp.toLp 2 fun i =>
    ∑ j : Fin 3, periodicFirstDerivative u i j x * e x j

/-- Symmetric velocity-gradient action in the selected direction. -/
def periodicStrainAction
    (u e : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  (2 : ℝ)⁻¹ •
    (periodicGradientAction u e x + periodicTransposeGradientAction u e x)

/-- Antisymmetric velocity-gradient action in the selected direction. -/
def periodicSkewAction
    (u e : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  (2 : ℝ)⁻¹ •
    (periodicGradientAction u e x - periodicTransposeGradientAction u e x)

/-- Curl reconstructed from the concrete periodic coordinate derivatives. -/
def periodicCoordinateCurl (u : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  WithLp.toLp 2 ![
    periodicFirstDerivative u 1 2 x - periodicFirstDerivative u 2 1 x,
    periodicFirstDerivative u 2 0 x - periodicFirstDerivative u 0 2 x,
    periodicFirstDerivative u 0 1 x - periodicFirstDerivative u 1 0 x]

/-- Standard cross product on `Vec3`, kept inside the `L²`-Euclidean wrapper. -/
def vec3Cross (a b : Vec3) : Vec3 :=
  WithLp.toLp 2 ![
    a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

/-- A concrete global unit direction used to witness that the anisotropic hypotheses are
simultaneously satisfiable. -/
def constantCoordinateDirection : Torus3 → Vec3 :=
  fun _ => EuclideanSpace.single 0 (1 : ℝ)

/-- Velocity observed in a spatially constant Galilean frame. -/
def centeredVelocity (u : Torus3 → Vec3) (a : Vec3) : Torus3 → Vec3 :=
  fun x => u x - a

@[simp]
theorem centeredVelocity_apply (u : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    centeredVelocity u a x = u x - a := rfl

@[simp]
theorem periodicFirstDerivative_centeredVelocity
    (u : Torus3 → Vec3) (a : Vec3) (i j : Fin 3) (x : Torus3) :
    periodicFirstDerivative (centeredVelocity u a) i j x =
      periodicFirstDerivative u i j x := by
  unfold periodicFirstDerivative torusCoordinateDerivative
  unfold torusCoordinateSliceDerivative
  congr 1
  funext r
  change deriv (fun s =>
    torusCoordinateSliceLift (fun y => u y j) i (Fin.removeNth i x) s - a j) r = _
  rw [deriv_sub_const]

@[simp]
theorem periodicSecondDerivative_centeredVelocity
    (u : Torus3 → Vec3) (a : Vec3) (i k j : Fin 3) (x : Torus3) :
    periodicSecondDerivative (centeredVelocity u a) i k j x =
      periodicSecondDerivative u i k j x := by
  simp [periodicSecondDerivative]

@[simp]
theorem periodicGradientL1_centeredVelocity
    (u : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    periodicGradientL1 (centeredVelocity u a) x = periodicGradientL1 u x := by
  simp [periodicGradientL1]

@[simp]
theorem periodicGradientAction_centeredVelocity
    (u e : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    periodicGradientAction (centeredVelocity u a) e x =
      periodicGradientAction u e x := by
  simp [periodicGradientAction]

@[simp]
theorem periodicTransposeGradientAction_centeredVelocity
    (u e : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    periodicTransposeGradientAction (centeredVelocity u a) e x =
      periodicTransposeGradientAction u e x := by
  simp [periodicTransposeGradientAction]

@[simp]
theorem periodicStrainAction_centeredVelocity
    (u e : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    periodicStrainAction (centeredVelocity u a) e x =
      periodicStrainAction u e x := by
  simp [periodicStrainAction]

@[simp]
theorem periodicCoordinateCurl_centeredVelocity
    (u : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    periodicCoordinateCurl (centeredVelocity u a) x =
      periodicCoordinateCurl u x := by
  simp [periodicCoordinateCurl]

@[simp]
theorem periodicFirstDerivative_zero_field (i j : Fin 3) (x : Torus3) :
    periodicFirstDerivative (fun _ : Torus3 => (0 : Vec3)) i j x = 0 := by
  simp [periodicFirstDerivative]

@[simp]
theorem periodicFirstDerivative_constantCoordinateDirection
    (i j : Fin 3) (x : Torus3) :
    periodicFirstDerivative constantCoordinateDirection i j x = 0 := by
  simp [periodicFirstDerivative, constantCoordinateDirection]

@[simp]
theorem periodicSecondDerivative_zero_field (i k j : Fin 3) (x : Torus3) :
    periodicSecondDerivative (fun _ : Torus3 => (0 : Vec3)) i k j x = 0 := by
  simp [periodicSecondDerivative]

/-- The skew gradient action is minus one half of `e × curl u` for the coordinate convention
`D i j = ∂ᵢuⱼ`. -/
theorem periodicSkewAction_eq_neg_half_cross_curl
    (u e : Torus3 → Vec3) (x : Torus3) :
    periodicSkewAction u e x =
      -(2 : ℝ)⁻¹ • vec3Cross (e x) (periodicCoordinateCurl u x) := by
  ext q
  fin_cases q <;>
    simp [periodicSkewAction, periodicGradientAction,
      periodicTransposeGradientAction, periodicCoordinateCurl, vec3Cross,
      Fin.sum_univ_three] <;>
    ring

/-- Parallelogram identity in the normalization used for strain and skew actions. -/
theorem norm_half_add_sq_eq_norm_half_sub_sq_add_inner (g h : Vec3) :
    ‖(2 : ℝ)⁻¹ • (g + h)‖ ^ 2 =
      ‖(2 : ℝ)⁻¹ • (g - h)‖ ^ 2 + inner ℝ g h := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm h g]
  ring

/-- Exact amplitude--direction derivative split.  If `ξ` is unit and its derivative is tangent
to the unit sphere, differentiating `ω = ρ ξ` gives orthogonal scalar and directional pieces. -/
theorem norm_amplitude_direction_derivative_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ dρ : ℝ) (ξ dξ : E)
    (hunit : ‖ξ‖ = 1) (horth : inner ℝ ξ dξ = 0) :
    ‖dρ • ξ + ρ • dξ‖ ^ 2 = dρ ^ 2 + ρ ^ 2 * ‖dξ‖ ^ 2 := by
  have horth' : inner ℝ dξ ξ = 0 := by
    rw [real_inner_comm]
    exact horth
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [horth, horth', norm_smul, norm_smul, hunit]
  simp only [Real.norm_eq_abs, mul_one, sq_abs]
  rw [mul_pow, sq_abs]
  ring

/-- Directional variation is bounded by the full derivative of `ω = ρ ξ`. -/
theorem amplitude_sq_mul_direction_derivative_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ dρ : ℝ) (ξ dξ : E)
    (hunit : ‖ξ‖ = 1) (horth : inner ℝ ξ dξ = 0) :
    ρ ^ 2 * ‖dξ‖ ^ 2 ≤ ‖dρ • ξ + ρ • dξ‖ ^ 2 := by
  rw [norm_amplitude_direction_derivative_sq ρ dρ ξ dξ hunit horth]
  nlinarith [sq_nonneg dρ]

/-- The triple coordinate sum used by periodic integration is exactly the inner product of the
gradient and transpose-gradient actions. -/
theorem sum_anisotropicMixedIntegrand_eq_inner_gradient_actions
    (u e : Torus3 → Vec3) (x : Torus3) :
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      anisotropicMixedIntegrand u e i j k x) =
      inner ℝ (periodicTransposeGradientAction u e x)
        (periodicGradientAction u e x) := by
  let term : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k =>
    (periodicFirstDerivative u i j x * e x j) *
      (e x k * periodicFirstDerivative u k i x)
  calc
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        anisotropicMixedIntegrand u e i j k x) =
        ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, term i j k := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [term, anisotropicMixedIntegrand]
      ring
    _ = ∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, term i j k := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact Finset.sum_comm
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, term i j k :=
      Finset.sum_comm
    _ = inner ℝ (periodicTransposeGradientAction u e x)
        (periodicGradientAction u e x) := by
      rw [PiLp.inner_apply]
      simp only [periodicTransposeGradientAction, periodicGradientAction,
        Real.inner_apply]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [term]

/-- Concrete pointwise identity behind the variable-direction criterion. -/
theorem norm_periodicStrainAction_sq_eq_cross_curl_add_mixed
    (u e : Torus3 → Vec3) (x : Torus3) :
    ‖periodicStrainAction u e x‖ ^ 2 =
      ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2 / 4 +
        inner ℝ (periodicTransposeGradientAction u e x)
          (periodicGradientAction u e x) := by
  have hpar := norm_half_add_sq_eq_norm_half_sub_sq_add_inner
    (periodicGradientAction u e x) (periodicTransposeGradientAction u e x)
  rw [← periodicStrainAction, ← periodicSkewAction] at hpar
  rw [hpar, periodicSkewAction_eq_neg_half_cross_curl]
  have hhalf : |(2 : ℝ)⁻¹| = (2 : ℝ)⁻¹ :=
    abs_of_pos (inv_pos.mpr (by norm_num))
  rw [norm_smul, Real.norm_eq_abs, abs_neg, hhalf]
  rw [real_inner_comm (periodicTransposeGradientAction u e x)
    (periodicGradientAction u e x)]
  ring

/-- Exact integrated periodic anisotropic identity.  All analytic hypotheses are on the
displayed concrete fields.  The mixed term is eliminated by the previously proved
three-factor Haar integration identity, leaving only transverse vorticity and the explicit
direction-gradient error. -/
theorem integral_periodicStrainAction_sq_eq_cross_curl_sub_direction_error
    (u e : Torus3 → Vec3)
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (he : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => e x j) i y))
    (huFirst : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => periodicFirstDerivative u k j x) i y))
    (hleft : ∀ i j k : Fin 3,
      Integrable (anisotropicMixedIntegrand u e i j k))
    (herror : ∀ i j k : Fin 3,
      Integrable (anisotropicDirectionErrorIntegrand u e i j k))
    (hmiddle : ∀ i j k : Fin 3,
      Integrable (anisotropicDivergenceIntegrand u e i j k))
    (hdiv : ∀ (x : Torus3) (k : Fin 3),
      ∑ i : Fin 3, periodicSecondDerivative u i k i x = 0)
    (hcross : Integrable (fun x : Torus3 =>
      ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2)) :
    (∫ x : Torus3, ‖periodicStrainAction u e x‖ ^ 2) =
      (∫ x : Torus3, ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2) / 4 -
        (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x) := by
  have hmixedI : ∀ j k : Fin 3, Integrable (fun x : Torus3 =>
      ∑ i : Fin 3, anisotropicMixedIntegrand u e i j k x) := by
    intro j k
    exact integrable_finsetSum Finset.univ fun i _hi => hleft i j k
  have hmixedK : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      ∑ k : Fin 3, ∑ i : Fin 3, anisotropicMixedIntegrand u e i j k x) := by
    intro j
    exact integrable_finsetSum Finset.univ fun k _hk => hmixedI j k
  have hmixed : Integrable (fun x : Torus3 =>
      ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        anisotropicMixedIntegrand u e i j k x) :=
    integrable_finsetSum Finset.univ fun j _hj => hmixedK j
  have hcrossQuarter : Integrable (fun x : Torus3 =>
      ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2 / 4) := by
    simpa only [div_eq_mul_inv, mul_comm] using hcross.const_mul (4 : ℝ)⁻¹
  have hpoint : (fun x : Torus3 => ‖periodicStrainAction u e x‖ ^ 2) =
      fun x => ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2 / 4 +
        ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          anisotropicMixedIntegrand u e i j k x := by
    funext x
    rw [norm_periodicStrainAction_sq_eq_cross_curl_add_mixed,
      sum_anisotropicMixedIntegrand_eq_inner_gradient_actions]
  have hintegralMixed :
      (∫ x : Torus3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        anisotropicMixedIntegrand u e i j k x) =
        ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, anisotropicMixedIntegrand u e i j k x := by
    calc
      (∫ x : Torus3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          anisotropicMixedIntegrand u e i j k x) =
          ∑ j : Fin 3, ∫ x : Torus3,
            ∑ k : Fin 3, ∑ i : Fin 3,
              anisotropicMixedIntegrand u e i j k x :=
        MeasureTheory.integral_finsetSum Finset.univ fun j _hj => hmixedK j
      _ = ∑ j : Fin 3, ∑ k : Fin 3, ∫ x : Torus3,
          ∑ i : Fin 3, anisotropicMixedIntegrand u e i j k x := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact MeasureTheory.integral_finsetSum Finset.univ fun k _hk => hmixedI j k
      _ = ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, anisotropicMixedIntegrand u e i j k x := by
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro k _hk
        exact MeasureTheory.integral_finsetSum Finset.univ fun i _hi => hleft i j k
  have hmixedIdentity := torus3_anisotropic_mixed_pairing_eq_direction_error
    u e hu he huFirst hleft herror hmiddle hdiv
  have hcrossIntegral :
      (∫ x : Torus3,
        ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2 / 4) =
        (∫ x : Torus3,
          ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2) / 4 := by
    have hfun : (fun x : Torus3 =>
        ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2 / 4) =
        fun x => (4 : ℝ)⁻¹ *
          ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2 := by
      funext x
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
    ring
  calc
    (∫ x : Torus3, ‖periodicStrainAction u e x‖ ^ 2) =
        ∫ x : Torus3,
          (‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2 / 4 +
            ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
              anisotropicMixedIntegrand u e i j k x) := by rw [hpoint]
    _ = (∫ x : Torus3,
          ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2 / 4) +
        (∫ x : Torus3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          anisotropicMixedIntegrand u e i j k x) :=
      MeasureTheory.integral_add hcrossQuarter hmixed
    _ = (∫ x : Torus3,
          ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2) / 4 +
        (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, anisotropicMixedIntegrand u e i j k x) := by
      rw [hintegralMixed, hcrossIntegral]
    _ = (∫ x : Torus3,
          ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2) / 4 -
        (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x) := by
      rw [hmixedIdentity]
      ring

/-- Concrete fourth-power anisotropic ledger on `Torus3`.  The rightmost quantity is the
actual spatial mixed error with the coordinate-`ℓ¹` gradient envelope.  The constant
`5832 = 2 * 54²` is produced by the checked three-dimensional component count and the exact
quadratic split, not inserted as an assumption. -/
theorem integral_periodicStrainAction_sq_sq_le_cross_curl_add_mixed
    (u e : Torus3 → Vec3)
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (he : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => e x j) i y))
    (huFirst : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => periodicFirstDerivative u k j x) i y))
    (hleft : ∀ i j k : Fin 3,
      Integrable (anisotropicMixedIntegrand u e i j k))
    (herror : ∀ i j k : Fin 3,
      Integrable (anisotropicDirectionErrorIntegrand u e i j k))
    (hmiddle : ∀ i j k : Fin 3,
      Integrable (anisotropicDivergenceIntegrand u e i j k))
    (hdiv : ∀ (x : Torus3) (k : Fin 3),
      ∑ i : Fin 3, periodicSecondDerivative u i k i x = 0)
    (hunit : ∀ x : Torus3, ‖e x‖ = 1)
    (hcross : Integrable (fun x : Torus3 =>
      ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2))
    (hdensity : Integrable (fun x : Torus3 =>
      ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x)) :
    (∫ x : Torus3, ‖periodicStrainAction u e x‖ ^ 2) ^ 2 ≤
      (∫ x : Torus3,
        ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2) ^ 2 / 8 +
      5832 * (∫ x : Torus3,
        ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x) ^ 2 := by
  let strainSq : ℝ := ∫ x : Torus3, ‖periodicStrainAction u e x‖ ^ 2
  let crossSq : ℝ := ∫ x : Torus3,
    ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2
  let mixed : ℝ := 54 * ∫ x : Torus3,
    ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x
  let errorSum : ℝ := ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
    ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x
  have hidentity := integral_periodicStrainAction_sq_eq_cross_curl_sub_direction_error
    u e hu he huFirst hleft herror hmiddle hdiv hcross
  have herrorBound :=
    abs_anisotropic_direction_error_sum_le_gradientL1 u e hunit hdensity
  have hstrain0 : 0 ≤ strainSq := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun x => sq_nonneg _
  have hcross0 : 0 ≤ crossSq := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun x => sq_nonneg _
  have hdensity0 : 0 ≤ ∫ x : Torus3,
      ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun x =>
      mul_nonneg
        (mul_nonneg (norm_nonneg _) (periodicGradientL1_nonneg u x))
        (periodicGradientL1_nonneg e x)
  have hmixed0 : 0 ≤ mixed := by
    dsimp [mixed]
    exact mul_nonneg (by norm_num) hdensity0
  have hstrain : strainSq ≤ crossSq / 4 + mixed := by
    dsimp [strainSq, crossSq, mixed, errorSum] at hidentity herrorBound ⊢
    linarith [neg_le_abs errorSum]
  have hfourth := variable_direction_strain_fourth_split
    hstrain0 hcross0 hmixed0 hstrain
  dsimp [strainSq, crossSq, mixed] at hfourth ⊢
  convert hfourth using 1
  all_goals ring

/-- Named bundle of the concrete hypotheses used by the periodic anisotropic ledger.  It is a
predicate on displayed fields, not a typeclass postulating that a Navier--Stokes solution or a
direction selector exists. -/
structure IsPeriodicAnisotropicPair (u e : Torus3 → Vec3) : Prop where
  velocitySlices : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
    ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y)
  directionSlices : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
    ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => e x j) i y)
  firstDerivativeSlices : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
    ContDiff ℝ 1
      (torusCoordinateSliceLift (fun x => periodicFirstDerivative u k j x) i y)
  mixedIntegrable : ∀ i j k : Fin 3,
    Integrable (anisotropicMixedIntegrand u e i j k)
  errorIntegrable : ∀ i j k : Fin 3,
    Integrable (anisotropicDirectionErrorIntegrand u e i j k)
  divergenceIntegrable : ∀ i j k : Fin 3,
    Integrable (anisotropicDivergenceIntegrand u e i j k)
  differentiatedDivergence : ∀ (x : Torus3) (k : Fin 3),
    ∑ i : Fin 3, periodicSecondDerivative u i k i x = 0
  unitDirection : ∀ x : Torus3, ‖e x‖ = 1
  crossIntegrable : Integrable (fun x : Torus3 =>
    ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2)
  densityIntegrable : Integrable (fun x : Torus3 =>
    ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x)

/-- The bundled hypotheses are nonvacuous: zero velocity and a displayed constant coordinate
unit vector satisfy every regularity, divergence, unit-length, and integrability field. -/
theorem constant_direction_zero_velocity_isPeriodicAnisotropicPair :
    IsPeriodicAnisotropicPair
      (fun _ : Torus3 => (0 : Vec3)) constantCoordinateDirection := by
  constructor
  · intro i j y
    change ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ))
    exact contDiff_const
  · intro i j y
    change ContDiff ℝ 1
      (fun _ : ℝ => EuclideanSpace.single 0 (1 : ℝ) j)
    exact contDiff_const
  · intro i k j y
    have hfun : (fun x : Torus3 =>
        periodicFirstDerivative (fun _ : Torus3 => (0 : Vec3)) k j x) =
        fun _ : Torus3 => (0 : ℝ) := by
      funext x
      simp
    rw [hfun]
    change ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ))
    exact contDiff_const
  · intro i j k
    have hfun : anisotropicMixedIntegrand
        (fun _ : Torus3 => (0 : Vec3)) constantCoordinateDirection i j k =
        fun _ : Torus3 => (0 : ℝ) := by
      funext x
      simp [anisotropicMixedIntegrand]
    rw [hfun]
    exact integrable_zero Torus3 ℝ volume
  · intro i j k
    have hfun : anisotropicDirectionErrorIntegrand
        (fun _ : Torus3 => (0 : Vec3)) constantCoordinateDirection i j k =
        fun _ : Torus3 => (0 : ℝ) := by
      funext x
      simp [anisotropicDirectionErrorIntegrand]
    rw [hfun]
    exact integrable_zero Torus3 ℝ volume
  · intro i j k
    have hfun : anisotropicDivergenceIntegrand
        (fun _ : Torus3 => (0 : Vec3)) constantCoordinateDirection i j k =
        fun _ : Torus3 => (0 : ℝ) := by
      funext x
      simp [anisotropicDivergenceIntegrand]
    rw [hfun]
    exact integrable_zero Torus3 ℝ volume
  · intro x k
    simp
  · intro x
    simp [constantCoordinateDirection]
  · simp [periodicCoordinateCurl, vec3Cross]
  · simp

/-- Bundled wrapper for the concrete fourth-power theorem. -/
theorem IsPeriodicAnisotropicPair.strain_fourth_le
    {u e : Torus3 → Vec3} (h : IsPeriodicAnisotropicPair u e) :
    (∫ x : Torus3, ‖periodicStrainAction u e x‖ ^ 2) ^ 2 ≤
      (∫ x : Torus3,
        ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2) ^ 2 / 8 +
      5832 * (∫ x : Torus3,
        ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x) ^ 2 :=
  integral_periodicStrainAction_sq_sq_le_cross_curl_add_mixed
    u e h.velocitySlices h.directionSlices h.firstDerivativeSlices
    h.mixedIntegrable h.errorIntegrable h.divergenceIntegrable
    h.differentiatedDivergence h.unitDirection h.crossIntegrable h.densityIntegrable

/-- Galilean-invariant form of the anisotropic bound.  The strain and curl are unchanged by a
spatially constant frame velocity `a`, while the sharp direction error only pays the centered
amplitude `‖u - a‖`. -/
theorem IsPeriodicAnisotropicPair.strain_fourth_le_centered
    {u e : Torus3 → Vec3} (a : Vec3)
    (h : IsPeriodicAnisotropicPair (centeredVelocity u a) e) :
    (∫ x : Torus3, ‖periodicStrainAction u e x‖ ^ 2) ^ 2 ≤
      (∫ x : Torus3,
        ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2) ^ 2 / 8 +
      5832 * (∫ x : Torus3,
        ‖u x - a‖ * periodicGradientL1 u x * periodicGradientL1 e x) ^ 2 := by
  simpa using h.strain_fourth_le

/-- Spatial directional-strain fourth power at one time. -/
def periodicStrainFourthAt (u e : Torus3 → Vec3) : ℝ :=
  (∫ x : Torus3, ‖periodicStrainAction u e x‖ ^ 2) ^ 2

/-- Spatial transverse-vorticity fourth power at one time. -/
def periodicCrossCurlFourthAt (u e : Torus3 → Vec3) : ℝ :=
  (∫ x : Torus3,
    ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2) ^ 2

/-- Square of the still-sharp spatial direction-gradient debit at one time. -/
def periodicDirectionMixedSqAt (u e : Torus3 → Vec3) : ℝ :=
  (∫ x : Torus3,
    ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x) ^ 2

/-- Galilean-invariant square of the direction-gradient debit. -/
def periodicCenteredDirectionMixedSqAt
    (u e : Torus3 → Vec3) (a : Vec3) : ℝ :=
  (∫ x : Torus3,
    ‖u x - a‖ * periodicGradientL1 u x * periodicGradientL1 e x) ^ 2

/-- Time-integrated anisotropic handoff.  For an explicitly supplied admissible pair at every
time, integrability of the transverse-vorticity fourth power and the sharp mixed debit implies
integrability of the directional-strain fourth power.  No solution or selector is inferred. -/
theorem integrable_periodicStrainFourth_of_crossCurl_and_directionMixed
    {τ : Type*} [MeasurableSpace τ] (μ : Measure τ)
    (u e : τ → Torus3 → Vec3)
    (hpair : ∀ t : τ, IsPeriodicAnisotropicPair (u t) (e t))
    (hstrainMeasurable : AEStronglyMeasurable
      (fun t => periodicStrainFourthAt (u t) (e t)) μ)
    (hcross : Integrable (fun t => periodicCrossCurlFourthAt (u t) (e t)) μ)
    (hmixed : Integrable (fun t => periodicDirectionMixedSqAt (u t) (e t)) μ) :
    Integrable (fun t => periodicStrainFourthAt (u t) (e t)) μ := by
  have hright : Integrable (fun t =>
      (8 : ℝ)⁻¹ * periodicCrossCurlFourthAt (u t) (e t) +
        5832 * periodicDirectionMixedSqAt (u t) (e t)) μ :=
    (hcross.const_mul (8 : ℝ)⁻¹).add (hmixed.const_mul 5832)
  apply hright.mono_nonneg hstrainMeasurable
  · exact Eventually.of_forall fun t => by
      exact sq_nonneg _
  · exact Eventually.of_forall fun t => by
      have h := (hpair t).strain_fourth_le
      dsimp [periodicStrainFourthAt, periodicCrossCurlFourthAt,
        periodicDirectionMixedSqAt] at h ⊢
      nlinarith

/-- Time-integrated Galilean-invariant handoff.  The frame velocity may vary with time but is
spatially constant, so only the centered mixed debit changes. -/
theorem integrable_periodicStrainFourth_of_crossCurl_and_centeredDirectionMixed
    {τ : Type*} [MeasurableSpace τ] (μ : Measure τ)
    (u e : τ → Torus3 → Vec3) (a : τ → Vec3)
    (hpair : ∀ t : τ, IsPeriodicAnisotropicPair (centeredVelocity (u t) (a t)) (e t))
    (hstrainMeasurable : AEStronglyMeasurable
      (fun t => periodicStrainFourthAt (u t) (e t)) μ)
    (hcross : Integrable (fun t => periodicCrossCurlFourthAt (u t) (e t)) μ)
    (hmixed : Integrable
      (fun t => periodicCenteredDirectionMixedSqAt (u t) (e t) (a t)) μ) :
    Integrable (fun t => periodicStrainFourthAt (u t) (e t)) μ := by
  have hstrainMeasurable' : AEStronglyMeasurable
      (fun t => periodicStrainFourthAt (centeredVelocity (u t) (a t)) (e t)) μ := by
    simpa [periodicStrainFourthAt] using hstrainMeasurable
  have hcross' : Integrable
      (fun t => periodicCrossCurlFourthAt (centeredVelocity (u t) (a t)) (e t)) μ := by
    simpa [periodicCrossCurlFourthAt] using hcross
  have hmixed' : Integrable
      (fun t => periodicDirectionMixedSqAt
        (centeredVelocity (u t) (a t)) (e t)) μ := by
    simpa [periodicDirectionMixedSqAt, periodicCenteredDirectionMixedSqAt] using hmixed
  have h := integrable_periodicStrainFourth_of_crossCurl_and_directionMixed
    μ (fun t => centeredVelocity (u t) (a t)) e hpair
      hstrainMeasurable' hcross' hmixed'
  simpa [periodicStrainFourthAt] using h
