import NSFormal.PeriodicIntegration

/-!
# Periodic variable-direction integration identity

This file assembles the componentwise Haar integration-by-parts theorem into the exact mixed
gradient identity used by the variable-direction anisotropic regularity ledger.  The only
divergence input is displayed explicitly as the differentiated-divergence sum; no direction
field or Navier--Stokes solution is postulated.
-/

open Filter Function MeasureTheory Set

noncomputable section

/-- Entry `∂ᵢ vⱼ` of the coordinate derivative of a torus vector field. -/
def periodicFirstDerivative
    (v : Torus3 → Vec3) (i j : Fin 3) (x : Torus3) : ℝ :=
  torusCoordinateDerivative (fun y => v y j) i x

/-- Entry `∂ᵢ∂ₖ vⱼ` of the iterated coordinate derivative. -/
def periodicSecondDerivative
    (v : Torus3 → Vec3) (i k j : Fin 3) (x : Torus3) : ℝ :=
  torusCoordinateDerivative (fun y => periodicFirstDerivative v k j y) i x

/-- Coordinate `ℓ¹` envelope of the spatial derivative.  In fixed dimension it is equivalent
to the Frobenius norm, while making every component domination completely explicit. -/
def periodicGradientL1 (v : Torus3 → Vec3) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, |periodicFirstDerivative v i j x|

theorem periodicGradientL1_nonneg (v : Torus3 → Vec3) (x : Torus3) :
    0 ≤ periodicGradientL1 v x := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_periodicFirstDerivative_le_gradientL1
    (v : Torus3 → Vec3) (i j : Fin 3) (x : Torus3) :
    |periodicFirstDerivative v i j x| ≤ periodicGradientL1 v x := by
  unfold periodicGradientL1
  calc
    |periodicFirstDerivative v i j x| ≤
        ∑ b : Fin 3, |periodicFirstDerivative v i b x| :=
      Finset.single_le_sum
        (f := fun b : Fin 3 => |periodicFirstDerivative v i b x|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, |periodicFirstDerivative v a b x| :=
      Finset.single_le_sum (f := fun a : Fin 3 =>
        ∑ b : Fin 3, |periodicFirstDerivative v a b x|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- Component integrand of
`⟨(∇u)e, (∇u)ᵀe⟩`. -/
def anisotropicMixedIntegrand
    (u e : Torus3 → Vec3) (i j k : Fin 3) (x : Torus3) : ℝ :=
  periodicFirstDerivative u i j x *
    ((e x j * periodicFirstDerivative u k i x) * e x k)

/-- The two terms in which integration by parts differentiates the selected direction. -/
def anisotropicDirectionErrorIntegrand
    (u e : Torus3 → Vec3) (i j k : Fin 3) (x : Torus3) : ℝ :=
  u x j *
    (((periodicFirstDerivative e i j x * periodicFirstDerivative u k i x) * e x k) +
      ((e x j * periodicFirstDerivative u k i x) * periodicFirstDerivative e i k x))

/-- The middle integration-by-parts term, cancelled after summing `i` by differentiated
incompressibility. -/
def anisotropicDivergenceIntegrand
    (u e : Torus3 → Vec3) (i j k : Fin 3) (x : Torus3) : ℝ :=
  u x j * ((e x j * periodicSecondDerivative u i k i x) * e x k)

/-- Full periodic variable-direction identity.  The mixed gradient pairing equals minus the
two explicit direction-derivative errors.  The second-derivative middle term is not discarded:
it is cancelled by the stated differentiated-incompressibility hypothesis. -/
theorem torus3_anisotropic_mixed_pairing_eq_direction_error
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
      ∑ i : Fin 3, periodicSecondDerivative u i k i x = 0) :
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      ∫ x : Torus3, anisotropicMixedIntegrand u e i j k x) =
      -(∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x) := by
  have hcomponent : ∀ i j k : Fin 3,
      (∫ x : Torus3, anisotropicMixedIntegrand u e i j k x) =
        -(∫ x : Torus3,
          anisotropicDirectionErrorIntegrand u e i j k x +
            anisotropicDivergenceIntegrand u e i j k x) := by
    intro i j k
    let f : Torus3 → ℝ := fun x => u x j
    let a : Torus3 → ℝ := fun x => e x j
    let b : Torus3 → ℝ := fun x => periodicFirstDerivative u k i x
    let c : Torus3 → ℝ := fun x => e x k
    have hright : Integrable (fun x : Torus3 => f x *
        (((torusCoordinateDerivative a i x * b x) * c x +
          (a x * torusCoordinateDerivative b i x) * c x +
            (a x * b x) * torusCoordinateDerivative c i x))) := by
      have hsum := (herror i j k).add (hmiddle i j k)
      apply hsum.congr
      filter_upwards with x
      change anisotropicDirectionErrorIntegrand u e i j k x +
        anisotropicDivergenceIntegrand u e i j k x = _
      simp only [f, a, b, c, anisotropicDirectionErrorIntegrand,
        anisotropicDivergenceIntegrand, periodicSecondDerivative,
        periodicFirstDerivative]
      ring
    have hleft' : Integrable (fun x : Torus3 =>
        torusCoordinateDerivative f i x * ((a x * b x) * c x)) := by
      apply (hleft i j k).congr
      filter_upwards with x
      simp only [f, a, b, c, anisotropicMixedIntegrand,
        periodicFirstDerivative]
    have hparts := torus3_integral_coordinateDerivative_mul_three_eq_neg
      f a b c i (hu i j) (he i j) (huFirst i k i) (he i k)
      hleft' hright
    calc
      (∫ x : Torus3, anisotropicMixedIntegrand u e i j k x) =
          (∫ x : Torus3,
            torusCoordinateDerivative f i x * ((a x * b x) * c x)) := by rfl
      _ = -(∫ x : Torus3, f x *
          (((torusCoordinateDerivative a i x * b x) * c x +
            (a x * torusCoordinateDerivative b i x) * c x +
              (a x * b x) * torusCoordinateDerivative c i x))) := hparts
      _ = -(∫ x : Torus3,
          anisotropicDirectionErrorIntegrand u e i j k x +
            anisotropicDivergenceIntegrand u e i j k x) := by
        congr 2
        funext x
        simp only [f, a, b, c, anisotropicDirectionErrorIntegrand,
          anisotropicDivergenceIntegrand, periodicSecondDerivative,
          periodicFirstDerivative]
        ring
  have hmiddleJK : ∀ j k : Fin 3,
      (∑ i : Fin 3,
        ∫ x : Torus3, anisotropicDivergenceIntegrand u e i j k x) = 0 := by
    intro j k
    calc
      (∑ i : Fin 3,
          ∫ x : Torus3, anisotropicDivergenceIntegrand u e i j k x) =
          ∫ x : Torus3,
            ∑ i : Fin 3, anisotropicDivergenceIntegrand u e i j k x := by
        exact (MeasureTheory.integral_finsetSum Finset.univ
          (fun i _hi => hmiddle i j k)).symm
      _ = 0 := by
        have hzero : (fun x : Torus3 =>
            ∑ i : Fin 3, anisotropicDivergenceIntegrand u e i j k x) = 0 := by
          funext x
          calc
            (∑ i : Fin 3, anisotropicDivergenceIntegrand u e i j k x) =
                (u x j * e x j * e x k) *
                  (∑ i : Fin 3, periodicSecondDerivative u i k i x) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _hi
              simp only [anisotropicDivergenceIntegrand]
              ring
            _ = 0 := by rw [hdiv x k, mul_zero]
        rw [hzero]
        simp
  calc
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, anisotropicMixedIntegrand u e i j k x) =
        ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          -(∫ x : Torus3,
            anisotropicDirectionErrorIntegrand u e i j k x +
              anisotropicDivergenceIntegrand u e i j k x) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcomponent i j k
    _ = -(∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3,
          anisotropicDirectionErrorIntegrand u e i j k x +
            anisotropicDivergenceIntegrand u e i j k x) := by
      simp only [Finset.sum_neg_distrib]
    _ = -(∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ((∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x) +
          (∫ x : Torus3, anisotropicDivergenceIntegrand u e i j k x))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro i _hi
      exact MeasureTheory.integral_add (herror i j k) (hmiddle i j k)
    _ = -(∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x) := by
      simp only [Finset.sum_add_distrib]
      simp_rw [hmiddleJK]
      simp

/-- Pointwise component estimate for the two direction-gradient errors.  Coordinate envelopes
for `u`, `∇u`, and `∇e`, together with unit-coordinate bounds for `e`, give the exact factor
`2` before the finite `3³` summation. -/
theorem abs_anisotropicDirectionErrorIntegrand_le
    (u e : Torus3 → Vec3) (i j k : Fin 3) (x : Torus3)
    (uMag gradUMag gradEMag : ℝ)
    (huMag0 : 0 ≤ uMag) (hgradUMag0 : 0 ≤ gradUMag) (hgradEMag0 : 0 ≤ gradEMag)
    (hu : |u x j| ≤ uMag)
    (hgradU : |periodicFirstDerivative u k i x| ≤ gradUMag)
    (hgradEj : |periodicFirstDerivative e i j x| ≤ gradEMag)
    (hgradEk : |periodicFirstDerivative e i k x| ≤ gradEMag)
    (hej : |e x j| ≤ 1) (hek : |e x k| ≤ 1) :
    |anisotropicDirectionErrorIntegrand u e i j k x| ≤
      2 * uMag * gradUMag * gradEMag := by
  rw [anisotropicDirectionErrorIntegrand, abs_mul]
  calc
    |u x j| *
        |(periodicFirstDerivative e i j x * periodicFirstDerivative u k i x) * e x k +
          (e x j * periodicFirstDerivative u k i x) * periodicFirstDerivative e i k x| ≤
        |u x j| *
          (|(periodicFirstDerivative e i j x * periodicFirstDerivative u k i x) * e x k| +
            |(e x j * periodicFirstDerivative u k i x) *
              periodicFirstDerivative e i k x|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |u x j| *
          ((|periodicFirstDerivative e i j x| *
              |periodicFirstDerivative u k i x|) * |e x k| +
            (|e x j| * |periodicFirstDerivative u k i x|) *
              |periodicFirstDerivative e i k x|) := by
      simp only [abs_mul]
    _ ≤ uMag * ((gradEMag * gradUMag) * 1 +
          (1 * gradUMag) * gradEMag) := by
      gcongr
    _ = 2 * uMag * gradUMag * gradEMag := by ring

/-- Concrete specialization of the component estimate to the Euclidean velocity norm and the
coordinate `ℓ¹` gradient envelopes. -/
theorem abs_anisotropicDirectionErrorIntegrand_le_gradientL1
    (u e : Torus3 → Vec3) (i j k : Fin 3) (x : Torus3)
    (hunit : ‖e x‖ = 1) :
    |anisotropicDirectionErrorIntegrand u e i j k x| ≤
      2 * ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x := by
  apply abs_anisotropicDirectionErrorIntegrand_le u e i j k x
      ‖u x‖ (periodicGradientL1 u x) (periodicGradientL1 e x)
  · exact norm_nonneg _
  · exact periodicGradientL1_nonneg u x
  · exact periodicGradientL1_nonneg e x
  · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (u x) j
  · exact abs_periodicFirstDerivative_le_gradientL1 u k i x
  · exact abs_periodicFirstDerivative_le_gradientL1 e i j x
  · exact abs_periodicFirstDerivative_le_gradientL1 e i k x
  · simpa only [Real.norm_eq_abs, hunit] using PiLp.norm_apply_le (e x) j
  · simpa only [Real.norm_eq_abs, hunit] using PiLp.norm_apply_le (e x) k

/-- The exact finite-index constant in the remaining direction error.  If each of the two
component products is bounded together by `2 * density`, then the `3³` coordinate terms cost
at most `54 * ∫ density`.  This is the measure-theoretic counting step behind the mixed error
`𝒜ₑ = ∫ |u| |∇u| |∇e|`. -/
theorem abs_anisotropic_direction_error_sum_le
    (u e : Torus3 → Vec3) (density : Torus3 → ℝ)
    (hdensity : Integrable density)
    (hpoint : ∀ (i j k : Fin 3) (x : Torus3),
      |anisotropicDirectionErrorIntegrand u e i j k x| ≤ 2 * density x) :
    |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x| ≤
      54 * ∫ x : Torus3, density x := by
  have hcomponent : ∀ i j k : Fin 3,
      |∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x| ≤
        2 * ∫ x : Torus3, density x := by
    intro i j k
    have h := norm_integral_le_of_norm_le
      (f := anisotropicDirectionErrorIntegrand u e i j k)
      (g := fun x => 2 * density x) (hdensity.const_mul 2)
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hpoint i j k x)
    simpa only [Real.norm_eq_abs, MeasureTheory.integral_const_mul] using h
  calc
    |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x| ≤
        ∑ j : Fin 3, |∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, |∑ i : Fin 3,
          ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x| := by
      apply Finset.sum_le_sum
      intro j _hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          |∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x| := by
      apply Finset.sum_le_sum
      intro j _hj
      apply Finset.sum_le_sum
      intro k _hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ∑ _i : Fin 3,
          (2 * ∫ x : Torus3, density x) := by
      apply Finset.sum_le_sum
      intro j _hj
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro i _hi
      exact hcomponent i j k
    _ = 54 * ∫ x : Torus3, density x := by
      norm_num [Fin.sum_univ_succ]
      ring

/-- Fully concrete `ℓ¹`-gradient form of the periodic mixed error bound. -/
theorem abs_anisotropic_direction_error_sum_le_gradientL1
    (u e : Torus3 → Vec3)
    (hunit : ∀ x : Torus3, ‖e x‖ = 1)
    (hintegrable : Integrable (fun x : Torus3 =>
      ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x)) :
    |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      ∫ x : Torus3, anisotropicDirectionErrorIntegrand u e i j k x| ≤
      54 * ∫ x : Torus3,
        ‖u x‖ * periodicGradientL1 u x * periodicGradientL1 e x := by
  apply abs_anisotropic_direction_error_sum_le u e _ hintegrable
  intro i j k x
  simpa only [mul_assoc] using
    abs_anisotropicDirectionErrorIntegrand_le_gradientL1 u e i j k x (hunit x)
