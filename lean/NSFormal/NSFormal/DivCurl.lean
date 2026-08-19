import NSFormal.Enstrophy

/-!
# Periodic div--curl energy identity

This file proves on the concrete measured three-torus that the full velocity-gradient
energy equals curl energy for a divergence-free field.  The differentiated-divergence
condition and every Fubini/integrability input are explicit; no abstract spatial domain or
hypothesized solution is introduced.
-/

open Filter Function MeasureTheory Set

noncomputable section

/-- Frobenius contraction of a gradient with its transpose,
`Σᵢⱼ (∂ᵢuⱼ)(∂ⱼuᵢ)`. -/
def periodicGradientTransposeContraction
    (u : Torus3 → Vec3) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    periodicFirstDerivative u i j x * periodicFirstDerivative u j i x

/-- Integrated Frobenius energy of the concrete coordinate gradient. -/
def torusGradientEnergy (u : Torus3 → Vec3) : ℝ :=
  ∫ x : Torus3, periodicGradientFrobeniusSq u x

/-- Integrated squared magnitude of a concrete torus vector field. -/
def torusVectorSecondMoment (w : Torus3 → Vec3) : ℝ :=
  ∫ x : Torus3, ‖w x‖ ^ 2

theorem torusGradientEnergy_nonneg (u : Torus3 → Vec3) :
    0 ≤ torusGradientEnergy u :=
  integral_nonneg fun x => periodicGradientFrobeniusSq_nonneg u x

theorem torusVectorSecondMoment_nonneg (w : Torus3 → Vec3) :
    0 ≤ torusVectorSecondMoment w :=
  integral_nonneg fun _ => sq_nonneg _

/-- Differentiated incompressibility follows from pointwise incompressibility and commutation of
mixed coordinate derivatives.  This removes the corresponding free hypothesis from applications
of the div--curl identity to smooth fields. -/
theorem periodicDifferentiatedDivergence_eq_zero_of_divergence_mixed
    (u : Torus3 → Vec3)
    (hfirst : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun z => periodicFirstDerivative u k j z) i y))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0)
    (hmixed : ∀ (i k j : Fin 3) (x : Torus3),
      periodicSecondDerivative u i k j x = periodicSecondDerivative u k i j x) :
    ∀ (x : Torus3) (j : Fin 3),
      ∑ i : Fin 3, periodicSecondDerivative u i j i x = 0 := by
  intro x j
  have hdivFun :
      (fun z : Torus3 =>
        periodicFirstDerivative u 0 0 z + periodicFirstDerivative u 1 1 z +
          periodicFirstDerivative u 2 2 z) = fun _ => (0 : ℝ) := by
    funext z
    simpa [torusCoordinateDivergence, periodicFirstDerivative, Fin.sum_univ_three] using hdiv z
  have hzero := congrArg
    (fun q : Torus3 → ℝ => torusCoordinateDerivative q j x) hdivFun
  rw [torusCoordinateDerivative_add
      (fun z => periodicFirstDerivative u 0 0 z + periodicFirstDerivative u 1 1 z)
      (fun z => periodicFirstDerivative u 2 2 z) j x
      ((hfirst j 0 0 _).add (hfirst j 1 1 _)) (hfirst j 2 2 _),
    torusCoordinateDerivative_add
      (fun z => periodicFirstDerivative u 0 0 z)
      (fun z => periodicFirstDerivative u 1 1 z) j x
      (hfirst j 0 0 _) (hfirst j 1 1 _),
    torusCoordinateDerivative_const] at hzero
  change periodicSecondDerivative u j 0 0 x + periodicSecondDerivative u j 1 1 x +
      periodicSecondDerivative u j 2 2 x = 0 at hzero
  simpa only [Fin.sum_univ_three, hmixed 0 j 0 x, hmixed 1 j 1 x,
    hmixed 2 j 2 x] using hzero

/-- Pointwise three-dimensional algebra behind the div--curl identity. -/
theorem periodicGradientFrobeniusSq_eq_curl_sq_add_transposeContraction
    (u : Torus3 → Vec3) (x : Torus3) :
    periodicGradientFrobeniusSq u x =
      ‖periodicCoordinateCurl u x‖ ^ 2 +
        periodicGradientTransposeContraction u x := by
  simp [periodicGradientFrobeniusSq,
    periodicGradientTransposeContraction, periodicCoordinateCurl,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring

/-- One integration-by-parts component of the transpose contraction. -/
theorem integral_periodicFirstDerivative_mul_transpose_eq_neg_second
    (u : Torus3 → Vec3) (i j : Fin 3)
    (hu : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (huFirst : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun x => periodicFirstDerivative u j i x) i y))
    (hleft : Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x * periodicFirstDerivative u j i x))
    (hright : Integrable (fun x : Torus3 =>
      u x j * periodicSecondDerivative u i j i x)) :
    (∫ x : Torus3,
      periodicFirstDerivative u i j x * periodicFirstDerivative u j i x) =
      -(∫ x : Torus3, u x j * periodicSecondDerivative u i j i x) := by
  have hparts := torus3_integral_mul_coordinateDerivative_eq_neg
    (fun x : Torus3 => u x j)
    (fun x : Torus3 => periodicFirstDerivative u j i x) i
    hu huFirst hright hleft
  have hleftDef : (fun x : Torus3 =>
      torusCoordinateDerivative (fun y => u y j) i x *
        periodicFirstDerivative u j i x) =
      fun x => periodicFirstDerivative u i j x *
        periodicFirstDerivative u j i x := by
    rfl
  have hrightDef : (fun x : Torus3 =>
      u x j * torusCoordinateDerivative
        (fun y => periodicFirstDerivative u j i y) i x) =
      fun x => u x j * periodicSecondDerivative u i j i x := by
    rfl
  rw [hleftDef, hrightDef] at hparts
  linarith

/-- Summed transpose contraction vanishes after periodic integration when the displayed
differentiated-divergence identity holds. -/
theorem integral_periodicGradientTransposeContraction_eq_zero
    (u : Torus3 → Vec3)
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (huFirst : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun x => periodicFirstDerivative u j i x) i y))
    (hcross : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x * periodicFirstDerivative u j i x))
    (hsecond : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      u x j * periodicSecondDerivative u i j i x))
    (hdifferentiatedDiv : ∀ (x : Torus3) (j : Fin 3),
      ∑ i : Fin 3, periodicSecondDerivative u i j i x = 0) :
    (∫ x : Torus3, periodicGradientTransposeContraction u x) = 0 := by
  have hcomponent : ∀ i j : Fin 3,
      (∫ x : Torus3,
        periodicFirstDerivative u i j x * periodicFirstDerivative u j i x) =
        -(∫ x : Torus3, u x j * periodicSecondDerivative u i j i x) :=
    fun i j => integral_periodicFirstDerivative_mul_transpose_eq_neg_second
      u i j (hu i j) (huFirst i j) (hcross i j) (hsecond i j)
  have hcrossIntegrable : Integrable
      (periodicGradientTransposeContraction u) := by
    unfold periodicGradientTransposeContraction
    exact integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hcross i j
  calc
    (∫ x : Torus3, periodicGradientTransposeContraction u x) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x : Torus3,
            periodicFirstDerivative u i j x * periodicFirstDerivative u j i x := by
      unfold periodicGradientTransposeContraction
      rw [MeasureTheory.integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _hi
        rw [MeasureTheory.integral_finsetSum Finset.univ]
        exact fun j _hj => hcross i j
      · exact fun i _hi => integrable_finsetSum Finset.univ fun j _hj => hcross i j
    _ = -∑ j : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, u x j * periodicSecondDerivative u i j i x := by
      simp_rw [hcomponent]
      rw [Finset.sum_comm]
      simp only [Finset.sum_neg_distrib]
    _ = -∑ j : Fin 3, ∫ x : Torus3,
          ∑ i : Fin 3, u x j * periodicSecondDerivative u i j i x := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      rw [MeasureTheory.integral_finsetSum Finset.univ]
      exact fun i _hi => hsecond i j
    _ = 0 := by
      have hzero : ∀ j : Fin 3,
          (fun x : Torus3 =>
            ∑ i : Fin 3, u x j * periodicSecondDerivative u i j i x) =
            (fun _ : Torus3 => (0 : ℝ)) := by
        intro j
        funext x
        rw [← Finset.mul_sum, hdifferentiatedDiv x j, mul_zero]
      simp_rw [hzero]
      simp

/-- Concrete periodic div--curl energy identity in the divergence-free case. -/
theorem integral_periodicGradientFrobeniusSq_eq_curl_sq
    (u : Torus3 → Vec3)
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (huFirst : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun x => periodicFirstDerivative u j i x) i y))
    (hcross : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x * periodicFirstDerivative u j i x))
    (hsecond : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      u x j * periodicSecondDerivative u i j i x))
    (hdifferentiatedDiv : ∀ (x : Torus3) (j : Fin 3),
      ∑ i : Fin 3, periodicSecondDerivative u i j i x = 0)
    (hcurl : Integrable (fun x : Torus3 => ‖periodicCoordinateCurl u x‖ ^ 2)) :
    (∫ x : Torus3, periodicGradientFrobeniusSq u x) =
      ∫ x : Torus3, ‖periodicCoordinateCurl u x‖ ^ 2 := by
  have htranspose : Integrable (periodicGradientTransposeContraction u) := by
    unfold periodicGradientTransposeContraction
    exact integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hcross i j
  have hpoint : periodicGradientFrobeniusSq u =
      fun x => ‖periodicCoordinateCurl u x‖ ^ 2 +
        periodicGradientTransposeContraction u x := by
    funext x
    exact periodicGradientFrobeniusSq_eq_curl_sq_add_transposeContraction u x
  rw [hpoint, MeasureTheory.integral_add hcurl htranspose,
    integral_periodicGradientTransposeContraction_eq_zero
      u hu huFirst hcross hsecond hdifferentiatedDiv, add_zero]

/-- Div--curl energy identity with differentiated incompressibility derived from ordinary
incompressibility and mixed-partial commutation. -/
theorem integral_periodicGradientFrobeniusSq_eq_curl_sq_of_divergence_mixed
    (u : Torus3 → Vec3)
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
    (∫ x : Torus3, periodicGradientFrobeniusSq u x) =
      ∫ x : Torus3, ‖periodicCoordinateCurl u x‖ ^ 2 := by
  apply integral_periodicGradientFrobeniusSq_eq_curl_sq u hu
    (fun i j y => hfirst i j i y) hcross hsecond
  · exact periodicDifferentiatedDivergence_eq_zero_of_divergence_mixed
      u hfirst hdiv hmixed
  · exact hcurl

/-- Coordinate curl agrees with the Fréchet-derivative curl used by the classical PDE
interface. -/
theorem periodicCoordinateCurl_eq_torusCurl
    (u : C(Torus3, Vec3)) (x : Torus3)
    (huLift : ContDiff ℝ 1 (torusLift u)) :
    periodicCoordinateCurl u x = torusCurl u x := by
  unfold periodicCoordinateCurl torusCurl
  have hcomponent : ∀ i j : Fin 3,
      periodicFirstDerivative u i j x = torusPartial u x i j := by
    intro i j
    exact torusCoordinateDerivative_component_eq_torusPartial u i j x huLift
  simp_rw [hcomponent]

/-- For a concrete curl field, the periodic div--curl identity identifies velocity-gradient
energy with the vorticity second moment. -/
theorem torusGradientEnergy_eq_torusVectorSecondMoment_of_curl
    (u w : C(Torus3, Vec3))
    (huLift : ContDiff ℝ 1 (torusLift u))
    (hw : ∀ x : Torus3, w x = torusCurl u x)
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (huFirst : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun x => periodicFirstDerivative u j i x) i y))
    (hcross : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x * periodicFirstDerivative u j i x))
    (hsecond : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      u x j * periodicSecondDerivative u i j i x))
    (hdifferentiatedDiv : ∀ (x : Torus3) (j : Fin 3),
      ∑ i : Fin 3, periodicSecondDerivative u i j i x = 0)
    (hcurl : Integrable (fun x : Torus3 => ‖periodicCoordinateCurl u x‖ ^ 2)) :
    torusGradientEnergy u = torusVectorSecondMoment w := by
  unfold torusGradientEnergy torusVectorSecondMoment
  rw [integral_periodicGradientFrobeniusSq_eq_curl_sq
    u hu huFirst hcross hsecond hdifferentiatedDiv hcurl]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change ‖periodicCoordinateCurl u x‖ ^ 2 = ‖w x‖ ^ 2
    rw [periodicCoordinateCurl_eq_torusCurl u x huLift, ← hw x]

/-- Application-ready div--curl identity: only ordinary incompressibility and mixed-partial
commutation are required. -/
theorem torusGradientEnergy_eq_torusVectorSecondMoment_of_curl_divergence_mixed
    (u w : C(Torus3, Vec3))
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
    torusGradientEnergy u = torusVectorSecondMoment w := by
  unfold torusGradientEnergy torusVectorSecondMoment
  rw [integral_periodicGradientFrobeniusSq_eq_curl_sq_of_divergence_mixed
    u hu hfirst hcross hsecond hdiv hmixed hcurl]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change ‖periodicCoordinateCurl u x‖ ^ 2 = ‖w x‖ ^ 2
    rw [periodicCoordinateCurl_eq_torusCurl u x huLift, ← hw x]
