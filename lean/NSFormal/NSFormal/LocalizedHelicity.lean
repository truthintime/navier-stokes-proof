import NSFormal.ConcreteDynamicCriterion

/-!
# A nondegenerate localized-helicity witness

This file constructs explicit smooth periodic fields for which the localized
helicity gap is genuinely stronger than ordinary helicity.  The vorticity is
the actual curl of the displayed velocity, is divergence free and nowhere
zero, has a nonconstant exact first integral, and has strictly positive
self-transport quotient.  Ordinary helicity cancels, whereas first-integral
weighted helicity is positive; consequently the concrete stretching Cauchy
defect is strictly positive.
-/

open Filter Function MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

def torusSinCoordinate (j : Fin 3) : C(Torus3, ℝ) :=
  ⟨fun x => Real.sin_periodic.lift (x j),
    Real.continuous_sin.quotient_liftOn' _ |>.comp (continuous_apply j)⟩

def torusCosCoordinate (j : Fin 3) : C(Torus3, ℝ) :=
  ⟨fun x => Real.cos_periodic.lift (x j),
    Real.continuous_cos.quotient_liftOn' _ |>.comp (continuous_apply j)⟩

theorem torusCoordinateDerivative_sinCoordinate (i j : Fin 3) (x : Torus3) :
    torusCoordinateDerivative (torusSinCoordinate j) i x =
      if i = j then torusCosCoordinate j x else 0 := by
  induction j using i.succAboveCases
  ·
    rw [if_pos rfl]
    unfold torusCoordinateDerivative torusCoordinateSliceDerivative
    have hslice :
        torusCoordinateSliceLift (torusSinCoordinate i) i (Fin.removeNth i x) = Real.sin := by
      funext r
      change Real.sin_periodic.lift
        (i.insertNth (r : AddCircle ((2 : ℝ) * Real.pi)) (Fin.removeNth i x) i) =
          Real.sin r
      rw [Fin.insertNth_apply_same, Real.sin_periodic.lift_coe]
    rw [hslice, Real.deriv_sin]
    change Real.cos (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 _).1 = _
    rw [← Real.cos_periodic.lift_coe, AddCircle.coe_equivIoc]
    rfl
  · rename_i k
    have hij : i ≠ i.succAbove k := (Fin.succAbove_ne i k).symm
    unfold torusCoordinateDerivative torusCoordinateSliceDerivative
    rw [if_neg hij]
    have hslice :
        torusCoordinateSliceLift (torusSinCoordinate (i.succAbove k)) i (Fin.removeNth i x) =
          fun _ : ℝ => torusSinCoordinate (i.succAbove k) x := by
      funext r
      change Real.sin_periodic.lift
        (i.insertNth (r : AddCircle ((2 : ℝ) * Real.pi))
          (Fin.removeNth i x) (i.succAbove k)) =
            Real.sin_periodic.lift (x (i.succAbove k))
      rw [Fin.insertNth_apply_succAbove]
      rfl
    rw [hslice, deriv_const']
    rfl

theorem torusCoordinateDerivative_cosCoordinate (i j : Fin 3) (x : Torus3) :
    torusCoordinateDerivative (torusCosCoordinate j) i x =
      if i = j then -torusSinCoordinate j x else 0 := by
  induction j using i.succAboveCases
  ·
    rw [if_pos rfl]
    unfold torusCoordinateDerivative torusCoordinateSliceDerivative
    have hslice :
        torusCoordinateSliceLift (torusCosCoordinate i) i (Fin.removeNth i x) = Real.cos := by
      funext r
      change Real.cos_periodic.lift
        (i.insertNth (r : AddCircle ((2 : ℝ) * Real.pi)) (Fin.removeNth i x) i) =
          Real.cos r
      rw [Fin.insertNth_apply_same, Real.cos_periodic.lift_coe]
    rw [hslice, Real.deriv_cos']
    change -Real.sin (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 _).1 = _
    rw [← Real.sin_periodic.lift_coe, AddCircle.coe_equivIoc]
    rfl
  · rename_i k
    have hij : i ≠ i.succAbove k := (Fin.succAbove_ne i k).symm
    unfold torusCoordinateDerivative torusCoordinateSliceDerivative
    rw [if_neg hij]
    have hslice :
        torusCoordinateSliceLift (torusCosCoordinate (i.succAbove k)) i (Fin.removeNth i x) =
          fun _ : ℝ => torusCosCoordinate (i.succAbove k) x := by
      funext r
      change Real.cos_periodic.lift
        (i.insertNth (r : AddCircle ((2 : ℝ) * Real.pi))
          (Fin.removeNth i x) (i.succAbove k)) =
            Real.cos_periodic.lift (x (i.succAbove k))
      rw [Fin.insertNth_apply_succAbove]
      rfl
    rw [hslice, deriv_const']
    rfl

def localizedHelicityVelocity : C(Torus3, Vec3) :=
  ⟨fun x => WithLp.toLp 2 ![
      1 - torusSinCoordinate 1 x * torusCosCoordinate 1 x,
      (2 : ℝ)⁻¹ * torusSinCoordinate 0 x,
      torusSinCoordinate 1 x], by
    exact (PiLp.continuous_toLp 2 _).comp (by
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop)⟩

def localizedHelicityVorticity : C(Torus3, Vec3) :=
  ⟨fun x => WithLp.toLp 2 ![
      torusCosCoordinate 1 x,
      0,
      torusCosCoordinate 1 x ^ 2 - torusSinCoordinate 1 x ^ 2 +
        (2 : ℝ)⁻¹ * torusCosCoordinate 0 x], by
    exact (PiLp.continuous_toLp 2 _).comp (by
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop)⟩

def localizedHelicityWeight : C(Torus3, ℝ) := torusCosCoordinate 1

theorem localizedHelicityVelocity_contDiff :
    ContDiff ℝ 2 (torusLift localizedHelicityVelocity) := by
  change ContDiff ℝ 2 (fun y : Vec3 => WithLp.toLp 2 ![
    1 - Real.sin (y 1) * Real.cos (y 1),
    (2 : ℝ)⁻¹ * Real.sin (y 0),
    Real.sin (y 1)])
  apply PiLp.contDiff_toLp.comp
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem localizedHelicityVorticity_contDiff :
    ContDiff ℝ 1 (torusLift localizedHelicityVorticity) := by
  change ContDiff ℝ 1 (fun y : Vec3 => WithLp.toLp 2 ![
    Real.cos (y 1),
    0,
    Real.cos (y 1) ^ 2 - Real.sin (y 1) ^ 2 +
      (2 : ℝ)⁻¹ * Real.cos (y 0)])
  apply PiLp.contDiff_toLp.comp
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem localizedHelicityWeight_contDiff :
    ContDiff ℝ 1 (torusLift localizedHelicityWeight) := by
  change ContDiff ℝ 1 (fun y : Vec3 => Real.cos (y 1))
  fun_prop

theorem torusSinCoordinate_contDiff (j : Fin 3) :
    ContDiff ℝ 1 (torusLift (torusSinCoordinate j)) := by
  change ContDiff ℝ 1 (fun y : Vec3 => Real.sin (y j))
  fun_prop

theorem torusCosCoordinate_contDiff (j : Fin 3) :
    ContDiff ℝ 1 (torusLift (torusCosCoordinate j)) := by
  change ContDiff ℝ 1 (fun y : Vec3 => Real.cos (y j))
  fun_prop

theorem localizedHelicity_oneSubSinMulCos_derivative (i : Fin 3) (x : Torus3) :
    torusCoordinateDerivative
        (fun z => 1 - torusSinCoordinate 1 z * torusCosCoordinate 1 z) i x =
      if i = 1 then -(torusCosCoordinate 1 x ^ 2 - torusSinCoordinate 1 x ^ 2) else 0 := by
  have hs := contDiff_torusCoordinateSliceLift_of_contDiff_torusLift
    (torusSinCoordinate 1) i (Fin.removeNth i x) (torusSinCoordinate_contDiff 1)
  have hc := contDiff_torusCoordinateSliceLift_of_contDiff_torusLift
    (torusCosCoordinate 1) i (Fin.removeNth i x) (torusCosCoordinate_contDiff 1)
  rw [torusCoordinateDerivative_sub
    (fun _ : Torus3 => (1 : ℝ))
    (fun z => torusSinCoordinate 1 z * torusCosCoordinate 1 z) i x
    contDiff_const (hs.mul hc)]
  rw [torusCoordinateDerivative_const]
  rw [torusCoordinateDerivative_mul (torusSinCoordinate 1) (torusCosCoordinate 1) i x hs hc]
  rw [torusCoordinateDerivative_sinCoordinate, torusCoordinateDerivative_cosCoordinate]
  by_cases hi : i = 1 <;> simp [hi] <;> ring

theorem localizedHelicity_halfSin_derivative (i : Fin 3) (x : Torus3) :
    torusCoordinateDerivative
        (fun z => (2 : ℝ)⁻¹ * torusSinCoordinate 0 z) i x =
      (2 : ℝ)⁻¹ * (if i = 0 then torusCosCoordinate 0 x else 0) := by
  have hs := contDiff_torusCoordinateSliceLift_of_contDiff_torusLift
    (torusSinCoordinate 0) i (Fin.removeNth i x) (torusSinCoordinate_contDiff 0)
  rw [torusCoordinateDerivative_mul
    (fun _ : Torus3 => (2 : ℝ)⁻¹) (torusSinCoordinate 0) i x contDiff_const hs]
  rw [torusCoordinateDerivative_const, torusCoordinateDerivative_sinCoordinate]
  ring

theorem localizedHelicityVorticity_eq_curl (x : Torus3) :
    localizedHelicityVorticity x = torusCurl localizedHelicityVelocity x := by
  rw [← periodicCoordinateCurl_eq_torusCurl localizedHelicityVelocity x
    (localizedHelicityVelocity_contDiff.of_le (by norm_num))]
  ext q
  fin_cases q <;>
    simp [periodicCoordinateCurl, periodicFirstDerivative,
      localizedHelicityVelocity, localizedHelicityVorticity,
      torusCoordinateDerivative_sinCoordinate, localizedHelicity_oneSubSinMulCos_derivative,
      localizedHelicity_halfSin_derivative] <;>
    ring

theorem localizedHelicityVorticity_divergence (x : Torus3) :
    torusCoordinateDivergence localizedHelicityVorticity x = 0 := by
  exact torusCoordinateDivergence_eq_zero_of_eq_torusCurl
    localizedHelicityVelocity localizedHelicityVorticity
    localizedHelicityVelocity_contDiff localizedHelicityVorticity_contDiff
    localizedHelicityVorticity_eq_curl x

theorem localizedHelicityWeight_firstIntegral (x : Torus3) :
    torusScalarTransport localizedHelicityVorticity localizedHelicityWeight x = 0 := by
  rw [torusScalarTransport, Fin.sum_univ_three]
  simp [localizedHelicityVorticity, localizedHelicityWeight, torusCoordinateDerivative_cosCoordinate]

theorem localizedHelicity_helicity_pointwise (x : Torus3) :
    inner ℝ (localizedHelicityVorticity x) (localizedHelicityVelocity x) =
      torusCosCoordinate 1 x - torusSinCoordinate 1 x ^ 3 +
        (2 : ℝ)⁻¹ * torusSinCoordinate 1 x * torusCosCoordinate 0 x := by
  simp [localizedHelicityVorticity, localizedHelicityVelocity,
    PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem localizedHelicity_weighted_helicity_pointwise (x : Torus3) :
    localizedHelicityWeight x *
        inner ℝ (localizedHelicityVorticity x) (localizedHelicityVelocity x) =
      torusCosCoordinate 1 x ^ 2 - torusCosCoordinate 1 x * torusSinCoordinate 1 x ^ 3 +
        (2 : ℝ)⁻¹ * torusCosCoordinate 1 x * torusSinCoordinate 1 x * torusCosCoordinate 0 x := by
  rw [localizedHelicity_helicity_pointwise]
  unfold localizedHelicityWeight
  ring

theorem torusCosCoordinate_eq_realCos_representative (j : Fin 3) (x : Torus3) :
    torusCosCoordinate j x = Real.cos
      (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x j)).1 := by
  change Real.cos_periodic.lift (x j) = _
  rw [← Real.cos_periodic.lift_coe, AddCircle.coe_equivIoc]

theorem torusSinCoordinate_eq_realSin_representative (j : Fin 3) (x : Torus3) :
    torusSinCoordinate j x = Real.sin
      (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x j)).1 := by
  change Real.sin_periodic.lift (x j) = _
  rw [← Real.sin_periodic.lift_coe, AddCircle.coe_equivIoc]

theorem torusCosSq_add_sinSq (j : Fin 3) (x : Torus3) :
    torusCosCoordinate j x ^ 2 + torusSinCoordinate j x ^ 2 = 1 := by
  rw [torusCosCoordinate_eq_realCos_representative, torusSinCoordinate_eq_realSin_representative]
  exact Real.cos_sq_add_sin_sq _

theorem localizedHelicityVorticity_ne_zero (x : Torus3) :
    localizedHelicityVorticity x ≠ 0 := by
  intro hzero
  have h0 := congrArg (fun v : Vec3 => v 0) hzero
  have h2 := congrArg (fun v : Vec3 => v 2) hzero
  simp [localizedHelicityVorticity] at h0 h2
  have hy := torusCosSq_add_sinSq 1 x
  have hx := torusCosSq_add_sinSq 0 x
  have hcosLe : torusCosCoordinate 0 x ≤ 1 := by
    nlinarith [sq_nonneg (torusSinCoordinate 0 x), sq_nonneg (torusCosCoordinate 0 x - 1)]
  nlinarith

theorem localizedHelicity_vorticityThird_derivative_zero (x : Torus3) :
    torusCoordinateDerivative
        (fun z => torusCosCoordinate 1 z ^ 2 - torusSinCoordinate 1 z ^ 2 +
          (2 : ℝ)⁻¹ * torusCosCoordinate 0 z) 0 x =
      -(2 : ℝ)⁻¹ * torusSinCoordinate 0 x := by
  unfold torusCoordinateDerivative torusCoordinateSliceDerivative
  change AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
    (deriv fun r : ℝ =>
      torusCosCoordinate 1 x ^ 2 - torusSinCoordinate 1 x ^ 2 + (2 : ℝ)⁻¹ * Real.cos r)
        (x 0) = -(2 : ℝ)⁻¹ * torusSinCoordinate 0 x
  have hderiv :
      deriv (fun r : ℝ =>
        torusCosCoordinate 1 x ^ 2 - torusSinCoordinate 1 x ^ 2 + (2 : ℝ)⁻¹ * Real.cos r) =
        fun r => -(2 : ℝ)⁻¹ * Real.sin r := by
    funext r
    let C : ℝ := torusCosCoordinate 1 x ^ 2 - torusSinCoordinate 1 x ^ 2
    have h := ((Real.hasDerivAt_cos r).mul_const (2 : ℝ)⁻¹).const_add C
    rw [show (fun s : ℝ =>
        torusCosCoordinate 1 x ^ 2 - torusSinCoordinate 1 x ^ 2 + (2 : ℝ)⁻¹ * Real.cos s) =
          fun s : ℝ => C + Real.cos s * (2 : ℝ)⁻¹ by
        funext s
        dsimp [C]
        ring]
    rw [h.deriv]
    ring
  rw [hderiv]
  change -(2 : ℝ)⁻¹ * Real.sin
      (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x 0)).1 = _
  rw [← Real.sin_periodic.lift_coe, AddCircle.coe_equivIoc]
  rfl

theorem localizedHelicity_vorticityThird_derivative_two (x : Torus3) :
    torusCoordinateDerivative
        (fun z => torusCosCoordinate 1 z ^ 2 - torusSinCoordinate 1 z ^ 2 +
          (2 : ℝ)⁻¹ * torusCosCoordinate 0 z) 2 x = 0 := by
  unfold torusCoordinateDerivative torusCoordinateSliceDerivative
  change AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
    (deriv fun _r : ℝ =>
      torusCosCoordinate 1 x ^ 2 - torusSinCoordinate 1 x ^ 2 + (2 : ℝ)⁻¹ * torusCosCoordinate 0 x)
        (x 2) = 0
  rw [deriv_const']
  rfl

theorem localizedHelicity_selfTransportVector (x : Torus3) :
    periodicVorticitySelfTransportVector localizedHelicityVorticity x =
      WithLp.toLp 2 ![0, 0,
        -(2 : ℝ)⁻¹ * torusCosCoordinate 1 x * torusSinCoordinate 0 x] := by
  ext q
  fin_cases q <;>
    simp [periodicVorticitySelfTransportVector, torusScalarTransport,
      Fin.sum_univ_three, localizedHelicityVorticity,
      torusCoordinateDerivative_cosCoordinate, localizedHelicity_vorticityThird_derivative_zero,
      localizedHelicity_vorticityThird_derivative_two, torusCoordinateDerivative_const] <;>
    ring

def localizedHelicityPoint : Torus3 := ![
  ((Real.pi / 2 : ℝ) : AddCircle ((2 : ℝ) * Real.pi)),
  0,
  0]

theorem localizedHelicity_selfTransportVector_ne_zero :
    periodicVorticitySelfTransportVector localizedHelicityVorticity
      localizedHelicityPoint ≠ 0 := by
  rw [localizedHelicity_selfTransportVector]
  intro hzero
  have h2 := congrArg (fun v : Vec3 => v 2) hzero
  change -(2 : ℝ)⁻¹ * torusCosCoordinate 1 localizedHelicityPoint *
      torusSinCoordinate 0 localizedHelicityPoint = 0 at h2
  have hc : torusCosCoordinate 1 localizedHelicityPoint = 1 := by
    change Real.cos (0 : ℝ) = 1
    norm_num
  have hs : torusSinCoordinate 0 localizedHelicityPoint = 1 := by
    change Real.sin (Real.pi / 2) = 1
    rw [Real.sin_pi_div_two]
  rw [hc, hs] at h2
  norm_num at h2

theorem localizedHelicity_quotientDensity_continuous :
    Continuous
      (periodicVorticitySelfTransportQuotientSq localizedHelicityVorticity) := by
  have hnorm : Continuous (fun x : Torus3 => ‖localizedHelicityVorticity x‖) := by
    fun_prop
  have hnormNe : ∀ x : Torus3, ‖localizedHelicityVorticity x‖ ≠ 0 := by
    intro x
    exact norm_ne_zero_iff.mpr (localizedHelicityVorticity_ne_zero x)
  have hinv : Continuous (fun x : Torus3 => ‖localizedHelicityVorticity x‖⁻¹) :=
    hnorm.inv₀ hnormNe
  have hself : Continuous
      (periodicVorticitySelfTransportVector localizedHelicityVorticity) := by
    rw [show periodicVorticitySelfTransportVector localizedHelicityVorticity =
        fun x : Torus3 => WithLp.toLp 2 ![0, 0,
          -(2 : ℝ)⁻¹ * torusCosCoordinate 1 x * torusSinCoordinate 0 x] by
      funext x
      exact localizedHelicity_selfTransportVector x]
    exact (PiLp.continuous_toLp 2 _).comp (by
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop)
  have hnormalized : Continuous
      (periodicNormalizedVorticitySelfTransportVector localizedHelicityVorticity) := by
    unfold periodicNormalizedVorticitySelfTransportVector
    exact hinv.smul hself
  have hfun :
      periodicVorticitySelfTransportQuotientSq localizedHelicityVorticity =
        fun x => ‖periodicNormalizedVorticitySelfTransportVector
          localizedHelicityVorticity x‖ ^ 2 := by
    funext x
    exact (periodicNormalizedVorticitySelfTransportVector_norm_sq
      localizedHelicityVorticity x).symm
  rw [hfun]
  fun_prop

theorem localizedHelicity_quotientDensity_pos_at_point :
    0 < periodicVorticitySelfTransportQuotientSq
      localizedHelicityVorticity localizedHelicityPoint := by
  have hwNorm : ‖localizedHelicityVorticity localizedHelicityPoint‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (localizedHelicityVorticity_ne_zero localizedHelicityPoint)
  have hnormalized :
      periodicNormalizedVorticitySelfTransportVector localizedHelicityVorticity
        localizedHelicityPoint ≠ 0 := by
    unfold periodicNormalizedVorticitySelfTransportVector
    exact smul_ne_zero (inv_ne_zero hwNorm)
      localizedHelicity_selfTransportVector_ne_zero
  rw [← periodicNormalizedVorticitySelfTransportVector_norm_sq]
  positivity

theorem localizedHelicity_selfTransportQuotient_pos :
    0 < torusVorticitySelfTransportQuotient localizedHelicityVorticity := by
  unfold torusVorticitySelfTransportQuotient
  have hcont := localizedHelicity_quotientDensity_continuous
  have hint : Integrable
      (periodicVorticitySelfTransportQuotientSq localizedHelicityVorticity) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hcont.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  exact integral_pos_of_integrable_nonneg_nonzero hcont hint
    (fun x => periodicVorticitySelfTransportQuotientSq_nonneg
      localizedHelicityVorticity x)
    localizedHelicity_quotientDensity_pos_at_point.ne'

def torusYHalfTurn : Torus3 := fun i =>
  if i = 1 then ((Real.pi : ℝ) : AddCircle ((2 : ℝ) * Real.pi)) else 0

theorem localizedHelicityWeight_nonconstant :
    localizedHelicityWeight torus3Origin ≠
      localizedHelicityWeight torusYHalfTurn := by
  have hzero : localizedHelicityWeight torus3Origin = 1 := by
    change Real.cos (0 : ℝ) = 1
    norm_num
  have hhalf : localizedHelicityWeight torusYHalfTurn = -1 := by
    change Real.cos Real.pi = -1
    exact Real.cos_pi
  rw [hzero, hhalf]
  norm_num

theorem torusSinCoordinate_one_add_yHalfTurn (x : Torus3) :
    torusSinCoordinate 1 (x + torusYHalfTurn) = -torusSinCoordinate 1 x := by
  change Real.sin_periodic.lift
      (x 1 + ((Real.pi : ℝ) : AddCircle ((2 : ℝ) * Real.pi))) =
    -Real.sin_periodic.lift (x 1)
  let q := x 1
  change Real.sin_periodic.lift
      (q + ((Real.pi : ℝ) : AddCircle ((2 : ℝ) * Real.pi))) =
    -Real.sin_periodic.lift q
  induction q using Quotient.inductionOn'
  rw [← AddCircle.coe_add]
  change Real.sin (_ + Real.pi) = -Real.sin _
  rw [Real.sin_add_pi]

theorem torusCosCoordinate_one_add_yHalfTurn (x : Torus3) :
    torusCosCoordinate 1 (x + torusYHalfTurn) = -torusCosCoordinate 1 x := by
  change Real.cos_periodic.lift
      (x 1 + ((Real.pi : ℝ) : AddCircle ((2 : ℝ) * Real.pi))) =
    -Real.cos_periodic.lift (x 1)
  let q := x 1
  change Real.cos_periodic.lift
      (q + ((Real.pi : ℝ) : AddCircle ((2 : ℝ) * Real.pi))) =
    -Real.cos_periodic.lift q
  induction q using Quotient.inductionOn'
  rw [← AddCircle.coe_add]
  change Real.cos (_ + Real.pi) = -Real.cos _
  rw [Real.cos_add_pi]

theorem torusCosCoordinate_zero_add_yHalfTurn (x : Torus3) :
    torusCosCoordinate 0 (x + torusYHalfTurn) = torusCosCoordinate 0 x := by
  change Real.cos_periodic.lift (x 0 + 0) = Real.cos_periodic.lift (x 0)
  rw [add_zero]

theorem torusSinCoordinate_neg (j : Fin 3) (x : Torus3) :
    torusSinCoordinate j (-x) = -torusSinCoordinate j x := by
  change Real.Angle.sin (-(x j)) = -Real.Angle.sin (x j)
  exact Real.Angle.sin_neg (x j)

theorem torusCosCoordinate_neg (j : Fin 3) (x : Torus3) :
    torusCosCoordinate j (-x) = torusCosCoordinate j x := by
  change Real.Angle.cos (-(x j)) = Real.Angle.cos (x j)
  exact Real.Angle.cos_neg (x j)

theorem localizedHelicity_helicity_integral_eq_zero :
    (∫ x : Torus3,
      inner ℝ (localizedHelicityVorticity x) (localizedHelicityVelocity x)) = 0 := by
  apply MeasureTheory.integral_eq_zero_of_add_right_eq_neg
    (g := torusYHalfTurn)
  intro x
  rw [localizedHelicity_helicity_pointwise, localizedHelicity_helicity_pointwise]
  rw [torusCosCoordinate_one_add_yHalfTurn, torusSinCoordinate_one_add_yHalfTurn,
    torusCosCoordinate_zero_add_yHalfTurn]
  ring

theorem torus3_integral_coordinateDerivative_eq_zero_of_contDiff
    (f : C(Torus3, ℝ)) (i : Fin 3)
    (hf : ContDiff ℝ 1 (torusLift f)) :
    (∫ x : Torus3, torusCoordinateDerivative f i x) = 0 := by
  let e : C(Torus3, Vec3) :=
    ContinuousMap.const Torus3 (EuclideanSpace.single i (1 : ℝ))
  have he : ContDiff ℝ 1 (torusLift e) := by
    change ContDiff ℝ 1
      (fun _ : Vec3 => EuclideanSpace.single i (1 : ℝ))
    fun_prop
  have hdiv : ∀ x : Torus3, torusCoordinateDivergence e x = 0 := by
    intro x
    simp [e, torusCoordinateDivergence, torusCoordinateDerivative_const]
  have hzero := integral_torusScalarTransport_eq_zero_of_contDiff
    e f he hf hdiv
  have htransport : torusScalarTransport e f = torusCoordinateDerivative f i := by
    funext x
    unfold torusScalarTransport
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro j _hj hji
      simp [e, hji]
    · simp
  rw [htransport] at hzero
  exact hzero

def localizedHelicityOddPrimitive : C(Torus3, ℝ) :=
  ⟨fun x => torusSinCoordinate 1 x ^ 4 / 4, by fun_prop⟩

def localizedHelicityCrossPrimitive : C(Torus3, ℝ) :=
  ⟨fun x => torusSinCoordinate 0 x * torusCosCoordinate 1 x * torusSinCoordinate 1 x, by fun_prop⟩

theorem localizedHelicityOddPrimitive_contDiff :
    ContDiff ℝ 1 (torusLift localizedHelicityOddPrimitive) := by
  change ContDiff ℝ 1 (fun y : Vec3 => Real.sin (y 1) ^ 4 / 4)
  fun_prop

theorem localizedHelicityCrossPrimitive_contDiff :
    ContDiff ℝ 1 (torusLift localizedHelicityCrossPrimitive) := by
  change ContDiff ℝ 1
    (fun y : Vec3 => Real.sin (y 0) * Real.cos (y 1) * Real.sin (y 1))
  fun_prop

theorem localizedHelicityOddPrimitive_derivative (x : Torus3) :
    torusCoordinateDerivative localizedHelicityOddPrimitive 1 x =
      torusCosCoordinate 1 x * torusSinCoordinate 1 x ^ 3 := by
  unfold torusCoordinateDerivative torusCoordinateSliceDerivative
  change AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
    (deriv fun r : ℝ => Real.sin r ^ 4 / 4) (x 1) =
      torusCosCoordinate 1 x * torusSinCoordinate 1 x ^ 3
  have hderiv : deriv (fun r : ℝ => Real.sin r ^ 4 / 4) =
      fun r => Real.cos r * Real.sin r ^ 3 := by
    funext r
    have hraw := ((Real.hasDerivAt_sin r).pow 4).div_const 4
    have hv := hraw.deriv
    convert hv using 1 <;> norm_num <;> ring
  rw [hderiv]
  change Real.cos (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x 1)).1 *
      Real.sin (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x 1)).1 ^ 3 = _
  rw [← Real.cos_periodic.lift_coe, ← Real.sin_periodic.lift_coe,
    AddCircle.coe_equivIoc]
  rfl

theorem localizedHelicityCrossPrimitive_derivative (x : Torus3) :
    torusCoordinateDerivative localizedHelicityCrossPrimitive 0 x =
      torusCosCoordinate 0 x * torusCosCoordinate 1 x * torusSinCoordinate 1 x := by
  unfold torusCoordinateDerivative torusCoordinateSliceDerivative
  change AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
    (deriv fun r : ℝ =>
      Real.sin r * torusCosCoordinate 1 x * torusSinCoordinate 1 x) (x 0) =
        torusCosCoordinate 0 x * torusCosCoordinate 1 x * torusSinCoordinate 1 x
  let C : ℝ := torusCosCoordinate 1 x * torusSinCoordinate 1 x
  have hderiv : deriv (fun r : ℝ => Real.sin r * C) =
      fun r => Real.cos r * C := by
    funext r
    exact ((Real.hasDerivAt_sin r).mul_const C).deriv
  rw [show (fun r : ℝ => Real.sin r * torusCosCoordinate 1 x * torusSinCoordinate 1 x) =
      fun r : ℝ => Real.sin r * C by
    funext r
    simp [C, mul_assoc]]
  rw [hderiv]
  change Real.cos (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x 0)).1 * C = _
  rw [← Real.cos_periodic.lift_coe, AddCircle.coe_equivIoc]
  change torusCosCoordinate 0 x * C = _
  dsimp [C]
  ring

theorem localizedHelicity_weighted_remainder_integral_eq_zero :
    (∫ x : Torus3,
      localizedHelicityWeight x *
          inner ℝ (localizedHelicityVorticity x) (localizedHelicityVelocity x) -
        torusCosCoordinate 1 x ^ 2) = 0 := by
  let oddTerm : Torus3 → ℝ := fun x => torusCosCoordinate 1 x * torusSinCoordinate 1 x ^ 3
  let crossTerm : Torus3 → ℝ := fun x =>
    torusCosCoordinate 0 x * torusCosCoordinate 1 x * torusSinCoordinate 1 x
  have hoddZero : (∫ x : Torus3, oddTerm x) = 0 := by
    rw [show oddTerm = torusCoordinateDerivative localizedHelicityOddPrimitive 1 by
      funext x
      exact (localizedHelicityOddPrimitive_derivative x).symm]
    exact torus3_integral_coordinateDerivative_eq_zero_of_contDiff
      localizedHelicityOddPrimitive 1 localizedHelicityOddPrimitive_contDiff
  have hcrossZero : (∫ x : Torus3, crossTerm x) = 0 := by
    rw [show crossTerm = torusCoordinateDerivative localizedHelicityCrossPrimitive 0 by
      funext x
      exact (localizedHelicityCrossPrimitive_derivative x).symm]
    exact torus3_integral_coordinateDerivative_eq_zero_of_contDiff
      localizedHelicityCrossPrimitive 0 localizedHelicityCrossPrimitive_contDiff
  have hoddInt : Integrable oddTerm := by
    have hc : Continuous oddTerm := by dsimp [oddTerm]; fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hcrossInt : Integrable crossTerm := by
    have hc : Continuous crossTerm := by dsimp [crossTerm]; fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  calc
    (∫ x : Torus3,
        localizedHelicityWeight x *
            inner ℝ (localizedHelicityVorticity x) (localizedHelicityVelocity x) -
          torusCosCoordinate 1 x ^ 2) =
        ∫ x : Torus3, -oddTerm x + (2 : ℝ)⁻¹ * crossTerm x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [oddTerm, crossTerm]
        rw [localizedHelicity_weighted_helicity_pointwise]
        ring
    _ = -(∫ x : Torus3, oddTerm x) +
        (2 : ℝ)⁻¹ * (∫ x : Torus3, crossTerm x) := by
      calc
        (∫ x : Torus3, -oddTerm x + (2 : ℝ)⁻¹ * crossTerm x) =
            (∫ x : Torus3, -oddTerm x) +
              ∫ x : Torus3, (2 : ℝ)⁻¹ * crossTerm x :=
          integral_add hoddInt.neg (hcrossInt.const_mul (2 : ℝ)⁻¹)
        _ = -(∫ x : Torus3, oddTerm x) +
            (2 : ℝ)⁻¹ * (∫ x : Torus3, crossTerm x) := by
          rw [integral_neg, integral_const_mul]
    _ = 0 := by rw [hoddZero, hcrossZero]; ring

theorem localizedHelicity_cosSq_integral_pos :
    0 < ∫ x : Torus3, torusCosCoordinate 1 x ^ 2 := by
  have hcont : Continuous (fun x : Torus3 => torusCosCoordinate 1 x ^ 2) := by fun_prop
  have hint : Integrable (fun x : Torus3 => torusCosCoordinate 1 x ^ 2) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hcont.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  apply integral_pos_of_integrable_nonneg_nonzero hcont hint
    (fun x => sq_nonneg (torusCosCoordinate 1 x))
  show torusCosCoordinate 1 torus3Origin ^ 2 ≠ 0
  change Real.cos (0 : ℝ) ^ 2 ≠ 0
  norm_num

theorem localizedHelicity_weighted_helicity_integral_pos :
    0 < ∫ x : Torus3,
      localizedHelicityWeight x *
        inner ℝ (localizedHelicityVorticity x) (localizedHelicityVelocity x) := by
  have hweightedCont : Continuous (fun x : Torus3 =>
      localizedHelicityWeight x *
        inner ℝ (localizedHelicityVorticity x) (localizedHelicityVelocity x)) := by
    fun_prop
  have hweightedInt : Integrable (fun x : Torus3 =>
      localizedHelicityWeight x *
        inner ℝ (localizedHelicityVorticity x) (localizedHelicityVelocity x)) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hweightedCont.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hcosCont : Continuous (fun x : Torus3 => torusCosCoordinate 1 x ^ 2) := by fun_prop
  have hcosInt : Integrable (fun x : Torus3 => torusCosCoordinate 1 x ^ 2) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hcosCont.continuousOn.integrableOn_compact
        (μ := (volume : Measure Torus3))
        (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  have hsub := integral_sub hweightedInt hcosInt
  rw [localizedHelicity_weighted_remainder_integral_eq_zero] at hsub
  have heq := sub_eq_zero.mp hsub.symm
  rw [heq]
  exact localizedHelicity_cosSq_integral_pos

theorem localizedHelicity_stretchingCauchyDefect_pos :
    0 < torusVorticitySelfTransportQuotient localizedHelicityVorticity *
          periodicVorticityWeightedVelocityVariance
            localizedHelicityVelocity localizedHelicityVorticity 0 -
        (∫ x : Torus3,
          torusStretchingProduction
            localizedHelicityVelocity localizedHelicityVorticity x) ^ 2 := by
  let Q : ℝ := torusVorticitySelfTransportQuotient localizedHelicityVorticity
  let H : ℝ := ∫ x : Torus3, localizedHelicityWeight x *
    inner ℝ (localizedHelicityVorticity x)
      (centeredVelocity localizedHelicityVelocity 0 x)
  let A : ℝ := ∫ x : Torus3, localizedHelicityWeight x ^ 2
  let D : ℝ := Q * periodicVorticityWeightedVelocityVariance
      localizedHelicityVelocity localizedHelicityVorticity 0 -
    (∫ x : Torus3,
      torusStretchingProduction localizedHelicityVelocity localizedHelicityVorticity x) ^ 2
  have hQ : 0 < Q := localizedHelicity_selfTransportQuotient_pos
  have hH : 0 < H := by
    dsimp [H]
    simpa [centeredVelocity_apply] using
      localizedHelicity_weighted_helicity_integral_pos
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x => sq_nonneg (localizedHelicityWeight x)
  have hgap : Q * H ^ 2 ≤ A * D := by
    simpa [Q, H, A, D] using
      (torus_stretchingCauchyDefect_firstIntegralWeighted_centered_helicity_lower_bound
        localizedHelicityVelocity localizedHelicityVorticity 0 localizedHelicityWeight
        (localizedHelicityVelocity_contDiff.of_le (by norm_num))
        localizedHelicityVorticity_contDiff localizedHelicityWeight_contDiff
        localizedHelicityVorticity_divergence localizedHelicityWeight_firstIntegral hQ.ne')
  have hleft : 0 < Q * H ^ 2 := mul_pos hQ (sq_pos_of_pos hH)
  have hright : 0 < A * D := hleft.trans_le hgap
  have hD : 0 < D := by
    by_contra hnot
    have hDnonpos : D ≤ 0 := le_of_not_gt hnot
    have := mul_nonpos_of_nonneg_of_nonpos hA hDnonpos
    linarith
  exact hD

end
