import NSFormal.FlowKoopman
import NSFormal.LocalizedHelicity

/-!
# A nontrivial Haar-preserving flow on the three-torus

The identity-flow inhabitant in `FlowKoopman.lean` verifies that the strongly
continuous interface is nonempty.  This file supplies a genuinely moving
example: the shear

`(x, y, z) ↦ (x + s cos y, y, z)`.

Its generator is the smooth divergence-free periodic curl field
`(cos y, 0, 0)`.  Besides strengthening nonvacuity, this is a concrete testbed
for the remaining bridge between Koopman generators and the descended torus
transport operator.
-/

open Function MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

private abbrev TorusCircle := AddCircle ((2 : ℝ) * Real.pi)

/-! ## The shear flow -/

/-- Translation in the first torus coordinate by `s cos(y)`. -/
def torus3CosShearMap (s : ℝ) (x : Torus3) : Torus3 :=
  fun i => x i + if i = 0 then ((s * torusCosCoordinate 1 x : ℝ) : TorusCircle) else 0

@[simp]
theorem torus3CosShearMap_apply_zero (s : ℝ) (x : Torus3) :
    torus3CosShearMap s x 0 =
      x 0 + ((s * torusCosCoordinate 1 x : ℝ) : TorusCircle) := by
  simp [torus3CosShearMap]

@[simp]
theorem torus3CosShearMap_apply_one (s : ℝ) (x : Torus3) :
    torus3CosShearMap s x 1 = x 1 := by
  simp [torus3CosShearMap]

@[simp]
theorem torus3CosShearMap_apply_two (s : ℝ) (x : Torus3) :
    torus3CosShearMap s x 2 = x 2 := by
  simp [torus3CosShearMap]

theorem torusCosCoordinate_one_torus3CosShearMap (s : ℝ) (x : Torus3) :
    torusCosCoordinate 1 (torus3CosShearMap s x) = torusCosCoordinate 1 x := by
  change Real.cos_periodic.lift (torus3CosShearMap s x 1) =
    Real.cos_periodic.lift (x 1)
  rw [torus3CosShearMap_apply_one]

theorem torus3CosShearMap_continuous :
    Continuous (uncurry torus3CosShearMap) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : ℝ × Torus3 => torus3CosShearMap p.1 p.2 0)
    rw [show (fun p : ℝ × Torus3 => torus3CosShearMap p.1 p.2 0) =
        fun p => p.2 0 + ((p.1 * torusCosCoordinate 1 p.2 : ℝ) : TorusCircle) by
      funext p
      rw [torus3CosShearMap_apply_zero]]
    fun_prop
  · change Continuous (fun p : ℝ × Torus3 => torus3CosShearMap p.1 p.2 1)
    rw [show (fun p : ℝ × Torus3 => torus3CosShearMap p.1 p.2 1) =
        fun p => p.2 1 by
      funext p
      rw [torus3CosShearMap_apply_one]]
    fun_prop
  · change Continuous (fun p : ℝ × Torus3 => torus3CosShearMap p.1 p.2 2)
    rw [show (fun p : ℝ × Torus3 => torus3CosShearMap p.1 p.2 2) =
        fun p => p.2 2 by
      funext p
      rw [torus3CosShearMap_apply_two]]
    fun_prop

/-- The cosine shear as an additive continuous flow. -/
def torus3CosShearFlow : Flow ℝ Torus3 where
  toFun := torus3CosShearMap
  cont' := torus3CosShearMap_continuous
  map_add' s t x := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta]
      rw [torus3CosShearMap_apply_zero, torus3CosShearMap_apply_zero,
        torus3CosShearMap_apply_zero, torusCosCoordinate_one_torus3CosShearMap]
      rw [show (s + t) * torusCosCoordinate 1 x =
          t * torusCosCoordinate 1 x + s * torusCosCoordinate 1 x by ring]
      rw [AddCircle.coe_add]
      abel
    · simp [torus3CosShearMap]
    · simp [torus3CosShearMap]
  map_zero' x := by
    funext i
    fin_cases i <;> simp [torus3CosShearMap]

@[simp]
theorem torus3CosShearFlow_apply (s : ℝ) (x : Torus3) :
    torus3CosShearFlow s x = torus3CosShearMap s x := rfl

/-! ## Haar-volume preservation -/

/-- The translation amount after splitting off the first torus coordinate. -/
def torusCosShearShift (s : ℝ) (y : TorusCoordinateComplement) : TorusCircle :=
  ((s * Real.cos_periodic.lift (y 0) : ℝ) : TorusCircle)

/-- The shear in split coordinates `(x, (y,z))`. -/
def torusCosShearPairMap (s : ℝ)
    (p : TorusCircle × TorusCoordinateComplement) :
    TorusCircle × TorusCoordinateComplement :=
  (p.1 + torusCosShearShift s p.2, p.2)

theorem torusCosShearShift_continuous (s : ℝ) :
    Continuous (torusCosShearShift s) := by
  have hc : Continuous
      (fun y : TorusCoordinateComplement => Real.cos_periodic.lift (y 0)) :=
    Real.continuous_cos.quotient_liftOn' _ |>.comp (continuous_apply 0)
  exact continuous_quot_mk.comp (continuous_const.mul hc)

theorem torusCosShearPairMap_measurePreserving (s : ℝ) :
    MeasurePreserving (torusCosShearPairMap s)
      (volume : Measure (TorusCircle × TorusCoordinateComplement)) volume := by
  have htranslate : ∀ y : TorusCoordinateComplement,
      MeasurePreserving (fun a : TorusCircle => a + torusCosShearShift s y)
        volume volume := by
    intro y
    exact measurePreserving_add_right volume (torusCosShearShift s y)
  have hmeas : Measurable
      (uncurry fun y : TorusCoordinateComplement =>
        fun a : TorusCircle => a + torusCosShearShift s y) := by
    apply Continuous.measurable
    exact continuous_snd.add ((torusCosShearShift_continuous s).comp continuous_fst)
  have hskew : MeasurePreserving
      (fun p : TorusCoordinateComplement × TorusCircle =>
        (p.1, p.2 + torusCosShearShift s p.1))
      ((volume : Measure TorusCoordinateComplement).prod volume)
      ((volume : Measure TorusCoordinateComplement).prod volume) :=
    (MeasurePreserving.id (volume : Measure TorusCoordinateComplement)).skew_product
      hmeas (Filter.Eventually.of_forall fun y => (htranslate y).map_eq)
  have hswapForward : MeasurePreserving
      (Prod.swap : TorusCircle × TorusCoordinateComplement →
        TorusCoordinateComplement × TorusCircle)
      ((volume : Measure TorusCircle).prod volume)
      ((volume : Measure TorusCoordinateComplement).prod volume) :=
    Measure.measurePreserving_swap
  have hswapBackward : MeasurePreserving
      (Prod.swap : TorusCoordinateComplement × TorusCircle →
        TorusCircle × TorusCoordinateComplement)
      ((volume : Measure TorusCoordinateComplement).prod volume)
      ((volume : Measure TorusCircle).prod volume) :=
    Measure.measurePreserving_swap
  have hconjugated : MeasurePreserving
      (fun p : TorusCircle × TorusCoordinateComplement =>
        (p.1 + torusCosShearShift s p.2, p.2))
      ((volume : Measure TorusCircle).prod volume)
      ((volume : Measure TorusCircle).prod volume) := by
    have hcomp := hswapBackward.comp (hskew.comp hswapForward)
    change MeasurePreserving
      (fun p : TorusCircle × TorusCoordinateComplement =>
        (p.1 + torusCosShearShift s p.2, p.2))
      ((volume : Measure TorusCircle).prod volume)
      ((volume : Measure TorusCircle).prod volume) at hcomp
    exact hcomp
  change MeasurePreserving
    (fun p : TorusCircle × TorusCoordinateComplement =>
      (p.1 + torusCosShearShift s p.2, p.2)) volume volume
  rw [Measure.volume_eq_prod]
  exact hconjugated

theorem torus3_coordinateSplit_cosShearMap (s : ℝ) (x : Torus3) :
    MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin 3 => TorusCircle) 0 (torus3CosShearMap s x) =
      torusCosShearPairMap s
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin 3 => TorusCircle) 0 x) := by
  apply Prod.ext
  · change torus3CosShearMap s x 0 = x 0 + torusCosShearShift s (Fin.removeNth 0 x)
    rw [torus3CosShearMap_apply_zero]
    rfl
  · funext j
    fin_cases j
    · change torus3CosShearMap s x 1 = x 1
      exact torus3CosShearMap_apply_one s x
    · change torus3CosShearMap s x 2 = x 2
      exact torus3CosShearMap_apply_two s x

/-- Every time slice of the nontrivial cosine shear preserves Haar volume on
the actual measured three-torus. -/
theorem torus3CosShearFlow_measurePreserving (s : ℝ) :
    MeasurePreserving (torus3CosShearFlow s)
      (volume : Measure Torus3) volume := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin 3 => TorusCircle) 0
  have he : MeasurePreserving e := torus3_volume_preserving_coordinate_split 0
  have hesymm : MeasurePreserving e.symm := MeasurePreserving.symm e he
  have hpair := torusCosShearPairMap_measurePreserving s
  have hfactor : torus3CosShearFlow s = e.symm ∘ torusCosShearPairMap s ∘ e := by
    funext x
    apply e.injective
    change e (torus3CosShearMap s x) =
      e (e.symm (torusCosShearPairMap s (e x)))
    rw [e.apply_symm_apply]
    exact torus3_coordinateSplit_cosShearMap s x
  rw [hfactor]
  exact hesymm.comp (hpair.comp he)

/-! ## The generating periodic curl field -/

/-- A smooth periodic velocity whose curl generates the cosine shear. -/
def torusCosShearVelocity : C(Torus3, Vec3) :=
  ⟨fun x => WithLp.toLp 2 ![0, 0, torusSinCoordinate 1 x], by
    exact (PiLp.continuous_toLp 2 _).comp (by
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop)⟩

/-- The vector field `(cos y, 0, 0)` generating `torus3CosShearFlow`. -/
def torusCosShearVorticity : C(Torus3, Vec3) :=
  ⟨fun x => WithLp.toLp 2 ![torusCosCoordinate 1 x, 0, 0], by
    exact (PiLp.continuous_toLp 2 _).comp (by
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop)⟩

theorem torusCosShearVelocity_contDiff :
    ContDiff ℝ 2 (torusLift torusCosShearVelocity) := by
  change ContDiff ℝ 2 (fun y : Vec3 => WithLp.toLp 2 ![0, 0, Real.sin (y 1)])
  apply PiLp.contDiff_toLp.comp
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem torusCosShearVorticity_contDiff :
    ContDiff ℝ 1 (torusLift torusCosShearVorticity) := by
  change ContDiff ℝ 1 (fun y : Vec3 => WithLp.toLp 2 ![Real.cos (y 1), 0, 0])
  apply PiLp.contDiff_toLp.comp
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The shear generator is a genuine periodic curl, not an arbitrary abstract
divergence-free field. -/
theorem torusCosShearVorticity_eq_curl (x : Torus3) :
    torusCosShearVorticity x = torusCurl torusCosShearVelocity x := by
  rw [← periodicCoordinateCurl_eq_torusCurl torusCosShearVelocity x
    (torusCosShearVelocity_contDiff.of_le (by norm_num))]
  ext q
  fin_cases q <;>
    simp [periodicCoordinateCurl, periodicFirstDerivative,
      torusCosShearVelocity, torusCosShearVorticity,
      torusCoordinateDerivative_sinCoordinate]

theorem torusCosShearVorticity_divergence (x : Torus3) :
    torusCoordinateDivergence torusCosShearVorticity x = 0 := by
  exact torusCoordinateDivergence_eq_zero_of_eq_torusCurl
    torusCosShearVelocity torusCosShearVorticity
    torusCosShearVelocity_contDiff torusCosShearVorticity_contDiff
    torusCosShearVorticity_eq_curl x

/-- The generator is concretely nonzero at the torus origin. -/
theorem torusCosShearVorticity_origin_ne_zero :
  torusCosShearVorticity torus3Origin ≠ 0 := by
  intro h
  have hzero := congrFun
    (congrArg (WithLp.ofLp : Vec3 → Fin 3 → ℝ) h) 0
  change Real.cos (0 : ℝ) = 0 at hzero
  norm_num at hzero

/-! ## Identification of the classical generator -/

theorem torusCosShearVorticity_scalarTransport
    (f : Torus3 → ℝ) (x : Torus3) :
    torusScalarTransport torusCosShearVorticity f x =
      torusCosCoordinate 1 x * torusCoordinateDerivative f 0 x := by
  rw [torusScalarTransport, Fin.sum_univ_three]
  simp [torusCosShearVorticity]

/-- On every scalar field differentiable along the first coordinate circle,
the pointwise generator of the concrete cosine shear is exactly the descended
transport operator `w·∇`. -/
theorem torus3CosShearFlow_hasDerivAt
    (f : Torus3 → ℝ) (x : Torus3)
    (hf : ContDiff ℝ 1
      (torusCoordinateSliceLift f 0 (Fin.removeNth 0 x))) :
    HasDerivAt (fun s : ℝ => f (torus3CosShearFlow s x))
      (torusScalarTransport torusCosShearVorticity f x) 0 := by
  let y : TorusCoordinateComplement := Fin.removeNth 0 x
  let r : ℝ := (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x 0)).1
  let c : ℝ := torusCosCoordinate 1 x
  let g : ℝ → ℝ := torusCoordinateSliceLift f 0 y
  have hpath : (fun s : ℝ => f (torus3CosShearFlow s x)) =
      fun s => g (r + s * c) := by
    funext s
    apply congrArg f
    funext i
    induction i using (0 : Fin 3).succAboveCases
    · change x 0 + ((s * c : ℝ) : TorusCircle) =
        ((r + s * c : ℝ) : TorusCircle)
      rw [AddCircle.coe_add]
      rw [show ((r : ℝ) : TorusCircle) = x 0 by
        unfold r
        exact AddCircle.coe_equivIoc]
    · rename_i j
      change torus3CosShearMap s x ((0 : Fin 3).succAbove j) =
        y j
      change x ((0 : Fin 3).succAbove j) +
          (if (0 : Fin 3).succAbove j = 0 then
            ((s * torusCosCoordinate 1 x : ℝ) : TorusCircle) else 0) =
        x ((0 : Fin 3).succAbove j)
      rw [if_neg (Fin.succAbove_ne 0 j), add_zero]
  have hg : HasDerivAt g (deriv g r) r :=
    (hf.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have haffine : HasDerivAt (fun s : ℝ => r + s * c) c 0 := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add r
  have hg0 : HasDerivAt g (deriv g r) (r + 0 * c) := by
    simpa using hg
  have hcomp : HasDerivAt (g ∘ fun s : ℝ => r + s * c)
      (deriv g r * c) 0 := hg0.comp 0 haffine
  rw [hpath]
  change HasDerivAt (g ∘ fun s : ℝ => r + s * c)
    (torusScalarTransport torusCosShearVorticity f x) 0
  convert hcomp using 1
  rw [torusCosShearVorticity_scalarTransport]
  change c * AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0 (deriv g) (x 0) =
    deriv g r * c
  change c * deriv g r = deriv g r * c
  ring

/-- The cosine shear is not the identity flow.  This follows inside the
formalization from its nonzero action on the first sine mode. -/
theorem torus3CosShearFlow_ne_identity :
    torus3CosShearFlow ≠ Flow.id ℝ Torus3 := by
  intro hflow
  have hslice : ContDiff ℝ 1
      (torusCoordinateSliceLift (torusSinCoordinate 0) 0
        (Fin.removeNth 0 torus3Origin)) :=
    contDiff_torusCoordinateSliceLift_of_contDiff_torusLift
      (torusSinCoordinate 0) 0 (Fin.removeNth 0 torus3Origin)
      (torusSinCoordinate_contDiff 0)
  have hderiv := torus3CosShearFlow_hasDerivAt
    (torusSinCoordinate 0) torus3Origin hslice
  have hpath : (fun s : ℝ => torusSinCoordinate 0
      (torus3CosShearFlow s torus3Origin)) =
      fun _ : ℝ => torusSinCoordinate 0 torus3Origin := by
    funext s
    rw [hflow]
    rfl
  rw [hpath] at hderiv
  have hzero : HasDerivAt
      (fun _ : ℝ => torusSinCoordinate 0 torus3Origin) 0 0 :=
    hasDerivAt_const (x := (0 : ℝ)) _
  have hgeneratorZero :
      torusScalarTransport torusCosShearVorticity
        (torusSinCoordinate 0) torus3Origin = 0 :=
    hderiv.unique hzero
  rw [torusCosShearVorticity_scalarTransport,
    torusCoordinateDerivative_sinCoordinate] at hgeneratorZero
  change Real.cos (0 : ℝ) * Real.cos (0 : ℝ) = 0 at hgeneratorZero
  norm_num at hgeneratorZero

/-! ## The concrete Koopman and Fejér constructions -/

abbrev TorusScalarL2 := Lp ℝ 2 (volume : Measure Torus3)

/-- The strong Koopman interval average specialized to the nontrivial cosine
shear on the measured three-torus. -/
def torus3CosShearKoopmanAverage (L : ℝ) (hL : 0 < L) :
    TorusScalarL2 →L[ℝ] TorusScalarL2 :=
  measurePreservingFlowKoopmanAverage (volume : Measure Torus3)
    torus3CosShearFlow torus3CosShearFlow_measurePreserving L hL

/-- The corresponding positive Fejér weight. -/
def torus3CosShearFejerWeight (L : ℝ) (hL : 0 < L)
    (seed : TorusScalarL2) : TorusScalarL2 :=
  measurePreservingFlowFejerWeight (volume : Measure Torus3)
    torus3CosShearFlow torus3CosShearFlow_measurePreserving L hL seed

theorem torus3CosShearKoopman_stronglyContinuous (seed : TorusScalarL2) :
    Continuous (fun s => measurePreservingFlowKoopman (volume : Measure Torus3)
      torus3CosShearFlow torus3CosShearFlow_measurePreserving s seed) := by
  exact measurePreservingFlowKoopman_stronglyContinuous
    (volume : Measure Torus3) torus3CosShearFlow
    torus3CosShearFlow_measurePreserving seed

theorem torus3CosShearFejerWeight_generator_norm_le
    (L : ℝ) (hL : 0 < L) (seed : TorusScalarL2) :
    ‖L⁻¹ •
        (torus3CosShearKoopmanAverage L hL).adjoint
          (measurePreservingFlowKoopman (volume : Measure Torus3)
            torus3CosShearFlow torus3CosShearFlow_measurePreserving L seed - seed)‖ ≤
      (2 / L) * ‖seed‖ := by
  exact measurePreservingFlowFejerWeight_generator_norm_le
    (volume : Measure Torus3) torus3CosShearFlow
    torus3CosShearFlow_measurePreserving L hL seed

/-- A concrete nonzero invariant seed for the moving shear flow. -/
def torus3ConstantOneL2 : TorusScalarL2 :=
  Lp.const 2 (volume : Measure Torus3) (1 : ℝ)

theorem torus3ConstantOneL2_ne_zero : torus3ConstantOneL2 ≠ 0 := by
  have hnorm : 0 < ‖torus3ConstantOneL2‖ := by
    rw [torus3ConstantOneL2,
      Lp.norm_const 2 (volume : Measure Torus3) (1 : ℝ) (by norm_num)]
    simp only [norm_one, one_mul]
    exact Real.rpow_pos_of_pos measureReal_univ_pos _
  exact norm_ne_zero_iff.mp hnorm.ne'

theorem torus3CosShearKoopman_constantOne (s : ℝ) :
    measurePreservingFlowKoopman (volume : Measure Torus3)
      torus3CosShearFlow torus3CosShearFlow_measurePreserving s
        torus3ConstantOneL2 = torus3ConstantOneL2 := by
  change Lp.compMeasurePreserving (torus3CosShearFlow s)
      (torus3CosShearFlow_measurePreserving s) torus3ConstantOneL2 =
    torus3ConstantOneL2
  apply Subtype.ext
  change (AEEqFun.const Torus3 (1 : ℝ)).compMeasurePreserving
      (torus3CosShearFlow s) (torus3CosShearFlow_measurePreserving s) =
    AEEqFun.const Torus3 (1 : ℝ)
  rfl

theorem torus3CosShearKoopmanAverage_constantOne
    (L : ℝ) (hL : 0 < L) :
    torus3CosShearKoopmanAverage L hL torus3ConstantOneL2 =
      torus3ConstantOneL2 := by
  rw [torus3CosShearKoopmanAverage,
    measurePreservingFlowKoopmanAverage_apply]
  simp_rw [torus3CosShearKoopman_constantOne]
  rw [intervalIntegral.integral_const]
  simp [hL.ne']

/-- The positive Fejér signal is strictly positive on an explicit seed for the
nontrivial flow. -/
theorem torus3CosShearFejerWeight_constantOne_signal_pos
    (L : ℝ) (hL : 0 < L) :
    0 < inner ℝ (torus3CosShearFejerWeight L hL torus3ConstantOneL2)
      torus3ConstantOneL2 := by
  apply measurePreservingFlowFejerWeight_inner_seed_pos
  rw [← torus3CosShearKoopmanAverage]
  rw [torus3CosShearKoopmanAverage_constantOne L hL]
  exact torus3ConstantOneL2_ne_zero

/-! ### A nonconstant retained first integral -/

/-- The nonconstant exact first integral `cos y`, promoted to the actual
scalar `L²` space. -/
def torus3CosineFirstIntegralL2 : TorusScalarL2 :=
  ((torusCosCoordinate 1).memLp_torus_volume 2).toLp (torusCosCoordinate 1)

theorem torus3CosineFirstIntegralL2_ne_zero :
    torus3CosineFirstIntegralL2 ≠ 0 := by
  let hmem := (torusCosCoordinate 1).memLp_torus_volume 2
  intro hzero
  have hcoe := hmem.coeFn_toLp
  have hzero' : hmem.toLp (torusCosCoordinate 1) = 0 := by
    simpa only [torus3CosineFirstIntegralL2] using hzero
  rw [hzero'] at hcoe
  have hae : (fun x : Torus3 => torusCosCoordinate 1 x) =ᵐ[
      (volume : Measure Torus3)] 0 := by
    filter_upwards [hcoe.symm] with x hx
    simpa using hx
  have hintegralZero :
      (∫ x : Torus3, torusCosCoordinate 1 x ^ 2) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with x hx
    simp [hx]
  exact (ne_of_gt localizedHelicity_cosSq_integral_pos) hintegralZero

theorem torus3CosShearKoopman_cosineFirstIntegral (s : ℝ) :
    measurePreservingFlowKoopman (volume : Measure Torus3)
      torus3CosShearFlow torus3CosShearFlow_measurePreserving s
        torus3CosineFirstIntegralL2 = torus3CosineFirstIntegralL2 := by
  let hmem := (torusCosCoordinate 1).memLp_torus_volume 2
  change Lp.compMeasurePreserving (torus3CosShearFlow s)
      (torus3CosShearFlow_measurePreserving s)
        (hmem.toLp (torusCosCoordinate 1)) =
    hmem.toLp (torusCosCoordinate 1)
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x =>
    torusCosCoordinate_one_torus3CosShearMap s x

theorem torus3CosShearKoopmanAverage_cosineFirstIntegral
    (L : ℝ) (hL : 0 < L) :
    torus3CosShearKoopmanAverage L hL torus3CosineFirstIntegralL2 =
      torus3CosineFirstIntegralL2 := by
  rw [torus3CosShearKoopmanAverage,
    measurePreservingFlowKoopmanAverage_apply]
  simp_rw [torus3CosShearKoopman_cosineFirstIntegral]
  rw [intervalIntegral.integral_const]
  simp [hL.ne']

/-- The positive Fejér construction retains a strictly positive signal from a
concrete nonconstant first integral of the nonidentity flow. -/
theorem torus3CosShearFejerWeight_cosineFirstIntegral_signal_pos
    (L : ℝ) (hL : 0 < L) :
    0 < inner ℝ
      (torus3CosShearFejerWeight L hL torus3CosineFirstIntegralL2)
      torus3CosineFirstIntegralL2 := by
  apply measurePreservingFlowFejerWeight_inner_seed_pos
  rw [← torus3CosShearKoopmanAverage]
  rw [torus3CosShearKoopmanAverage_cosineFirstIntegral L hL]
  exact torus3CosineFirstIntegralL2_ne_zero
