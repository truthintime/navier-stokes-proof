import NSFormal.NavierStokes
import NSFormal.PeriodicIntegration
import NSFormal.VortexStretching

/-!
# Global enstrophy on the periodic three-torus

This file connects the sup-norm time-differentiability used by the concrete
Navier--Stokes interfaces to the Haar-volume enstrophy functional.  The key
point is that integration on the compact torus is itself a continuous linear
map on continuous scalar fields.  Consequently differentiation under the
spatial integral is a direct chain-rule theorem, with no separately assumed
dominated-convergence hypothesis.
-/

open MeasureTheory Set

noncomputable section

/-! ## Identifying the integration and PDE derivatives -/

/-- Differentiation preserves periodicity.  This statement does not need a
regularity hypothesis: `deriv` is defined to be zero where differentiation
fails, and translation preserves that failure as well as genuine derivatives. -/
theorem Function.Periodic.deriv
    {f : ℝ → ℝ} {T : ℝ} (hf : Function.Periodic f T) :
    Function.Periodic (_root_.deriv f) T := by
  intro x
  have h := congrFun
    (congrArg (fun g : ℝ → ℝ => _root_.deriv g) hf.funext) x
  rw [_root_.deriv_comp_add_const] at h
  exact h

/-- The descended coordinate derivative can be evaluated at the canonical
`Ico` representative, even though its definition uses `liftIoc`.  Periodicity
of the derivative is what identifies the two values at the quotient seam. -/
theorem torusCoordinateDerivative_eq_deriv_slice_representative
    (f : Torus3 → ℝ) (i : Fin 3) (x : Torus3) :
    torusCoordinateDerivative f i x =
      deriv (torusCoordinateSliceLift f i (Fin.removeNth i x))
        (torus3Representative x i) := by
  let q : ℝ → ℝ := torusCoordinateSliceLift f i (Fin.removeNth i x)
  have hqper : Function.Periodic q ((2 : ℝ) * Real.pi) :=
    torusCoordinateSliceLift_periodic f i (Fin.removeNth i x)
  have hqderiv := hqper.deriv
  have hend : deriv q 0 = deriv q (0 + (2 : ℝ) * Real.pi) :=
    (hqderiv 0).symm
  have hrep : torus3Representative x i ∈
      Set.Ico (0 : ℝ) (0 + (2 : ℝ) * Real.pi) := by
    exact (AddCircle.equivIco ((2 : ℝ) * Real.pi) 0 (x i)).property
  have hcoe :
      ((torus3Representative x i : ℝ) :
        AddCircle ((2 : ℝ) * Real.pi)) = x i := by
    exact AddCircle.coe_equivIco
  rw [torusCoordinateDerivative, torusCoordinateSliceDerivative]
  change AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0 (deriv q) (x i) = _
  rw [← hcoe, AddCircle.liftIoc_eq_liftIco hend,
    AddCircle.liftIco_coe_apply hrep]

/-- Moving along a lifted Euclidean coordinate line is exactly the real lift
of the corresponding coordinate slice of the quotient torus. -/
theorem torus3Mk_coordinateLine_representative
    (x : Torus3) (i : Fin 3) (s : ℝ) :
    torus3Mk (coordinateLine (torus3Representative x) i s) =
      i.insertNth
        (((torus3Representative x i + s : ℝ) :
          AddCircle ((2 : ℝ) * Real.pi)))
        (Fin.removeNth i x) := by
  symm
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [torus3Mk, coordinateLine]
  · ext j
    simp [Fin.removeNth_apply, torus3Mk, coordinateLine,
      torus3Representative]

/-- The coordinate derivative used by the concrete Haar integration theory is
the same derivative as `torusPartial`, used by the Navier--Stokes PDE.  This is
the central compatibility lemma between the two independently constructed
periodic-calculus layers. -/
theorem torusCoordinateDerivative_eq_torusPartial
    (f : C(Torus3, ℝ)) (i : Fin 3) (x : Torus3)
    (hf : ContDiff ℝ 1 (torusLift f)) :
    torusCoordinateDerivative f i x = torusPartial f x i := by
  rw [torusCoordinateDerivative_eq_deriv_slice_representative]
  let q : ℝ → ℝ := torusCoordinateSliceLift f i (Fin.removeNth i x)
  let r : ℝ := torus3Representative x i
  have hfun : (fun s : ℝ => q (r + s)) =
      fun s : ℝ => torusLift f
        (coordinateLine (torus3Representative x) i s) := by
    funext s
    change f (i.insertNth
        (((torus3Representative x i + s : ℝ) :
          AddCircle ((2 : ℝ) * Real.pi)))
        (Fin.removeNth i x)) =
      f (torus3Mk (coordinateLine (torus3Representative x) i s))
    rw [torus3Mk_coordinateLine_representative]
  have hshift : deriv q r = deriv (fun s : ℝ => q (r + s)) 0 := by
    rw [deriv_comp_const_add]
    simp
  rw [show deriv (torusCoordinateSliceLift f i (Fin.removeNth i x))
      (torus3Representative x i) = deriv q r by rfl, hshift, hfun]
  have hdifferentiable : DifferentiableAt ℝ (torusLift f)
      (torus3Representative x) :=
    (hf.differentiable one_ne_zero).differentiableAt
  rw [show (fun s : ℝ => torusLift f
      (coordinateLine (torus3Representative x) i s)) =
        fun s : ℝ => torusLift f
          (torus3Representative x + s • EuclideanSpace.single i (1 : ℝ)) by
      rfl]
  have hdifferentiable0 : DifferentiableAt ℝ (torusLift f)
      (torus3Representative x +
        (0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
    simpa using hdifferentiable
  rw [hdifferentiable0.deriv_comp_add_smul]
  simp [torusPartial, torusDirectionalDerivative]

/-- A scalar component of a continuous torus vector field. -/
def torusVectorComponent (u : C(Torus3, Vec3)) (j : Fin 3) : C(Torus3, ℝ) :=
  ⟨fun x => u x j, by fun_prop⟩

@[simp]
theorem torusVectorComponent_apply
    (u : C(Torus3, Vec3)) (j : Fin 3) (x : Torus3) :
    torusVectorComponent u j x = u x j := rfl

/-- Compatibility of the descended scalar derivative with vector-field
components of the PDE derivative. -/
theorem torusCoordinateDerivative_component_eq_torusPartial
    (u : C(Torus3, Vec3)) (i j : Fin 3) (x : Torus3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    torusCoordinateDerivative (fun z => u z j) i x = torusPartial u x i j := by
  have hucomp : ContDiff ℝ 1 (torusLift (torusVectorComponent u j)) := by
    change ContDiff ℝ 1 (fun y => torusLift u y j)
    exact ContDiff.continuousLinearMap_comp (EuclideanSpace.proj j) hu
  have hscalar := torusCoordinateDerivative_eq_torusPartial
    (torusVectorComponent u j) i x hucomp
  have hudiff : DifferentiableAt ℝ (torusLift u) (torus3Representative x) :=
    (hu.differentiable one_ne_zero).differentiableAt
  have hcomp := (EuclideanSpace.proj j).hasFDerivAt.comp
    (torus3Representative x) hudiff.hasFDerivAt
  have hfd := hcomp.fderiv
  have hfun : torusLift (torusVectorComponent u j) =
      (EuclideanSpace.proj j) ∘ torusLift u := by
    rfl
  rw [torusPartial, torusDirectionalDerivative, hfun, hfd,
    ContinuousLinearMap.comp_apply] at hscalar
  exact hscalar

/-- The divergence used by concrete Haar integration is exactly the divergence
appearing in the Navier--Stokes predicate. -/
theorem torusCoordinateDivergence_eq_torusDivergence
    (u : C(Torus3, Vec3)) (x : Torus3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    torusCoordinateDivergence u x = torusDivergence u x := by
  unfold torusCoordinateDivergence torusDivergence
  apply Finset.sum_congr rfl
  intro i _hi
  exact torusCoordinateDerivative_component_eq_torusPartial u i i x hu

/-- Coordinate differentiation of half squared vorticity obeys the exact chain
rule used in the scalar enstrophy equation. -/
theorem torusPartial_vorticityEnergyField
    (w : C(Torus3, Vec3)) (x : Torus3) (i : Fin 3)
    (hw : ContDiff ℝ 1 (torusLift w)) :
    torusPartial (vorticityEnergyField w) x i =
      inner ℝ (w x) (torusPartial w x i) := by
  let e : Vec3 := EuclideanSpace.single i (1 : ℝ)
  let r : Vec3 := torus3Representative x
  have hwline : ContDiff ℝ 1 (fun s : ℝ => torusLift w (r + s • e)) :=
    hw.comp (by fun_prop)
  have hwlineAt : HasDerivAt (fun s : ℝ => torusLift w (r + s • e))
      (deriv (fun s : ℝ => torusLift w (r + s • e)) 0) 0 :=
    (hwline.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have hline := hasDerivAt_vorticityEnergy hwlineAt
  have hlineDeriv :
      deriv (fun s : ℝ => vorticityEnergy (torusLift w (r + s • e))) 0 =
        inner ℝ (torusLift w r)
          (deriv (fun s : ℝ => torusLift w (r + s • e)) 0) :=
    by simpa using hline.deriv
  have hwDiff : DifferentiableAt ℝ (torusLift w) r :=
    (hw.differentiable one_ne_zero).differentiableAt
  have hwDiff0 : DifferentiableAt ℝ (torusLift w) (r + (0 : ℝ) • e) := by
    simpa using hwDiff
  have hwLineDeriv := hwDiff0.deriv_comp_add_smul
  have henergy : ContDiff ℝ 1 (torusLift (vorticityEnergyField w)) := by
    change ContDiff ℝ 1 (fun y => vorticityEnergy (torusLift w y))
    simpa [vorticityEnergy, real_inner_self_eq_norm_sq] using
      (hw.inner ℝ hw).div_const (2 : ℝ)
  have henergyDiff : DifferentiableAt ℝ
      (torusLift (vorticityEnergyField w)) r :=
    (henergy.differentiable one_ne_zero).differentiableAt
  have henergyDiff0 : DifferentiableAt ℝ
      (torusLift (vorticityEnergyField w)) (r + (0 : ℝ) • e) := by
    simpa using henergyDiff
  have henergyLineDeriv := henergyDiff0.deriv_comp_add_smul
  calc
    torusPartial (vorticityEnergyField w) x i =
        fderiv ℝ (torusLift (vorticityEnergyField w)) r e := by
      rfl
    _ = deriv (fun s : ℝ =>
          torusLift (vorticityEnergyField w) (r + s • e)) 0 := by
      simpa using henergyLineDeriv.symm
    _ = deriv (fun s : ℝ =>
          vorticityEnergy (torusLift w (r + s • e))) 0 := by
      rfl
    _ = inner ℝ (torusLift w r)
          (deriv (fun s : ℝ => torusLift w (r + s • e)) 0) := hlineDeriv
    _ = inner ℝ (w x) (torusPartial w x i) := by
      rw [hwLineDeriv]
      simp [r, e, torusPartial, torusDirectionalDerivative, torusLift]

/-- Resolve a lifted directional derivative in the standard orthonormal
coordinate frame. -/
theorem torusDirectionalDerivative_eq_sum_partial
    (f : C(Torus3, Vec3)) (x : Torus3) (v : Vec3) :
    torusDirectionalDerivative f x v =
      ∑ i : Fin 3, v i • torusPartial f x i := by
  have hv : v = ∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_three]
  calc
    torusDirectionalDerivative f x v =
        fderiv ℝ (torusLift f) (torus3Representative x) v := rfl
    _ = fderiv ℝ (torusLift f) (torus3Representative x)
        (∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ)) :=
      congrArg (fderiv ℝ (torusLift f) (torus3Representative x)) hv
    _ = ∑ i : Fin 3, v i •
        fderiv ℝ (torusLift f) (torus3Representative x)
          (EuclideanSpace.single i (1 : ℝ)) := by simp
    _ = ∑ i : Fin 3, v i • torusPartial f x i := rfl

/-- The scalar energy transport produced by the advective vorticity term. -/
def torusVorticityTransportProduction
    (u w : C(Torus3, Vec3)) (x : Torus3) : ℝ :=
  inner ℝ (w x) (torusTransport u w x)

/-- The PDE transport pairing `⟨w,(u·∇)w⟩` is exactly the concrete
coordinate transport of the scalar half-squared-vorticity field. -/
theorem torusVorticityTransportProduction_eq_scalarTransport
    (u w : C(Torus3, Vec3)) (x : Torus3)
    (hw : ContDiff ℝ 1 (torusLift w)) :
    torusVorticityTransportProduction u w x =
      torusScalarTransport u (vorticityEnergyField w) x := by
  have henergy : ContDiff ℝ 1 (torusLift (vorticityEnergyField w)) := by
    change ContDiff ℝ 1 (fun y => vorticityEnergy (torusLift w y))
    simpa [vorticityEnergy, real_inner_self_eq_norm_sq] using
      (hw.inner ℝ hw).div_const (2 : ℝ)
  rw [torusVorticityTransportProduction, torusTransport,
    torusDirectionalDerivative_eq_sum_partial, torusScalarTransport, inner_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [real_inner_smul_right, ← torusPartial_vorticityEnergyField w x i hw,
    torusCoordinateDerivative_eq_torusPartial
      (vorticityEnergyField w) i x henergy]

/-! ## Concrete periodic cancellations -/

/-- The integral of scalar transport vanishes for a divergence-free periodic
field.  All Fubini/integrability obligations are explicit; the cancellation
itself is the already-proved Haar integration-by-parts theorem with the left
test function specialized to `1`. -/
theorem integral_torusScalarTransport_eq_zero
    (u : Torus3 → Vec3) (g : Torus3 → ℝ)
    (hu : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) i y))
    (hg : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift g i y))
    (hleft : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      (((1 : ℝ) * u x i) * torusCoordinateDerivative g i x)))
    (hright : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => (1 : ℝ) * u z i) i x * g x))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0) :
    (∫ x : Torus3, torusScalarTransport u g x) = 0 := by
  have hskew := torus3_divergenceFree_transport_skew
    u (fun _ : Torus3 => (1 : ℝ)) g hu
    (fun _ _ => contDiff_const) hg hleft hright hdiv
  simpa [torusScalarTransport] using hskew

/-- Consequently the advective term in the concrete vorticity equation makes
zero contribution to global enstrophy. -/
theorem integral_torusVorticityTransportProduction_eq_zero
    (u w : C(Torus3, Vec3))
    (hw : ContDiff ℝ 1 (torusLift w))
    (huSlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) i y))
    (henergySlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (vorticityEnergyField w) i y))
    (hleft : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      (((1 : ℝ) * u x i) *
        torusCoordinateDerivative (vorticityEnergyField w) i x)))
    (hright : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => (1 : ℝ) * u z i) i x *
        vorticityEnergyField w x))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0) :
    (∫ x : Torus3, torusVorticityTransportProduction u w x) = 0 := by
  calc
    (∫ x : Torus3, torusVorticityTransportProduction u w x) =
        ∫ x : Torus3,
          torusScalarTransport u (vorticityEnergyField w) x := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        torusVorticityTransportProduction_eq_scalarTransport u w x hw
    _ = 0 := integral_torusScalarTransport_eq_zero
      u (vorticityEnergyField w) huSlices henergySlices hleft hright hdiv

/-- Incompressibility from the concrete Navier--Stokes predicate is also
incompressibility for the coordinate operator used by Haar integration. -/
theorem IsClassicalNavierStokesOn.torusCoordinateDivergence_eq_zero
    {ν a b : ℝ} {u uTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (h : IsClassicalNavierStokesOn ν a b u uTime p)
    {t : ℝ} (ht : t ∈ Icc a b) (x : Torus3) :
    torusCoordinateDivergence (u t) x = 0 := by
  rw [torusCoordinateDivergence_eq_torusDivergence
    (u t) x ((h.2.2.2.1 t ht).of_le (by norm_num))]
  exact h.2.2.2.2.2.1 t ht x

/-- The scalar Laplacian of a continuous torus field, computed at the canonical
representative exactly as in the concrete vector Laplacian. -/
def torusScalarLaplacian (f : C(Torus3, ℝ)) (x : Torus3) : ℝ :=
  torusLiftLaplacian f (torus3Representative x)

/-! ## Mean-zero scalar Laplacian -/

/-- The second derivative of a smooth periodic scalar function has zero mean
over a fundamental interval. -/
theorem intervalIntegral_iteratedDeriv_two_eq_zero_of_periodic
    {T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T) (hf : ContDiff ℝ 2 f)
    (hper : Function.Periodic f T) :
    (∫ x in (0 : ℝ)..T, iteratedDeriv 2 f x) = 0 := by
  have hderiv : ContDiff ℝ 1 (deriv f) := by
    simpa using hf.deriv'
  have hderivPer : Function.Periodic (deriv f) T := hper.deriv
  simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ',
    iteratedDeriv_one] using
      intervalIntegral_deriv_eq_zero_of_periodic hT hderiv hderivPer

/-- Second derivative of a coordinate slice, descended to its measured
coordinate circle. -/
def torusCoordinateSliceSecondDerivative
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (a : AddCircle ((2 : ℝ) * Real.pi)) : ℝ :=
  AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
    (iteratedDeriv 2 (torusCoordinateSliceLift f i y)) a

/-- The descended second coordinate derivative on the whole torus. -/
def torusCoordinateSecondDerivative
    (f : Torus3 → ℝ) (i : Fin 3) (x : Torus3) : ℝ :=
  torusCoordinateSliceSecondDerivative f i (Fin.removeNth i x) (x i)

/-- Every smooth coordinate slice has zero circle mean second derivative. -/
theorem addCircle_integral_torusCoordinateSliceSecondDerivative_eq_zero
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (hf : ContDiff ℝ 2 (torusCoordinateSliceLift f i y)) :
    (∫ a : AddCircle ((2 : ℝ) * Real.pi),
      torusCoordinateSliceSecondDerivative f i y a) = 0 := by
  change (∫ a : AddCircle ((2 : ℝ) * Real.pi),
    AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
      (iteratedDeriv 2 (torusCoordinateSliceLift f i y)) a) = 0
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral]
  simpa only [zero_add] using
    intervalIntegral_iteratedDeriv_two_eq_zero_of_periodic
      (T := (2 : ℝ) * Real.pi)
      (mul_nonneg (by norm_num) Real.pi_nonneg) hf
        (torusCoordinateSliceLift_periodic f i y)

/-- Fubini lifts the circle cancellation to the physical three-torus. -/
theorem torus3_integral_coordinateSecondDerivative_eq_zero
    (f : Torus3 → ℝ) (i : Fin 3)
    (hf : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 2 (torusCoordinateSliceLift f i y))
    (hint : Integrable (torusCoordinateSecondDerivative f i)) :
    (∫ x : Torus3, torusCoordinateSecondDerivative f i x) = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin 3 => AddCircle ((2 : ℝ) * Real.pi)) i
  have he : MeasurePreserving e := torus3_volume_preserving_coordinate_split i
  have hesymm : MeasurePreserving e.symm := MeasurePreserving.symm e he
  have hint' : Integrable ((torusCoordinateSecondDerivative f i) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hint
  calc
    (∫ x : Torus3, torusCoordinateSecondDerivative f i x) =
        ∫ z : AddCircle ((2 : ℝ) * Real.pi) × TorusCoordinateComplement,
          (torusCoordinateSecondDerivative f i ∘ e.symm) z := by
      symm
      exact hesymm.integral_comp' (torusCoordinateSecondDerivative f i)
    _ = ∫ y : TorusCoordinateComplement,
        ∫ a : AddCircle ((2 : ℝ) * Real.pi),
          torusCoordinateSliceSecondDerivative f i y a := by
      rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hint']
      simp [e, torusCoordinateSecondDerivative,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    _ = 0 := by
      simp_rw [addCircle_integral_torusCoordinateSliceSecondDerivative_eq_zero
        f i _ (hf _)]
      simp

/-- As for the first derivative, the descended second derivative may be
evaluated at the canonical `Ico` representative. -/
theorem torusCoordinateSecondDerivative_eq_iteratedDeriv_slice_representative
    (f : Torus3 → ℝ) (i : Fin 3) (x : Torus3) :
    torusCoordinateSecondDerivative f i x =
      iteratedDeriv 2 (torusCoordinateSliceLift f i (Fin.removeNth i x))
        (torus3Representative x i) := by
  let q : ℝ → ℝ := torusCoordinateSliceLift f i (Fin.removeNth i x)
  have hqper : Function.Periodic q ((2 : ℝ) * Real.pi) :=
    torusCoordinateSliceLift_periodic f i (Fin.removeNth i x)
  have hqsecondPer :
      Function.Periodic (iteratedDeriv 2 q) ((2 : ℝ) * Real.pi) := by
    simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ',
      iteratedDeriv_one] using hqper.deriv.deriv
  have hend : iteratedDeriv 2 q 0 =
      iteratedDeriv 2 q (0 + (2 : ℝ) * Real.pi) :=
    (hqsecondPer 0).symm
  have hrep : torus3Representative x i ∈
      Set.Ico (0 : ℝ) (0 + (2 : ℝ) * Real.pi) :=
    (AddCircle.equivIco ((2 : ℝ) * Real.pi) 0 (x i)).property
  have hcoe :
      ((torus3Representative x i : ℝ) :
        AddCircle ((2 : ℝ) * Real.pi)) = x i :=
    AddCircle.coe_equivIco
  rw [torusCoordinateSecondDerivative,
    torusCoordinateSliceSecondDerivative]
  change AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
      (iteratedDeriv 2 q) (x i) = _
  rw [← hcoe, AddCircle.liftIoc_eq_liftIco hend,
    AddCircle.liftIco_coe_apply hrep]

/-- The lifted second coordinate derivative used by the PDE Laplacian equals
the descended derivative whose Haar integral vanishes. -/
theorem torusLiftCoordinateSecond_eq_torusCoordinateSecondDerivative
    (f : C(Torus3, ℝ)) (i : Fin 3) (x : Torus3) :
    torusLiftCoordinateSecond f (torus3Representative x) i =
      torusCoordinateSecondDerivative f i x := by
  rw [torusCoordinateSecondDerivative_eq_iteratedDeriv_slice_representative]
  let q : ℝ → ℝ := torusCoordinateSliceLift f i (Fin.removeNth i x)
  let r : ℝ := torus3Representative x i
  have hfun : (fun s : ℝ => q (r + s)) =
      fun s : ℝ => torusLift f
        (coordinateLine (torus3Representative x) i s) := by
    funext s
    change f (i.insertNth
        (((torus3Representative x i + s : ℝ) :
          AddCircle ((2 : ℝ) * Real.pi)))
        (Fin.removeNth i x)) =
      f (torus3Mk (coordinateLine (torus3Representative x) i s))
    rw [torus3Mk_coordinateLine_representative]
  have hiter := congrFun (congrArg (iteratedDeriv 2) hfun) 0
  rw [iteratedDeriv_comp_const_add] at hiter
  simpa [torusLiftCoordinateSecond, q, r] using hiter.symm

/-- Coordinate decomposition of the concrete scalar torus Laplacian. -/
theorem torusScalarLaplacian_eq_sum_coordinateSecondDerivative
    (f : C(Torus3, ℝ)) (x : Torus3) :
    torusScalarLaplacian f x =
      ∑ i : Fin 3, torusCoordinateSecondDerivative f i x := by
  unfold torusScalarLaplacian torusLiftLaplacian
  apply Finset.sum_congr rfl
  intro i _hi
  exact torusLiftCoordinateSecond_eq_torusCoordinateSecondDerivative f i x

/-- The scalar Laplacian of a periodic field has zero Haar mean.  This is now
proved for the same lifted Laplacian that occurs in the PDE. -/
theorem integral_torusScalarLaplacian_eq_zero
    (f : C(Torus3, ℝ))
    (hf : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 2 (torusCoordinateSliceLift f i y))
    (hint : ∀ i : Fin 3,
      Integrable (torusCoordinateSecondDerivative f i)) :
    (∫ x : Torus3, torusScalarLaplacian f x) = 0 := by
  calc
    (∫ x : Torus3, torusScalarLaplacian f x) =
        ∫ x : Torus3,
          ∑ i : Fin 3, torusCoordinateSecondDerivative f i x := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        torusScalarLaplacian_eq_sum_coordinateSecondDerivative f x
    _ = ∑ i : Fin 3,
        ∫ x : Torus3, torusCoordinateSecondDerivative f i x := by
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun i _hi => hint i)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      exact torus3_integral_coordinateSecondDerivative_eq_zero
        f i (hf i) (hint i)

/-- Haar-volume integration is a linear functional on continuous scalar fields
on the physical torus. -/
def torusIntegralLinearMap : C(Torus3, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x : Torus3, f x
  map_add' f g := by
    change (∫ x : Torus3, f x + g x) = _
    rw [MeasureTheory.integral_add]
    · simpa only [IntegrableOn, Measure.restrict_univ] using
        f.continuous.continuousOn.integrableOn_compact
          (μ := MeasureTheory.volume)
          (isCompact_univ : IsCompact (Set.univ : Set Torus3))
    · simpa only [IntegrableOn, Measure.restrict_univ] using
        g.continuous.continuousOn.integrableOn_compact
          (μ := MeasureTheory.volume)
          (isCompact_univ : IsCompact (Set.univ : Set Torus3))
  map_smul' c f := by
    change (∫ x : Torus3, c * f x) = c * ∫ x : Torus3, f x
    exact MeasureTheory.integral_const_mul c (fun x : Torus3 => f x)

@[simp]
theorem torusIntegralLinearMap_apply (f : C(Torus3, ℝ)) :
    torusIntegralLinearMap f = ∫ x : Torus3, f x := rfl

/-- Haar-volume integration is continuous for the sup norm on continuous
fields.  Its explicit bound is the volume of the torus. -/
def torusIntegralCLM : C(Torus3, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous torusIntegralLinearMap
    (MeasureTheory.volume.real Set.univ) fun f => by
      calc
        ‖∫ x : Torus3, f x‖ ≤ ‖f‖ * MeasureTheory.volume.real Set.univ :=
          norm_integral_le_of_norm_le_const
            (f := fun x : Torus3 => f x) (C := ‖f‖) (μ := MeasureTheory.volume)
            (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)
        _ = MeasureTheory.volume.real Set.univ * ‖f‖ := mul_comm _ _

@[simp]
theorem torusIntegralCLM_apply (f : C(Torus3, ℝ)) :
    torusIntegralCLM f = ∫ x : Torus3, f x := by
  change torusIntegralLinearMap f = ∫ x : Torus3, f x
  rfl

/-- The global half-enstrophy functional. -/
def torusEnstrophy (w : C(Torus3, Vec3)) : ℝ :=
  ∫ x : Torus3, vorticityEnergyField w x

/-- Pointwise palinstrophy density `|∇w|²` in the lifted coordinate frame. -/
def torusPalinstrophyDensity (w : C(Torus3, Vec3)) (x : Torus3) : ℝ :=
  torusLiftGradientSq w (torus3Representative x)

/-- Signed vortex-stretching production. -/
def torusStretchingProduction
    (u w : C(Torus3, Vec3)) (x : Torus3) : ℝ :=
  inner ℝ (w x) (torusStretching u w x)

/-- Sup-norm differentiability of vorticity rigorously differentiates the
global enstrophy integral. -/
theorem torusEnstrophy_hasDerivAt
    {ω : ℝ → C(Torus3, Vec3)} {ω' : C(Torus3, Vec3)} {t : ℝ}
    (hω : HasDerivAt ω ω' t) :
    HasDerivAt (fun s => torusEnstrophy (ω s))
      (∫ x : Torus3, inner ℝ (ω t x) (ω' x)) t := by
  have henergy := hω.vorticityEnergyField
  have hintegral := torusIntegralCLM.hasFDerivAt.comp_hasDerivAt t henergy
  have hfun :
      torusIntegralCLM ∘ (fun s => vorticityEnergyField (ω s)) =
        fun s => torusEnstrophy (ω s) := by
    funext s
    simp only [Function.comp_apply, torusIntegralCLM_apply, torusEnstrophy]
  rw [hfun] at hintegral
  simpa only [Function.comp_apply, torusIntegralCLM_apply, torusEnstrophy,
    vorticityEnergyField_apply, vorticityEnergyDerivativeField_apply] using hintegral

/-- The concrete classical vorticity interface therefore supplies a genuine
time derivative of global enstrophy at every interior time. -/
theorem IsClassicalVorticityEquationOn.hasDerivAt_torusEnstrophy
    {ν a b : ℝ} {u ω ωTime : ℝ → C(Torus3, Vec3)}
    (h : IsClassicalVorticityEquationOn ν a b u ω ωTime)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivAt (fun s => torusEnstrophy (ω s))
      (∫ x : Torus3, inner ℝ (ω t x) (ωTime t x)) t :=
  torusEnstrophy_hasDerivAt (h.2.2.1 t ht)

/-- Pair the concrete pointwise vorticity equation with vorticity and integrate.
This is already a global identity for every solution satisfying the repository's
classical vorticity predicate; no scalar evolution law is assumed separately. -/
theorem IsClassicalVorticityEquationOn.hasDerivAt_torusEnstrophy_paired
    {ν a b : ℝ} {u ω ωTime : ℝ → C(Torus3, Vec3)}
    (h : IsClassicalVorticityEquationOn ν a b u ω ωTime)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivAt (fun s => torusEnstrophy (ω s))
      (∫ x : Torus3, inner ℝ (ω t x)
        (torusStretching (u t) (ω t) x +
          ν • torusVectorLaplacian (ω t) x -
          torusTransport (u t) (ω t) x)) t := by
  apply (h.hasDerivAt_torusEnstrophy ht).congr_deriv
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [h.2.2.2.2 t ht x]

/-- Exact global enstrophy derivative with the diffusion product rule exposed:

`E' = ∫ stretching + ν Δ(|ω|²/2) - ν |∇ω|² - transport`.

The two periodic cancellation terms remain visible rather than being hidden in
an abstract scalar PDE hypothesis. -/
theorem IsClassicalVorticityEquationOn.hasDerivAt_torusEnstrophy_expanded
    {ν a b : ℝ} {u ω ωTime : ℝ → C(Torus3, Vec3)}
    (h : IsClassicalVorticityEquationOn ν a b u ω ωTime)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivAt (fun s => torusEnstrophy (ω s))
      (∫ x : Torus3,
        torusStretchingProduction (u t) (ω t) x +
          ν * torusScalarLaplacian (vorticityEnergyField (ω t)) x -
          ν * torusPalinstrophyDensity (ω t) x -
          torusVorticityTransportProduction (u t) (ω t) x) t := by
  apply (h.hasDerivAt_torusEnstrophy_paired ht).congr_deriv
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  have hdiff := inner_torusLiftVectorLaplacian_eq
    (ω t) (torus3Representative x) (h.2.2.2.1 t ⟨ht.1, ht.2.le⟩)
  have hlift : torusLift (ω t) (torus3Representative x) = ω t x := by
    simp [torusLift]
  rw [hlift] at hdiff
  simp only [torusStretchingProduction, torusVorticityTransportProduction,
    torusScalarLaplacian, torusPalinstrophyDensity, torusVectorLaplacian]
  rw [inner_sub_right, inner_add_right, real_inner_smul_right, hdiff]
  ring

/-- Once the two genuine periodic divergences have zero spatial mean, the
classical vorticity equation gives the clean enstrophy balance

`E' = ∫ ω·(ω·∇)u - ν∫|∇ω|²`.

Integrability is stated term-by-term so no use of linearity for undefined
Bochner integrals is hidden. -/
theorem IsClassicalVorticityEquationOn.hasDerivAt_torusEnstrophy_balance
    {ν a b : ℝ} {u ω ωTime : ℝ → C(Torus3, Vec3)}
    (h : IsClassicalVorticityEquationOn ν a b u ω ωTime)
    {t : ℝ} (ht : t ∈ Ico a b)
    (hS : Integrable (torusStretchingProduction (u t) (ω t)))
    (hL : Integrable
      (torusScalarLaplacian (vorticityEnergyField (ω t))))
    (hP : Integrable (torusPalinstrophyDensity (ω t)))
    (hT : Integrable (torusVorticityTransportProduction (u t) (ω t)))
    (hlap : (∫ x : Torus3,
      torusScalarLaplacian (vorticityEnergyField (ω t)) x) = 0)
    (htransport : (∫ x : Torus3,
      torusVorticityTransportProduction (u t) (ω t) x) = 0) :
    HasDerivAt (fun s => torusEnstrophy (ω s))
      (∫ x : Torus3,
        torusStretchingProduction (u t) (ω t) x -
          ν * torusPalinstrophyDensity (ω t) x) t := by
  apply (h.hasDerivAt_torusEnstrophy_expanded ht).congr_deriv
  let S : Torus3 → ℝ := torusStretchingProduction (u t) (ω t)
  let L : Torus3 → ℝ :=
    torusScalarLaplacian (vorticityEnergyField (ω t))
  let P : Torus3 → ℝ := torusPalinstrophyDensity (ω t)
  let T : Torus3 → ℝ := torusVorticityTransportProduction (u t) (ω t)
  have hSc : Integrable S := hS
  have hLc : Integrable L := hL
  have hPc : Integrable P := hP
  have hTc : Integrable T := hT
  change (∫ x : Torus3, ((((S + ν • L) - ν • P) - T) x)) =
    ∫ x : Torus3, ((S - ν • P) x)
  calc
    (∫ x : Torus3, ((((S + ν • L) - ν • P) - T) x)) =
        (∫ x : Torus3, (((S + ν • L) - ν • P) x)) -
          (∫ x : Torus3, T x) := by
      simpa only [Pi.sub_apply] using MeasureTheory.integral_sub
        ((hSc.add (hLc.smul ν)).sub (hPc.smul ν)) hTc
    _ = (((∫ x : Torus3, ((S + ν • L) x)) -
          (∫ x : Torus3, ((ν • P) x))) -
          (∫ x : Torus3, T x)) := by
      congr 1
      simpa only [Pi.sub_apply] using MeasureTheory.integral_sub
        (hSc.add (hLc.smul ν)) (hPc.smul ν)
    _ = ((((∫ x : Torus3, S x) +
          (∫ x : Torus3, ((ν • L) x))) -
          (∫ x : Torus3, ((ν • P) x))) -
          (∫ x : Torus3, T x)) := by
      congr 2
      simpa only [Pi.add_apply] using MeasureTheory.integral_add hSc (hLc.smul ν)
    _ = (((∫ x : Torus3, S x) + ν * (∫ x : Torus3, L x) -
          ν * (∫ x : Torus3, P x)) - (∫ x : Torus3, T x)) := by
      simp only [Pi.smul_apply, smul_eq_mul, MeasureTheory.integral_const_mul]
    _ = (∫ x : Torus3, S x) - ν * (∫ x : Torus3, P x) := by
      change ((∫ x : Torus3, S x) +
        ν * (∫ x : Torus3,
          torusScalarLaplacian (vorticityEnergyField (ω t)) x) -
        ν * (∫ x : Torus3, P x)) -
        (∫ x : Torus3,
          torusVorticityTransportProduction (u t) (ω t) x) = _
      rw [hlap, htransport]
      ring
    _ = ∫ x : Torus3, ((S - ν • P) x) := by
      symm
      calc
        (∫ x : Torus3, ((S - ν • P) x)) =
            (∫ x : Torus3, S x) - (∫ x : Torus3, ((ν • P) x)) := by
          simpa only [Pi.sub_apply] using
            MeasureTheory.integral_sub hSc (hPc.smul ν)
        _ = (∫ x : Torus3, S x) - ν * (∫ x : Torus3, P x) := by
          simp only [Pi.smul_apply, smul_eq_mul,
            MeasureTheory.integral_const_mul]

/-- Fully assemble the clean enstrophy balance from the concrete classical
Navier--Stokes and vorticity predicates plus ordinary smoothness/integrability
obligations.  Neither periodic cancellation is assumed as an equality here:
both are derived above from Haar integration by parts. -/
theorem hasDerivAt_torusEnstrophy_balance_of_classicalNavierStokes
    {ν a b : ℝ}
    {u uTime ω ωTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsClassicalNavierStokesOn ν a b u uTime p)
    (hω : IsClassicalVorticityEquationOn ν a b u ω ωTime)
    {t : ℝ} (ht : t ∈ Ico a b)
    (hS : Integrable (torusStretchingProduction (u t) (ω t)))
    (hL : Integrable
      (torusScalarLaplacian (vorticityEnergyField (ω t))))
    (hP : Integrable (torusPalinstrophyDensity (ω t)))
    (hT : Integrable (torusVorticityTransportProduction (u t) (ω t)))
    (henergySlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 2
        (torusCoordinateSliceLift (vorticityEnergyField (ω t)) i y))
    (hsecond : ∀ i : Fin 3, Integrable
      (torusCoordinateSecondDerivative (vorticityEnergyField (ω t)) i))
    (huSlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u t x i) i y))
    (htransportLeft : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      (((1 : ℝ) * u t x i) *
        torusCoordinateDerivative (vorticityEnergyField (ω t)) i x)))
    (htransportRight : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => (1 : ℝ) * u t z i) i x *
        vorticityEnergyField (ω t) x)) :
    HasDerivAt (fun s => torusEnstrophy (ω s))
      (∫ x : Torus3,
        torusStretchingProduction (u t) (ω t) x -
          ν * torusPalinstrophyDensity (ω t) x) t := by
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have hw : ContDiff ℝ 1 (torusLift (ω t)) :=
    (hω.2.2.2.1 t htcc).of_le (by norm_num)
  apply hω.hasDerivAt_torusEnstrophy_balance ht hS hL hP hT
  · exact integral_torusScalarLaplacian_eq_zero
      (vorticityEnergyField (ω t)) henergySlices hsecond
  · exact integral_torusVorticityTransportProduction_eq_zero
      (u t) (ω t) hw huSlices
      (fun i y => (henergySlices i y).of_le (by norm_num))
      htransportLeft htransportRight
      (fun x => hNS.torusCoordinateDivergence_eq_zero htcc x)

/-! ## Quotient-weighted production for the concrete PDE balance -/

/-- The stretching density in the PDE enstrophy balance is exactly the
coordinate-model density used by the zero-safe self-transport quotient theory. -/
theorem torusStretchingProduction_eq_periodicVortexStretchingDensity
    (u w : C(Torus3, Vec3)) (x : Torus3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    torusStretchingProduction u w x =
      periodicVortexStretchingDensity u w x := by
  simp only [torusStretchingProduction, torusStretching,
    torusDirectionalDerivative_eq_sum_partial, inner_sum,
    real_inner_smul_right, periodicVortexStretchingDensity,
    torusScalarTransport]
  have hcomponent : ∀ i j : Fin 3,
      torusCoordinateDerivative (fun y => u y i) j x =
        torusPartial u x j i := fun i j =>
    torusCoordinateDerivative_component_eq_torusPartial u j i x hu
  simp_rw [hcomponent]
  simp only [PiLp.inner_apply, Real.inner_apply]
  simp [Fin.sum_univ_three]
  ring

/-- The narrowest quotient/weighted-variance factorization now bounds the
actual stretching term appearing in the concrete enstrophy derivative. -/
theorem sq_integral_torusStretchingProduction_le_selfTransportQuotient_weightedVariance
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (huLift : ContDiff ℝ 1 (torusLift u))
    (hwTransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => w x j) j y))
    (hwSlices : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => w x i) j y))
    (huCentered : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun x => centeredVelocity u frame x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((w x i) * w x j) * periodicFirstDerivative u j i x))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => w z i * w z j) j x *
        centeredVelocity u frame x i))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hquotient : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq w x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 =>
      ‖w x‖ * ‖centeredVelocity u frame x‖) 2 volume)
    (hcomponents : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight w x * (u x j - frame j) ^ 2)) :
    (∫ x : Torus3, torusStretchingProduction u w x) ^ 2 ≤
      (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq w x) *
        periodicVorticityWeightedVelocityVariance u w frame := by
  have hkinematic :=
    sq_integral_periodicVortexStretching_le_selfTransportQuotient_weightedVariance
      u w frame hwTransport hwSlices huCentered hleft hright hdiv
      hquotient hvariance hcomponents
  have hdensity :
      (∫ x : Torus3, torusStretchingProduction u w x) =
        ∫ x : Torus3, periodicVortexStretchingDensity u w x := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x =>
      torusStretchingProduction_eq_periodicVortexStretchingDensity u w x huLift
  rw [hdensity]
  exact hkinematic
