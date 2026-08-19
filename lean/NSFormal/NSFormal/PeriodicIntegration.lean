import NSFormal.Domain
import NSFormal.ForTauCeti.PeriodicIntegration

/-!
# Periodic integration by parts

This file supplies the first concrete spatial-integration layer for the torus
argument.  The boundary cancellation is proved on a fundamental interval and
then transported, using Mathlib's measure-preserving identification, to the
actual Haar-volume integral on `AddCircle T`.
-/

open Function MeasureTheory Set
open scoped Interval

noncomputable section

/-- The integral of a derivative over one period vanishes.  This is the
one-dimensional boundary cancellation underlying periodic divergence
identities. -/
theorem intervalIntegral_deriv_eq_zero_of_periodic
    {T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T) (hf : ContDiff ℝ 1 f)
    (hper : Periodic f T) :
    ∫ x in (0 : ℝ)..T, deriv f x = 0 :=
  ForTauCeti.intervalIntegral_deriv_eq_zero_of_periodic hT hf hper

/-- Integration by parts over one period, with the endpoint terms cancelled
by genuine periodicity rather than by an abstract skew-adjointness axiom. -/
theorem intervalIntegral_mul_deriv_eq_neg_deriv_mul_of_periodic
    {T : ℝ} {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfper : Periodic f T) (hgper : Periodic g T) :
    ∫ x in (0 : ℝ)..T, f x * deriv g x =
      -∫ x in (0 : ℝ)..T, deriv f x * g x :=
  ForTauCeti.intervalIntegral_mul_deriv_eq_neg_deriv_mul_of_periodic
    hf hg hfper hgper

/-- The same integration-by-parts identity as an equality of integrals over
the concrete measured circle.  `liftIoc` merely chooses the standard
fundamental-domain representative; Mathlib proves its circle integral equals
the interval integral. -/
theorem addCircle_integral_mul_deriv_eq_neg_deriv_mul_of_periodic
    {T : ℝ} [Fact (0 < T)] {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfper : Periodic f T) (hgper : Periodic g T) :
    (∫ x : AddCircle T,
        AddCircle.liftIoc T 0 (fun r => f r * deriv g r) x) =
      -(∫ x : AddCircle T,
        AddCircle.liftIoc T 0 (fun r => deriv f r * g r) x) :=
  ForTauCeti.addCircle_integral_mul_deriv_eq_neg_deriv_mul_of_periodic
    hf hg hfper hgper

/-- A concrete nonconstant smooth periodic field witnesses that the preceding
interfaces are not vacuous. -/
theorem exists_nonconstant_smooth_two_pi_periodic :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ 1 f ∧ Periodic f ((2 : ℝ) * Real.pi) ∧
        f 0 ≠ f (Real.pi / 2) := by
  refine ⟨Real.sin, Real.contDiff_sin, Real.sin_periodic, ?_⟩
  simp

/-- A fully concrete measured-circle instance of periodic integration by
parts, using the nonconstant sine and cosine modes. -/
theorem sine_cosine_addCircle_integration_by_parts :
    (∫ x : AddCircle ((2 : ℝ) * Real.pi),
        AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
          (fun r => Real.sin r * deriv Real.cos r) x) =
      -(∫ x : AddCircle ((2 : ℝ) * Real.pi),
        AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
          (fun r => deriv Real.sin r * Real.cos r) x) := by
  exact addCircle_integral_mul_deriv_eq_neg_deriv_mul_of_periodic
    Real.contDiff_sin Real.contDiff_cos Real.sin_periodic Real.cos_periodic

/-! ## Coordinate slices of the physical three-torus -/

/-- The two coordinates complementary to a selected coordinate of `Torus3`. -/
abbrev TorusCoordinateComplement :=
  Fin 2 → AddCircle ((2 : ℝ) * Real.pi)

/-- Restrict a scalar torus field to the coordinate circle selected by `i`,
with the other two coordinates fixed by `y`. -/
def torusCoordinateSlice
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (a : AddCircle ((2 : ℝ) * Real.pi)) : ℝ :=
  f (i.insertNth a y)

/-- Lift a coordinate slice to its `2π`-periodic real parametrization. -/
def torusCoordinateSliceLift
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement) (r : ℝ) : ℝ :=
  torusCoordinateSlice f i y (r : AddCircle ((2 : ℝ) * Real.pi))

theorem torusCoordinateSliceLift_periodic
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement) :
    Periodic (torusCoordinateSliceLift f i y) ((2 : ℝ) * Real.pi) := by
  intro r
  apply congrArg f
  rw [Fin.insertNth_inj]
  exact ⟨by simp, rfl⟩

/-- The coordinate derivative on the measured circle, obtained by
differentiating the smooth periodic lift and descending through a fundamental
domain. -/
def torusCoordinateSliceDerivative
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (a : AddCircle ((2 : ℝ) * Real.pi)) : ℝ :=
  AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
    (deriv (torusCoordinateSliceLift f i y)) a

theorem liftIoc_torusCoordinateSliceLift
    (f : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (a : AddCircle ((2 : ℝ) * Real.pi)) :
    AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
        (torusCoordinateSliceLift f i y) a =
      torusCoordinateSlice f i y a := by
  change f (i.insertNth
      ((AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 a).1 :
        AddCircle ((2 : ℝ) * Real.pi)) y) = f (i.insertNth a y)
  rw [AddCircle.coe_equivIoc]

theorem liftIoc_mul
    {T : ℝ} [Fact (0 < T)] (f g : ℝ → ℝ) (a : AddCircle T) :
    AddCircle.liftIoc T 0 (fun r => f r * g r) a =
      AddCircle.liftIoc T 0 f a * AddCircle.liftIoc T 0 g a := by
  rfl

/-- Periodic integration by parts on every genuine coordinate circle of the
physical three-torus. -/
theorem torusCoordinateSlice_integration_by_parts
    (f g : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (hf : ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hg : ContDiff ℝ 1 (torusCoordinateSliceLift g i y)) :
    (∫ a : AddCircle ((2 : ℝ) * Real.pi),
        torusCoordinateSlice f i y a * torusCoordinateSliceDerivative g i y a) =
      -(∫ a : AddCircle ((2 : ℝ) * Real.pi),
        torusCoordinateSliceDerivative f i y a * torusCoordinateSlice g i y a) := by
  have h := addCircle_integral_mul_deriv_eq_neg_deriv_mul_of_periodic
    hf hg (torusCoordinateSliceLift_periodic f i y)
      (torusCoordinateSliceLift_periodic g i y)
  simpa only [liftIoc_mul, liftIoc_torusCoordinateSliceLift,
    torusCoordinateSliceDerivative] using h

/-- Integrating the coordinate-circle identity over the two complementary
torus coordinates gives the corresponding iterated three-dimensional
identity. -/
theorem torusCoordinate_iterated_integration_by_parts
    (f g : Torus3 → ℝ) (i : Fin 3)
    (hf : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hg : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift g i y)) :
    (∫ y : TorusCoordinateComplement,
      ∫ a : AddCircle ((2 : ℝ) * Real.pi),
        torusCoordinateSlice f i y a * torusCoordinateSliceDerivative g i y a) =
      -(∫ y : TorusCoordinateComplement,
        ∫ a : AddCircle ((2 : ℝ) * Real.pi),
          torusCoordinateSliceDerivative f i y a * torusCoordinateSlice g i y a) := by
  simp_rw [torusCoordinateSlice_integration_by_parts f g i _ (hf _) (hg _)]
  exact MeasureTheory.integral_neg _

/-- The coordinate derivative as a scalar field on all of `Torus3`. -/
def torusCoordinateDerivative (f : Torus3 → ℝ) (i : Fin 3) (x : Torus3) : ℝ :=
  torusCoordinateSliceDerivative f i (Fin.removeNth i x) (x i)

@[simp]
theorem torusCoordinateDerivative_const (c : ℝ) (i : Fin 3) (x : Torus3) :
    torusCoordinateDerivative (fun _ : Torus3 => c) i x = 0 := by
  have hfun :
      torusCoordinateSliceLift (fun _ : Torus3 => c) i (Fin.removeNth i x) =
        fun _ : ℝ => c := by rfl
  rw [torusCoordinateDerivative, torusCoordinateSliceDerivative, hfun]
  rw [deriv_const']
  rfl

/-- The volume measure on `Torus3` splits, at any selected coordinate, into
the circle measure and the volume on the two complementary circles. -/
theorem torus3_volume_preserving_coordinate_split (i : Fin 3) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin 3 => AddCircle ((2 : ℝ) * Real.pi)) i) :=
  volume_preserving_piFinSuccAbove
    (fun _ : Fin 3 => AddCircle ((2 : ℝ) * Real.pi)) i

/-- Concrete three-dimensional periodic integration by parts for scalar
fields on `Torus3`.  The integrability assumptions are exactly the hypotheses
needed by Fubini; the skew identity itself is supplied on every coordinate
circle by the preceding theorem. -/
theorem torus3_integral_mul_coordinateDerivative_eq_neg
    (f g : Torus3 → ℝ) (i : Fin 3)
    (hf : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hg : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift g i y))
    (hfg : Integrable (fun x : Torus3 => f x * torusCoordinateDerivative g i x))
    (hgf : Integrable (fun x : Torus3 => torusCoordinateDerivative f i x * g x)) :
    (∫ x : Torus3, f x * torusCoordinateDerivative g i x) =
      -(∫ x : Torus3, torusCoordinateDerivative f i x * g x) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin 3 => AddCircle ((2 : ℝ) * Real.pi)) i
  have he : MeasurePreserving e := torus3_volume_preserving_coordinate_split i
  have hesymm : MeasurePreserving e.symm := MeasurePreserving.symm e he
  have hfg' : Integrable
      ((fun x : Torus3 => f x * torusCoordinateDerivative g i x) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hfg
  have hgf' : Integrable
      ((fun x : Torus3 => torusCoordinateDerivative f i x * g x) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hgf
  calc
    (∫ x : Torus3, f x * torusCoordinateDerivative g i x) =
        ∫ z : AddCircle ((2 : ℝ) * Real.pi) × TorusCoordinateComplement,
          ((fun x : Torus3 => f x * torusCoordinateDerivative g i x) ∘ e.symm) z := by
      symm
      exact hesymm.integral_comp'
        (fun x : Torus3 => f x * torusCoordinateDerivative g i x)
    _ = ∫ y : TorusCoordinateComplement,
        ∫ a : AddCircle ((2 : ℝ) * Real.pi),
          torusCoordinateSlice f i y a * torusCoordinateSliceDerivative g i y a := by
      rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hfg']
      simp [e, torusCoordinateDerivative, torusCoordinateSlice,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    _ = -(∫ y : TorusCoordinateComplement,
        ∫ a : AddCircle ((2 : ℝ) * Real.pi),
          torusCoordinateSliceDerivative f i y a * torusCoordinateSlice g i y a) :=
      torusCoordinate_iterated_integration_by_parts f g i hf hg
    _ = -(∫ z : AddCircle ((2 : ℝ) * Real.pi) × TorusCoordinateComplement,
        ((fun x : Torus3 => torusCoordinateDerivative f i x * g x) ∘ e.symm) z) := by
      rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hgf']
      simp [e, torusCoordinateDerivative, torusCoordinateSlice,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    _ = -(∫ x : Torus3, torusCoordinateDerivative f i x * g x) := by
      exact congrArg Neg.neg (hesymm.integral_comp'
        (fun x : Torus3 => torusCoordinateDerivative f i x * g x))

theorem liftIoc_add
    {T : ℝ} [Fact (0 < T)] (f g : ℝ → ℝ) (a : AddCircle T) :
    AddCircle.liftIoc T 0 (fun r => f r + g r) a =
      AddCircle.liftIoc T 0 f a + AddCircle.liftIoc T 0 g a := by
  rfl

theorem liftIoc_sub
    {T : ℝ} [Fact (0 < T)] (f g : ℝ → ℝ) (a : AddCircle T) :
    AddCircle.liftIoc T 0 (fun r => f r - g r) a =
      AddCircle.liftIoc T 0 f a - AddCircle.liftIoc T 0 g a := by
  rfl

theorem liftIoc_div
    {T : ℝ} [Fact (0 < T)] (f g : ℝ → ℝ) (a : AddCircle T) :
    AddCircle.liftIoc T 0 (fun r => f r / g r) a =
      AddCircle.liftIoc T 0 f a / AddCircle.liftIoc T 0 g a := by
  rfl

/-- The concrete coordinate derivative is additive on smooth slices. -/
theorem torusCoordinateDerivative_add
    (f g : Torus3 → ℝ) (i : Fin 3) (x : Torus3)
    (hf : ContDiff ℝ 1 (torusCoordinateSliceLift f i (Fin.removeNth i x)))
    (hg : ContDiff ℝ 1 (torusCoordinateSliceLift g i (Fin.removeNth i x))) :
    torusCoordinateDerivative (fun z => f z + g z) i x =
      torusCoordinateDerivative f i x + torusCoordinateDerivative g i x := by
  unfold torusCoordinateDerivative torusCoordinateSliceDerivative
  rw [show torusCoordinateSliceLift (fun z => f z + g z) i (Fin.removeNth i x) =
      fun r => torusCoordinateSliceLift f i (Fin.removeNth i x) r +
        torusCoordinateSliceLift g i (Fin.removeNth i x) r by rfl]
  have hderiv : deriv (fun r =>
      torusCoordinateSliceLift f i (Fin.removeNth i x) r +
        torusCoordinateSliceLift g i (Fin.removeNth i x) r) =
      fun r => deriv (torusCoordinateSliceLift f i (Fin.removeNth i x)) r +
        deriv (torusCoordinateSliceLift g i (Fin.removeNth i x)) r := by
    funext r
    exact (((hf.differentiable one_ne_zero).differentiableAt.hasDerivAt).add
      ((hg.differentiable one_ne_zero).differentiableAt.hasDerivAt)).deriv
  rw [hderiv, liftIoc_add]

/-- The concrete coordinate derivative respects subtraction on smooth slices. -/
theorem torusCoordinateDerivative_sub
    (f g : Torus3 → ℝ) (i : Fin 3) (x : Torus3)
    (hf : ContDiff ℝ 1 (torusCoordinateSliceLift f i (Fin.removeNth i x)))
    (hg : ContDiff ℝ 1 (torusCoordinateSliceLift g i (Fin.removeNth i x))) :
    torusCoordinateDerivative (fun z => f z - g z) i x =
      torusCoordinateDerivative f i x - torusCoordinateDerivative g i x := by
  unfold torusCoordinateDerivative torusCoordinateSliceDerivative
  rw [show torusCoordinateSliceLift (fun z => f z - g z) i (Fin.removeNth i x) =
      fun r => torusCoordinateSliceLift f i (Fin.removeNth i x) r -
        torusCoordinateSliceLift g i (Fin.removeNth i x) r by rfl]
  have hderiv : deriv (fun r =>
      torusCoordinateSliceLift f i (Fin.removeNth i x) r -
        torusCoordinateSliceLift g i (Fin.removeNth i x) r) =
      fun r => deriv (torusCoordinateSliceLift f i (Fin.removeNth i x)) r -
        deriv (torusCoordinateSliceLift g i (Fin.removeNth i x)) r := by
    funext r
    exact (((hf.differentiable one_ne_zero).differentiableAt.hasDerivAt).sub
      ((hg.differentiable one_ne_zero).differentiableAt.hasDerivAt)).deriv
  rw [hderiv, liftIoc_sub]

/-- Quotient rule for the concrete coordinate derivative. -/
theorem torusCoordinateDerivative_div
    (f g : Torus3 → ℝ) (i : Fin 3) (x : Torus3)
    (hf : ContDiff ℝ 1 (torusCoordinateSliceLift f i (Fin.removeNth i x)))
    (hg : ContDiff ℝ 1 (torusCoordinateSliceLift g i (Fin.removeNth i x)))
    (hg0 : g x ≠ 0) :
    torusCoordinateDerivative (fun z => f z / g z) i x =
      (torusCoordinateDerivative f i x * g x -
        f x * torusCoordinateDerivative g i x) / g x ^ 2 := by
  unfold torusCoordinateDerivative torusCoordinateSliceDerivative
  rw [show torusCoordinateSliceLift (fun z => f z / g z) i (Fin.removeNth i x) =
      fun r => torusCoordinateSliceLift f i (Fin.removeNth i x) r /
        torusCoordinateSliceLift g i (Fin.removeNth i x) r by rfl]
  have hg0' : torusCoordinateSliceLift g i (Fin.removeNth i x)
      (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x i)).1 ≠ 0 := by
    simpa [torusCoordinateSliceLift, torusCoordinateSlice] using hg0
  let r := (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x i)).1
  change deriv (fun s =>
      torusCoordinateSliceLift f i (Fin.removeNth i x) s /
        torusCoordinateSliceLift g i (Fin.removeNth i x) s) r = _
  have hfval : torusCoordinateSliceLift f i (Fin.removeNth i x) r = f x := by
    simp [r, torusCoordinateSliceLift, torusCoordinateSlice]
  have hgval : torusCoordinateSliceLift g i (Fin.removeNth i x) r = g x := by
    simp [r, torusCoordinateSliceLift, torusCoordinateSlice]
  rw [← hfval, ← hgval]
  exact (((hf.differentiable one_ne_zero).differentiableAt.hasDerivAt).div
    ((hg.differentiable one_ne_zero).differentiableAt.hasDerivAt) hg0').deriv

/-- The descended coordinate derivative obeys the genuine Leibniz rule on a
smooth torus coordinate slice. -/
theorem torusCoordinateSliceDerivative_mul
    (f g : Torus3 → ℝ) (i : Fin 3) (y : TorusCoordinateComplement)
    (a : AddCircle ((2 : ℝ) * Real.pi))
    (hf : ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hg : ContDiff ℝ 1 (torusCoordinateSliceLift g i y)) :
    torusCoordinateSliceDerivative (fun x => f x * g x) i y a =
      torusCoordinateSliceDerivative f i y a * torusCoordinateSlice g i y a +
        torusCoordinateSlice f i y a * torusCoordinateSliceDerivative g i y a := by
  have hderiv :
      deriv (torusCoordinateSliceLift (fun x => f x * g x) i y) =
        fun r =>
          deriv (torusCoordinateSliceLift f i y) r * torusCoordinateSliceLift g i y r +
            torusCoordinateSliceLift f i y r * deriv (torusCoordinateSliceLift g i y) r := by
    funext r
    change deriv
        (fun s => torusCoordinateSliceLift f i y s * torusCoordinateSliceLift g i y s) r = _
    exact (((hf.differentiable one_ne_zero).differentiableAt.hasDerivAt).mul
      ((hg.differentiable one_ne_zero).differentiableAt.hasDerivAt)).deriv
  rw [torusCoordinateSliceDerivative, hderiv, liftIoc_add, liftIoc_mul, liftIoc_mul]
  simp only [torusCoordinateSliceDerivative, liftIoc_torusCoordinateSliceLift]

/-- Global pointwise Leibniz rule for the concrete coordinate derivative on
`Torus3`. -/
theorem torusCoordinateDerivative_mul
    (f g : Torus3 → ℝ) (i : Fin 3) (x : Torus3)
    (hf : ContDiff ℝ 1 (torusCoordinateSliceLift f i (Fin.removeNth i x)))
    (hg : ContDiff ℝ 1 (torusCoordinateSliceLift g i (Fin.removeNth i x))) :
    torusCoordinateDerivative (fun z => f z * g z) i x =
      torusCoordinateDerivative f i x * g x +
        f x * torusCoordinateDerivative g i x := by
  simpa [torusCoordinateDerivative, torusCoordinateSlice] using
    torusCoordinateSliceDerivative_mul f g i (Fin.removeNth i x) (x i) hf hg

/-- Leibniz rule for a product of three scalar fields.  This is the exact product expansion
needed when the variable-direction anisotropic identity differentiates
`e_j * (∂ₖ uᵢ) * e_k`. -/
theorem torusCoordinateDerivative_mul_three
    (a b c : Torus3 → ℝ) (i : Fin 3) (x : Torus3)
    (ha : ContDiff ℝ 1 (torusCoordinateSliceLift a i (Fin.removeNth i x)))
    (hb : ContDiff ℝ 1 (torusCoordinateSliceLift b i (Fin.removeNth i x)))
    (hc : ContDiff ℝ 1 (torusCoordinateSliceLift c i (Fin.removeNth i x))) :
    torusCoordinateDerivative (fun z => (a z * b z) * c z) i x =
      (torusCoordinateDerivative a i x * b x) * c x +
        (a x * torusCoordinateDerivative b i x) * c x +
          (a x * b x) * torusCoordinateDerivative c i x := by
  have hab : ContDiff ℝ 1
      (torusCoordinateSliceLift (fun z => a z * b z) i (Fin.removeNth i x)) :=
    ha.mul hb
  rw [torusCoordinateDerivative_mul (fun z => a z * b z) c i x hab hc]
  rw [torusCoordinateDerivative_mul a b i x ha hb]
  ring

/-- Periodic integration by parts with the full three-factor derivative visible.  This is a
componentwise, concrete-Haar-measure version of the differential step in the variable-direction
anisotropic ledger; the middle term is the one later cancelled after summing by differentiated
incompressibility. -/
theorem torus3_integral_coordinateDerivative_mul_three_eq_neg
    (f a b c : Torus3 → ℝ) (i : Fin 3)
    (hf : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (ha : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift a i y))
    (hb : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift b i y))
    (hc : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift c i y))
    (hleft : Integrable (fun x : Torus3 =>
      torusCoordinateDerivative f i x * ((a x * b x) * c x)))
    (hright : Integrable (fun x : Torus3 => f x *
      (((torusCoordinateDerivative a i x * b x) * c x +
        (a x * torusCoordinateDerivative b i x) * c x +
          (a x * b x) * torusCoordinateDerivative c i x)))) :
    (∫ x : Torus3,
      torusCoordinateDerivative f i x * ((a x * b x) * c x)) =
      -(∫ x : Torus3, f x *
        (((torusCoordinateDerivative a i x * b x) * c x +
          (a x * torusCoordinateDerivative b i x) * c x +
            (a x * b x) * torusCoordinateDerivative c i x))) := by
  let g : Torus3 → ℝ := fun x => (a x * b x) * c x
  have hg : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift g i y) := by
    intro y
    exact ((ha y).mul (hb y)).mul (hc y)
  have hderiv : ∀ x : Torus3,
      torusCoordinateDerivative g i x =
        (torusCoordinateDerivative a i x * b x) * c x +
          (a x * torusCoordinateDerivative b i x) * c x +
            (a x * b x) * torusCoordinateDerivative c i x := by
    intro x
    exact torusCoordinateDerivative_mul_three a b c i x (ha _) (hb _) (hc _)
  have hfg : Integrable (fun x : Torus3 =>
      f x * torusCoordinateDerivative g i x) := by
    apply hright.congr
    filter_upwards with x
    rw [hderiv x]
  have hgf : Integrable (fun x : Torus3 =>
      torusCoordinateDerivative f i x * g x) := by
    simpa only [g] using hleft
  have hparts := torus3_integral_mul_coordinateDerivative_eq_neg
    f g i hf hg hfg hgf
  have hreverse :
      (∫ x : Torus3, torusCoordinateDerivative f i x * g x) =
        -(∫ x : Torus3, f x * torusCoordinateDerivative g i x) := by
    linarith
  calc
    (∫ x : Torus3,
        torusCoordinateDerivative f i x * ((a x * b x) * c x)) =
        (∫ x : Torus3, torusCoordinateDerivative f i x * g x) := by rfl
    _ = -(∫ x : Torus3, f x * torusCoordinateDerivative g i x) := hreverse
    _ = -(∫ x : Torus3, f x *
        (((torusCoordinateDerivative a i x * b x) * c x +
          (a x * torusCoordinateDerivative b i x) * c x +
            (a x * b x) * torusCoordinateDerivative c i x))) := by
      congr 2
      funext x
      rw [hderiv x]

/-- One coordinate of the periodic transport integration-by-parts formula.
The second term on the right is the corresponding contribution to
`(div u) f g`; it is retained explicitly, so incompressibility can later
cancel it rather than being hidden in an axiom. -/
theorem torus3_transport_component_integration_by_parts
    (b f g : Torus3 → ℝ) (i : Fin 3)
    (hb : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift b i y))
    (hf : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hg : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift g i y))
    (hleft : Integrable (fun x : Torus3 =>
      (f x * b x) * torusCoordinateDerivative g i x))
    (hright : Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => f z * b z) i x * g x)) :
    (∫ x : Torus3, (f x * b x) * torusCoordinateDerivative g i x) =
      -(∫ x : Torus3,
        (torusCoordinateDerivative f i x * b x +
          f x * torusCoordinateDerivative b i x) * g x) := by
  have hprod : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => f x * b x) i y) := by
    intro y
    exact (hf y).mul (hb y)
  have hparts := torus3_integral_mul_coordinateDerivative_eq_neg
    (fun x => f x * b x) g i hprod hg hleft hright
  calc
    (∫ x : Torus3, (f x * b x) * torusCoordinateDerivative g i x) =
        -(∫ x : Torus3,
          torusCoordinateDerivative (fun z => f z * b z) i x * g x) := hparts
    _ = -(∫ x : Torus3,
        (torusCoordinateDerivative f i x * b x +
          f x * torusCoordinateDerivative b i x) * g x) := by
      congr 2
      funext x
      rw [torusCoordinateDerivative_mul f b i x (hf _) (hb _)]

/-- Coordinate expression for transport by a vector field on the physical
torus. -/
def torusScalarTransport (u : Torus3 → Vec3) (f : Torus3 → ℝ) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, u x i * torusCoordinateDerivative f i x

/-- Coordinate divergence of a vector field on the physical torus. -/
def torusCoordinateDivergence (u : Torus3 → Vec3) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, torusCoordinateDerivative (fun z => u z i) i x

/-- The full periodic transport identity
`∫ f (u·∇g) = -∫ ((u·∇f) + f div u) g` on the concrete three-torus. -/
theorem torus3_transport_integration_by_parts
    (u : Torus3 → Vec3) (f g : Torus3 → ℝ)
    (hu : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) i y))
    (hf : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hg : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift g i y))
    (hleft : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      (f x * u x i) * torusCoordinateDerivative g i x))
    (hright : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => f z * u z i) i x * g x)) :
    (∫ x : Torus3, f x * torusScalarTransport u g x) =
      -(∫ x : Torus3,
        (torusScalarTransport u f x + f x * torusCoordinateDivergence u x) * g x) := by
  have hprod : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => f x * u x i) i y) := by
    intro i y
    exact (hf i y).mul (hu i y)
  have hcomponent : ∀ i : Fin 3,
      (∫ x : Torus3, (f x * u x i) * torusCoordinateDerivative g i x) =
        -(∫ x : Torus3,
          torusCoordinateDerivative (fun z => f z * u z i) i x * g x) := by
    intro i
    exact torus3_integral_mul_coordinateDerivative_eq_neg
      (fun x => f x * u x i) g i (hprod i) (hg i) (hleft i) (hright i)
  calc
    (∫ x : Torus3, f x * torusScalarTransport u g x) =
        ∫ x : Torus3,
          ∑ i : Fin 3, (f x * u x i) * torusCoordinateDerivative g i x := by
      congr 1
      funext x
      simp only [torusScalarTransport, Finset.mul_sum]
      ring_nf
    _ = ∑ i : Fin 3,
        ∫ x : Torus3, (f x * u x i) * torusCoordinateDerivative g i x := by
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun i _hi => hleft i)
    _ = ∑ i : Fin 3,
        -(∫ x : Torus3,
          torusCoordinateDerivative (fun z => f z * u z i) i x * g x) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcomponent i
    _ = -(∑ i : Fin 3,
        ∫ x : Torus3,
          torusCoordinateDerivative (fun z => f z * u z i) i x * g x) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∫ x : Torus3,
        ∑ i : Fin 3,
          torusCoordinateDerivative (fun z => f z * u z i) i x * g x) := by
      rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun i _hi => hright i)]
    _ = -(∫ x : Torus3,
        (torusScalarTransport u f x + f x * torusCoordinateDivergence u x) * g x) := by
      congr 2
      funext x
      calc
        (∑ i : Fin 3,
            torusCoordinateDerivative (fun z => f z * u z i) i x * g x) =
            ∑ i : Fin 3,
              (torusCoordinateDerivative f i x * u x i +
                f x * torusCoordinateDerivative (fun z => u z i) i x) * g x := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [torusCoordinateDerivative_mul f (fun z => u z i) i x
            (hf i _) (hu i _)]
        _ = (torusScalarTransport u f x + f x * torusCoordinateDivergence u x) * g x := by
          simp only [torusScalarTransport, torusCoordinateDivergence]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [← Finset.sum_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          · rw [← Finset.sum_mul, Finset.mul_sum]

/-- For an incompressible vector field, the concrete periodic transport
operator is skew-adjoint in the volume pairing. -/
theorem torus3_divergenceFree_transport_skew
    (u : Torus3 → Vec3) (f g : Torus3 → ℝ)
    (hu : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) i y))
    (hf : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift f i y))
    (hg : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift g i y))
    (hleft : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      (f x * u x i) * torusCoordinateDerivative g i x))
    (hright : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => f z * u z i) i x * g x))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0) :
    (∫ x : Torus3, f x * torusScalarTransport u g x) =
      -(∫ x : Torus3, torusScalarTransport u f x * g x) := by
  rw [torus3_transport_integration_by_parts u f g hu hf hg hleft hright]
  congr 2
  funext x
  rw [hdiv]
  ring
