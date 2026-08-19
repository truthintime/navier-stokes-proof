/-
Copyright (c) 2026 The navier-stokes-proof contributors. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Periodic integration seeds for Tau Ceti

This file isolates the representation-independent kernel of the concrete periodic integration
work in `NSFormal.PeriodicIntegration` and generalizes its scalar product-torus theorem from the
period-`2π` three-torus to the normalized unit torus in arbitrary positive finite dimension.

It is an extraction seed, not a second public Sobolev API.  The derivative below is still a
classical coordinate derivative obtained from a periodic real lift.  The eventual Tau Ceti
interface should hide the half-open representative and connect this smooth result to intrinsic
periodic weak derivatives.
-/

open Function MeasureTheory Set
open scoped Interval

noncomputable section

namespace ForTauCeti

section Circle

/-- The integral of a derivative over one period vanishes. -/
theorem intervalIntegral_deriv_eq_zero_of_periodic
    {T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T) (hf : ContDiff ℝ 1 f)
    (hper : Periodic f T) :
    ∫ x in (0 : ℝ)..T, deriv f x = 0 := by
  rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc hf.contDiffOn hT]
  have hend : f T = f 0 := by simpa using hper 0
  rw [hend, sub_self]

/-- Integration by parts over one period, with the endpoint term cancelled by periodicity. -/
theorem intervalIntegral_mul_deriv_eq_neg_deriv_mul_of_periodic
    {T : ℝ} {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfper : Periodic f T) (hgper : Periodic g T) :
    ∫ x in (0 : ℝ)..T, f x * deriv g x =
      -∫ x in (0 : ℝ)..T, deriv f x * g x := by
  have hfac : AbsolutelyContinuousOnInterval f 0 T :=
    hf.contDiffOn.absolutelyContinuousOnInterval
  have hgac : AbsolutelyContinuousOnInterval g 0 T :=
    hg.contDiffOn.absolutelyContinuousOnInterval
  rw [hfac.integral_mul_deriv_eq_deriv_mul hgac]
  have hfend : f T = f 0 := by simpa using hfper 0
  have hgend : g T = g 0 := by simpa using hgper 0
  rw [hfend, hgend, sub_self, zero_sub]

/-- Smooth integration by parts on a measured circle of arbitrary positive period. -/
theorem addCircle_integral_mul_deriv_eq_neg_deriv_mul_of_periodic
    {T : ℝ} [Fact (0 < T)] {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfper : Periodic f T) (hgper : Periodic g T) :
    (∫ x : AddCircle T,
        AddCircle.liftIoc T 0 (fun r => f r * deriv g r) x) =
      -(∫ x : AddCircle T,
        AddCircle.liftIoc T 0 (fun r => deriv f r * g r) x) := by
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral,
    AddCircle.integral_liftIoc_eq_intervalIntegral]
  simpa using
    intervalIntegral_mul_deriv_eq_neg_deriv_mul_of_periodic hf hg hfper hgper

end Circle

section UnitCircleRegression

/-- The real part of the first nonzero unit-circle Fourier mode, on the real lift. -/
def unitCosineLift (r : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * r)

/-- The imaginary part of the first nonzero unit-circle Fourier mode, on the real lift. -/
def unitSineLift (r : ℝ) : ℝ :=
  Real.sin (2 * Real.pi * r)

theorem unitCosineLift_contDiff : ContDiff ℝ 1 unitCosineLift := by
  exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

theorem unitSineLift_contDiff : ContDiff ℝ 1 unitSineLift := by
  exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

theorem unitCosineLift_periodic : Periodic unitCosineLift 1 := by
  intro r
  change Real.cos (2 * Real.pi * (r + 1)) = Real.cos (2 * Real.pi * r)
  simpa only [mul_add, mul_one] using Real.cos_periodic (2 * Real.pi * r)

theorem unitSineLift_periodic : Periodic unitSineLift 1 := by
  intro r
  change Real.sin (2 * Real.pi * (r + 1)) = Real.sin (2 * Real.pi * r)
  simpa only [mul_add, mul_one] using Real.sin_periodic (2 * Real.pi * r)

/-- The unit-period normalization puts the factor `2π` in the first-mode derivative. -/
theorem deriv_unitSineLift (r : ℝ) :
    deriv unitSineLift r = 2 * Real.pi * unitCosineLift r := by
  have hinner : HasDerivAt (fun s : ℝ => (2 * Real.pi) * s) (2 * Real.pi) r :=
    hasDerivAt_const_mul (2 * Real.pi)
  have h := ((Real.hasDerivAt_sin (2 * Real.pi * r)).comp r hinner).deriv
  change deriv (Real.sin ∘ fun s : ℝ => (2 * Real.pi) * s) r =
    2 * Real.pi * Real.cos (2 * Real.pi * r)
  rw [h]
  ring

/-- The cosine test pins both the `2π` normalization and the derivative sign. -/
theorem deriv_unitCosineLift (r : ℝ) :
    deriv unitCosineLift r = -(2 * Real.pi * unitSineLift r) := by
  have hinner : HasDerivAt (fun s : ℝ => (2 * Real.pi) * s) (2 * Real.pi) r :=
    hasDerivAt_const_mul (2 * Real.pi)
  have h := ((Real.hasDerivAt_cos (2 * Real.pi * r)).comp r hinner).deriv
  change deriv (Real.cos ∘ fun s : ℝ => (2 * Real.pi) * s) r =
    -(2 * Real.pi * Real.sin (2 * Real.pi * r))
  rw [h]
  ring

/-- A nonconstant unit-period test of the circle integration-by-parts kernel. -/
theorem unitCircle_sine_cosine_integration_by_parts :
    (∫ x : UnitAddCircle,
        AddCircle.liftIoc 1 0
          (fun r => unitSineLift r * deriv unitCosineLift r) x) =
      -(∫ x : UnitAddCircle,
        AddCircle.liftIoc 1 0
          (fun r => deriv unitSineLift r * unitCosineLift r) x) := by
  exact addCircle_integral_mul_deriv_eq_neg_deriv_mul_of_periodic
    unitSineLift_contDiff unitCosineLift_contDiff
    unitSineLift_periodic unitCosineLift_periodic

end UnitCircleRegression

section UnitTorus

variable {n : ℕ}

/-- The coordinates complementary to `i : Fin (n + 1)` on a unit torus. -/
abbrev UnitTorusCoordinateComplement (n : ℕ) := UnitAddTorus (Fin n)

/-- Restrict a scalar field on `UnitAddTorus (Fin (n + 1))` to one coordinate circle. -/
def unitTorusCoordinateSlice
    (f : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1))
    (y : UnitTorusCoordinateComplement n) (a : UnitAddCircle) : ℝ :=
  f (i.insertNth a y)

/-- Lift a unit-torus coordinate slice to its one-periodic real parametrization. -/
def unitTorusCoordinateSliceLift
    (f : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1))
    (y : UnitTorusCoordinateComplement n) (r : ℝ) : ℝ :=
  unitTorusCoordinateSlice f i y (r : UnitAddCircle)

theorem unitTorusCoordinateSliceLift_periodic
    (f : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1))
    (y : UnitTorusCoordinateComplement n) :
    Periodic (unitTorusCoordinateSliceLift f i y) 1 := by
  intro r
  apply congrArg f
  rw [Fin.insertNth_inj]
  exact ⟨by simp, rfl⟩

/-- The classical coordinate derivative, defined through the smooth periodic real lift. -/
def unitTorusCoordinateSliceDerivative
    (f : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1))
    (y : UnitTorusCoordinateComplement n) (a : UnitAddCircle) : ℝ :=
  AddCircle.liftIoc 1 0 (deriv (unitTorusCoordinateSliceLift f i y)) a

private theorem liftIoc_unitTorusCoordinateSliceLift
    (f : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1))
    (y : UnitTorusCoordinateComplement n) (a : UnitAddCircle) :
    AddCircle.liftIoc 1 0 (unitTorusCoordinateSliceLift f i y) a =
      unitTorusCoordinateSlice f i y a := by
  change f (i.insertNth
      ((AddCircle.equivIoc 1 0 a).1 : UnitAddCircle) y) =
    f (i.insertNth a y)
  rw [AddCircle.coe_equivIoc]

private theorem liftIoc_mul (f g : ℝ → ℝ) (a : UnitAddCircle) :
    AddCircle.liftIoc 1 0 (fun r => f r * g r) a =
      AddCircle.liftIoc 1 0 f a * AddCircle.liftIoc 1 0 g a := by
  rfl

/-- Integration by parts on each coordinate circle of a unit torus. -/
theorem unitTorusCoordinateSlice_integration_by_parts
    (f g : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1))
    (y : UnitTorusCoordinateComplement n)
    (hf : ContDiff ℝ 1 (unitTorusCoordinateSliceLift f i y))
    (hg : ContDiff ℝ 1 (unitTorusCoordinateSliceLift g i y)) :
    (∫ a : UnitAddCircle,
        unitTorusCoordinateSlice f i y a * unitTorusCoordinateSliceDerivative g i y a) =
      -(∫ a : UnitAddCircle,
        unitTorusCoordinateSliceDerivative f i y a * unitTorusCoordinateSlice g i y a) := by
  have h := addCircle_integral_mul_deriv_eq_neg_deriv_mul_of_periodic
    hf hg (unitTorusCoordinateSliceLift_periodic f i y)
      (unitTorusCoordinateSliceLift_periodic g i y)
  simpa only [liftIoc_mul, liftIoc_unitTorusCoordinateSliceLift,
    unitTorusCoordinateSliceDerivative] using h

/-- The classical coordinate derivative as a scalar field on the whole unit torus. -/
def unitTorusCoordinateDerivative
    (f : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1))
    (x : UnitAddTorus (Fin (n + 1))) : ℝ :=
  unitTorusCoordinateSliceDerivative f i (Fin.removeNth i x) (x i)

@[simp]
theorem unitTorusCoordinateDerivative_const (c : ℝ) (i : Fin (n + 1))
    (x : UnitAddTorus (Fin (n + 1))) :
    unitTorusCoordinateDerivative (fun _ => c) i x = 0 := by
  have hfun :
      unitTorusCoordinateSliceLift (fun _ : UnitAddTorus (Fin (n + 1)) => c)
          i (Fin.removeNth i x) =
        fun _ : ℝ => c := by
    rfl
  rw [unitTorusCoordinateDerivative, unitTorusCoordinateSliceDerivative, hfun]
  rw [deriv_const']
  rfl

/-- Haar volume splits into a selected unit circle and the complementary unit torus. -/
theorem unitTorus_volume_preserving_coordinate_split (i : Fin (n + 1)) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => UnitAddCircle) i) :=
  volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => UnitAddCircle) i

/-- Smooth scalar coordinate integration by parts on a normalized unit torus of arbitrary
positive finite dimension. -/
theorem unitTorus_integral_mul_coordinateDerivative_eq_neg
    (f g : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1))
    (hf : ∀ y : UnitTorusCoordinateComplement n,
      ContDiff ℝ 1 (unitTorusCoordinateSliceLift f i y))
    (hg : ∀ y : UnitTorusCoordinateComplement n,
      ContDiff ℝ 1 (unitTorusCoordinateSliceLift g i y))
    (hfg : Integrable (fun x => f x * unitTorusCoordinateDerivative g i x))
    (hgf : Integrable (fun x => unitTorusCoordinateDerivative f i x * g x)) :
    (∫ x, f x * unitTorusCoordinateDerivative g i x) =
      -(∫ x, unitTorusCoordinateDerivative f i x * g x) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => UnitAddCircle) i
  have he : MeasurePreserving e := unitTorus_volume_preserving_coordinate_split i
  have hesymm : MeasurePreserving e.symm := MeasurePreserving.symm e he
  have hfg' : Integrable
      ((fun x => f x * unitTorusCoordinateDerivative g i x) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hfg
  have hgf' : Integrable
      ((fun x => unitTorusCoordinateDerivative f i x * g x) ∘ e.symm) :=
    hesymm.integrable_comp_of_integrable hgf
  calc
    (∫ x, f x * unitTorusCoordinateDerivative g i x) =
        ∫ z : UnitAddCircle × UnitTorusCoordinateComplement n,
          ((fun x => f x * unitTorusCoordinateDerivative g i x) ∘ e.symm) z := by
      symm
      exact hesymm.integral_comp'
        (fun x => f x * unitTorusCoordinateDerivative g i x)
    _ = ∫ y : UnitTorusCoordinateComplement n,
        ∫ a : UnitAddCircle,
          unitTorusCoordinateSlice f i y a *
            unitTorusCoordinateSliceDerivative g i y a := by
      rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hfg']
      simp [e, unitTorusCoordinateDerivative, unitTorusCoordinateSlice,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    _ = -(∫ y : UnitTorusCoordinateComplement n,
        ∫ a : UnitAddCircle,
          unitTorusCoordinateSliceDerivative f i y a *
            unitTorusCoordinateSlice g i y a) := by
      simp_rw [unitTorusCoordinateSlice_integration_by_parts f g i _ (hf _) (hg _)]
      exact MeasureTheory.integral_neg _
    _ = -(∫ z : UnitAddCircle × UnitTorusCoordinateComplement n,
        ((fun x => unitTorusCoordinateDerivative f i x * g x) ∘ e.symm) z) := by
      rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hgf']
      simp [e, unitTorusCoordinateDerivative, unitTorusCoordinateSlice,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    _ = -(∫ x, unitTorusCoordinateDerivative f i x * g x) := by
      exact congrArg Neg.neg (hesymm.integral_comp'
        (fun x => unitTorusCoordinateDerivative f i x * g x))

end UnitTorus

end ForTauCeti
