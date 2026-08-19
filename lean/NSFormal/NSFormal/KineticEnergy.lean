import NSFormal.SpatialInterpolation
import NSFormal.PeriodicRegularity

/-!
# Kinetic energy of concrete periodic Navier--Stokes solutions

This file derives the velocity kinetic-energy identity from the actual
`IsClassicalNavierStokesOn` momentum equation.  In particular, pressure work
and nonlinear transport are cancelled by the concrete Haar integration-by-parts
theorems; neither cancellation is postulated as an abstract interface.
-/

open Filter Function MeasureTheory Set

noncomputable section

/-- Kinetic energy is the integral of `|u|² / 2`. -/
def torusKineticEnergy (u : C(Torus3, Vec3)) : ℝ :=
  torusEnstrophy u

/-- The pressure-work density `u · ∇p`. -/
def torusPressureWork
    (u : C(Torus3, Vec3)) (p : C(Torus3, ℝ)) (x : Torus3) : ℝ :=
  inner ℝ (u x) (torusGradient p x)

/-- The pressure work is coordinate transport of the pressure by the velocity. -/
theorem torusPressureWork_eq_scalarTransport
    (u : C(Torus3, Vec3)) (p : C(Torus3, ℝ)) (x : Torus3)
    (hp : ContDiff ℝ 1 (torusLift p)) :
    torusPressureWork u p x = torusScalarTransport u p x := by
  simp only [torusPressureWork, torusGradient, torusScalarTransport,
    PiLp.inner_apply, Real.inner_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [torusCoordinateDerivative_eq_torusPartial p i x hp]

/-- Periodic incompressibility cancels pressure work globally. -/
theorem integral_torusPressureWork_eq_zero
    (u : C(Torus3, Vec3)) (p : C(Torus3, ℝ))
    (hp : ContDiff ℝ 1 (torusLift p))
    (huSlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) i y))
    (hpSlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift p i y))
    (hleft : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      (((1 : ℝ) * u x i) * torusCoordinateDerivative p i x)))
    (hright : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => (1 : ℝ) * u z i) i x * p x))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0) :
    (∫ x : Torus3, torusPressureWork u p x) = 0 := by
  calc
    (∫ x : Torus3, torusPressureWork u p x) =
        ∫ x : Torus3, torusScalarTransport u p x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        torusPressureWork_eq_scalarTransport u p x hp
    _ = 0 := integral_torusScalarTransport_eq_zero
      u p huSlices hpSlices hleft hright hdiv

/-- Smoothness on the compact torus automatically makes pressure work integrable. -/
theorem integrable_torusPressureWork_of_contDiff
    (u : C(Torus3, Vec3)) (p : C(Torus3, ℝ))
    (hp : ContDiff ℝ 1 (torusLift p)) :
    Integrable (torusPressureWork u p) := by
  exact (integrable_torusScalarTransport_of_contDiff u p hp).congr
    (Eventually.of_forall fun x =>
      (torusPressureWork_eq_scalarTransport u p x hp).symm)

/-- The pressure cancellation with every slice and integrability premise
discharged from ordinary lift smoothness. -/
theorem integral_torusPressureWork_eq_zero_of_contDiff
    (u : C(Torus3, Vec3)) (p : C(Torus3, ℝ))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hp : ContDiff ℝ 1 (torusLift p))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0) :
    (∫ x : Torus3, torusPressureWork u p x) = 0 := by
  calc
    (∫ x : Torus3, torusPressureWork u p x) =
        ∫ x : Torus3, torusScalarTransport u p x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        torusPressureWork_eq_scalarTransport u p x hp
    _ = 0 := integral_torusScalarTransport_eq_zero_of_contDiff u p hu hp hdiv

/-- Smoothness of the transported vector field makes its transport-energy
density integrable. -/
theorem integrable_torusVorticityTransportProduction_of_contDiff
    (u w : C(Torus3, Vec3)) (hw : ContDiff ℝ 1 (torusLift w)) :
    Integrable (torusVorticityTransportProduction u w) := by
  have henergy := contDiff_torusLift_vorticityEnergyField w hw
  exact (integrable_torusScalarTransport_of_contDiff
    u (vorticityEnergyField w) henergy).congr
      (Eventually.of_forall fun x =>
        (torusVorticityTransportProduction_eq_scalarTransport u w x hw).symm)

/-- Divergence-free transport contributes zero to global vector energy, with
all analytic side conditions discharged from smoothness. -/
theorem integral_torusVorticityTransportProduction_eq_zero_of_contDiff
    (u w : C(Torus3, Vec3))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0) :
    (∫ x : Torus3, torusVorticityTransportProduction u w x) = 0 := by
  have henergy := contDiff_torusLift_vorticityEnergyField w hw
  calc
    (∫ x : Torus3, torusVorticityTransportProduction u w x) =
        ∫ x : Torus3, torusScalarTransport u (vorticityEnergyField w) x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        torusVorticityTransportProduction_eq_scalarTransport u w x hw
    _ = 0 := integral_torusScalarTransport_eq_zero_of_contDiff
      u (vorticityEnergyField w) hu henergy hdiv

/-- Sup-norm differentiability of velocity differentiates kinetic energy. -/
theorem torusKineticEnergy_hasDerivAt
    {u : ℝ → C(Torus3, Vec3)} {u' : C(Torus3, Vec3)} {t : ℝ}
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => torusKineticEnergy (u s))
      (∫ x : Torus3, inner ℝ (u t x) (u' x)) t := by
  simpa only [torusKineticEnergy] using torusEnstrophy_hasDerivAt hu

/-- Pair the concrete momentum equation with velocity and integrate. -/
theorem IsClassicalNavierStokesOn.hasDerivAt_torusKineticEnergy_paired
    {ν a b : ℝ} {u uTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (h : IsClassicalNavierStokesOn ν a b u uTime p)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivAt (fun s => torusKineticEnergy (u s))
      (∫ x : Torus3, inner ℝ (u t x)
        (ν • torusVectorLaplacian (u t) x - torusGradient (p t) x -
          torusTransport (u t) (u t) x)) t := by
  apply (torusKineticEnergy_hasDerivAt (h.2.2.1 t ht)).congr_deriv
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  exact eq_sub_of_add_eq (h.2.2.2.2.2.2 t ht x)

/-- Expose the diffusion product rule in the kinetic-energy derivative. -/
theorem IsClassicalNavierStokesOn.hasDerivAt_torusKineticEnergy_expanded
    {ν a b : ℝ} {u uTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (h : IsClassicalNavierStokesOn ν a b u uTime p)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivAt (fun s => torusKineticEnergy (u s))
      (∫ x : Torus3,
        ν * torusScalarLaplacian (vorticityEnergyField (u t)) x -
          ν * torusPalinstrophyDensity (u t) x -
          torusPressureWork (u t) (p t) x -
          torusVorticityTransportProduction (u t) (u t) x) t := by
  apply (h.hasDerivAt_torusKineticEnergy_paired ht).congr_deriv
  apply integral_congr_ae
  filter_upwards with x
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have hdiff := inner_torusLiftVectorLaplacian_eq
    (u t) (torus3Representative x) (h.2.2.2.1 t htcc)
  have hlift : torusLift (u t) (torus3Representative x) = u t x := by
    simp [torusLift]
  rw [hlift] at hdiff
  simp only [torusPressureWork, torusVorticityTransportProduction,
    torusScalarLaplacian, torusPalinstrophyDensity, torusVectorLaplacian]
  rw [inner_sub_right, inner_sub_right, real_inner_smul_right, hdiff]
  ring

/-- After the three periodic cancellations, momentum supplies the exact
kinetic-energy dissipation rate. -/
theorem IsClassicalNavierStokesOn.hasDerivAt_torusKineticEnergy_balance
    {ν a b : ℝ} {u uTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (h : IsClassicalNavierStokesOn ν a b u uTime p)
    {t : ℝ} (ht : t ∈ Ico a b)
    (hL : Integrable
      (torusScalarLaplacian (vorticityEnergyField (u t))))
    (hP : Integrable (torusPalinstrophyDensity (u t)))
    (hW : Integrable (torusPressureWork (u t) (p t)))
    (hT : Integrable (torusVorticityTransportProduction (u t) (u t)))
    (hlap : (∫ x : Torus3,
      torusScalarLaplacian (vorticityEnergyField (u t)) x) = 0)
    (hpressure : (∫ x : Torus3,
      torusPressureWork (u t) (p t) x) = 0)
    (htransport : (∫ x : Torus3,
      torusVorticityTransportProduction (u t) (u t) x) = 0) :
    HasDerivAt (fun s => torusKineticEnergy (u s))
      (-ν * torusPalinstrophy (u t)) t := by
  apply (h.hasDerivAt_torusKineticEnergy_expanded ht).congr_deriv
  let L : Torus3 → ℝ :=
    torusScalarLaplacian (vorticityEnergyField (u t))
  let P : Torus3 → ℝ := torusPalinstrophyDensity (u t)
  let W : Torus3 → ℝ := torusPressureWork (u t) (p t)
  let T : Torus3 → ℝ := torusVorticityTransportProduction (u t) (u t)
  have hLc : Integrable L := hL
  have hPc : Integrable P := hP
  have hWc : Integrable W := hW
  have hTc : Integrable T := hT
  change (∫ x : Torus3, (((ν • L - ν • P) - W - T) x)) =
    -ν * torusPalinstrophy (u t)
  calc
    (∫ x : Torus3, (((ν • L - ν • P) - W - T) x)) =
        (∫ x : Torus3, (((ν • L - ν • P) - W) x)) -
          (∫ x : Torus3, T x) := by
      simpa only [Pi.sub_apply] using MeasureTheory.integral_sub
        (((hLc.smul ν).sub (hPc.smul ν)).sub hWc) hTc
    _ = ((∫ x : Torus3, ((ν • L - ν • P) x)) -
          (∫ x : Torus3, W x)) - (∫ x : Torus3, T x) := by
      congr 1
      simpa only [Pi.sub_apply] using MeasureTheory.integral_sub
        ((hLc.smul ν).sub (hPc.smul ν)) hWc
    _ = (((∫ x : Torus3, (ν • L) x) -
          (∫ x : Torus3, (ν • P) x)) -
          (∫ x : Torus3, W x)) - (∫ x : Torus3, T x) := by
      congr 2
      simpa only [Pi.sub_apply] using MeasureTheory.integral_sub
        (hLc.smul ν) (hPc.smul ν)
    _ = ((ν * ∫ x : Torus3, L x) - (ν * ∫ x : Torus3, P x) -
          (∫ x : Torus3, W x)) - (∫ x : Torus3, T x) := by
      simp only [Pi.smul_apply, smul_eq_mul,
        MeasureTheory.integral_const_mul]
    _ = -ν * torusPalinstrophy (u t) := by
      change ((ν * (∫ x : Torus3,
          torusScalarLaplacian (vorticityEnergyField (u t)) x) -
        ν * (∫ x : Torus3, P x) -
        (∫ x : Torus3, torusPressureWork (u t) (p t) x)) -
        (∫ x : Torus3,
          torusVorticityTransportProduction (u t) (u t) x)) = _
      rw [hlap, hpressure, htransport]
      simp only [torusPalinstrophy]
      ring

/-- Assemble the clean kinetic-energy derivative using the actual classical
momentum equation and the concrete periodic cancellation theorems. -/
theorem hasDerivAt_torusKineticEnergy_balance_of_classicalNavierStokes
    {ν a b : ℝ} {u uTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsClassicalNavierStokesOn ν a b u uTime p)
    {t : ℝ} (ht : t ∈ Ico a b)
    (hL : Integrable
      (torusScalarLaplacian (vorticityEnergyField (u t))))
    (hP : Integrable (torusPalinstrophyDensity (u t)))
    (hW : Integrable (torusPressureWork (u t) (p t)))
    (hT : Integrable (torusVorticityTransportProduction (u t) (u t)))
    (henergySlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 2
        (torusCoordinateSliceLift (vorticityEnergyField (u t)) i y))
    (hsecond : ∀ i : Fin 3, Integrable
      (torusCoordinateSecondDerivative (vorticityEnergyField (u t)) i))
    (huSlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u t x i) i y))
    (hpSlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (p t) i y))
    (hpressureLeft : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      (((1 : ℝ) * u t x i) * torusCoordinateDerivative (p t) i x)))
    (hpressureRight : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => (1 : ℝ) * u t z i) i x * p t x))
    (htransportLeft : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      (((1 : ℝ) * u t x i) *
        torusCoordinateDerivative (vorticityEnergyField (u t)) i x)))
    (htransportRight : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => (1 : ℝ) * u t z i) i x *
        vorticityEnergyField (u t) x)) :
    HasDerivAt (fun s => torusKineticEnergy (u s))
      (-ν * torusPalinstrophy (u t)) t := by
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have hu : ContDiff ℝ 1 (torusLift (u t)) :=
    (hNS.2.2.2.1 t htcc).of_le (by norm_num)
  have hp : ContDiff ℝ 1 (torusLift (p t)) := hNS.2.2.2.2.1 t htcc
  apply hNS.hasDerivAt_torusKineticEnergy_balance ht hL hP hW hT
  · exact integral_torusScalarLaplacian_eq_zero
      (vorticityEnergyField (u t)) henergySlices hsecond
  · exact integral_torusPressureWork_eq_zero
      (u t) (p t) hp huSlices hpSlices hpressureLeft hpressureRight
      (fun x => hNS.torusCoordinateDivergence_eq_zero htcc x)
  · exact integral_torusVorticityTransportProduction_eq_zero
      (u t) (u t) hu huSlices
      (fun i y => (henergySlices i y).of_le (by norm_num))
      htransportLeft htransportRight
      (fun x => hNS.torusCoordinateDivergence_eq_zero htcc x)

/-- Application form of the kinetic-energy balance.  Smoothness from the
classical predicate discharges pressure, transport, palinstrophy, and all
coordinate-slice and integrability obligations, including the descended
second derivatives. -/
theorem hasDerivAt_torusKineticEnergy_balance_of_classicalNavierStokes_smooth
    {ν a b : ℝ} {u uTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsClassicalNavierStokesOn ν a b u uTime p)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivAt (fun s => torusKineticEnergy (u s))
      (-ν * torusPalinstrophy (u t)) t := by
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have hu2 : ContDiff ℝ 2 (torusLift (u t)) := hNS.2.2.2.1 t htcc
  have hu1 : ContDiff ℝ 1 (torusLift (u t)) :=
    hu2.of_le (by norm_num)
  have hp1 : ContDiff ℝ 1 (torusLift (p t)) := hNS.2.2.2.2.1 t htcc
  have henergy2 : ContDiff ℝ 2
      (torusLift (vorticityEnergyField (u t))) :=
    contDiff_torusLift_vorticityEnergyField (u t) hu2
  have hsecond : ∀ i : Fin 3, Integrable
      (torusCoordinateSecondDerivative (vorticityEnergyField (u t)) i) :=
    fun i => integrable_torusCoordinateSecondDerivative_of_contDiff
      (vorticityEnergyField (u t)) i henergy2
  have henergySlices : ∀ (i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 2
        (torusCoordinateSliceLift (vorticityEnergyField (u t)) i y) :=
    fun i y => contDiff_torusCoordinateSliceLift_of_contDiff_torusLift
      (vorticityEnergyField (u t)) i y henergy2
  have hL : Integrable
      (torusScalarLaplacian (vorticityEnergyField (u t))) := by
    have hsum : Integrable (fun x : Torus3 =>
        ∑ i : Fin 3,
          torusCoordinateSecondDerivative (vorticityEnergyField (u t)) i x) :=
      MeasureTheory.integrable_finsetSum Finset.univ fun i _ => hsecond i
    exact hsum.congr (Eventually.of_forall fun x =>
      (torusScalarLaplacian_eq_sum_coordinateSecondDerivative
        (vorticityEnergyField (u t)) x).symm)
  have hP : Integrable (torusPalinstrophyDensity (u t)) :=
    integrable_torusPalinstrophyDensity_of_contDiff (u t) hu1
  have hW : Integrable (torusPressureWork (u t) (p t)) :=
    integrable_torusPressureWork_of_contDiff (u t) (p t) hp1
  have hT : Integrable
      (torusVorticityTransportProduction (u t) (u t)) :=
    integrable_torusVorticityTransportProduction_of_contDiff (u t) (u t) hu1
  apply hNS.hasDerivAt_torusKineticEnergy_balance ht hL hP hW hT
  · exact integral_torusScalarLaplacian_eq_zero
      (vorticityEnergyField (u t)) henergySlices hsecond
  · exact integral_torusPressureWork_eq_zero_of_contDiff
      (u t) (p t) hu1 hp1
      (fun x => hNS.torusCoordinateDivergence_eq_zero htcc x)
  · exact integral_torusVorticityTransportProduction_eq_zero_of_contDiff
      (u t) (u t) hu1 hu1
      (fun x => hNS.torusCoordinateDivergence_eq_zero htcc x)

/-- Kinetic energy is nonnegative. -/
theorem torusKineticEnergy_nonneg (u : C(Torus3, Vec3)) :
    0 ≤ torusKineticEnergy u := by
  unfold torusKineticEnergy torusEnstrophy
  exact integral_nonneg fun x => vorticityEnergyField_nonneg u x

/-- The squared `L²` norm is twice the half-squared energy. -/
theorem torusVectorSecondMoment_eq_two_torusEnstrophy
    (w : C(Torus3, Vec3)) :
    torusVectorSecondMoment w = 2 * torusEnstrophy w := by
  unfold torusVectorSecondMoment torusEnstrophy
  calc
    (∫ x : Torus3, ‖w x‖ ^ 2) =
        ∫ x : Torus3, 2 * vorticityEnergyField w x := by
      apply integral_congr_ae
      filter_upwards with x
      simp [vorticityEnergyField_apply, vorticityEnergy]
      ring
    _ = 2 * ∫ x : Torus3, vorticityEnergyField w x := by
      exact MeasureTheory.integral_const_mul 2 (vorticityEnergyField w)

/-- Concrete periodic div--curl converts velocity palinstrophy into twice the
enstrophy of its curl. -/
theorem torusPalinstrophy_eq_two_torusEnstrophy_of_curl_divergence_mixed
    (u w : C(Torus3, Vec3))
    (huLift : ContDiff ℝ 1 (torusLift u))
    (hw : ∀ x : Torus3, w x = torusCurl u x)
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hfirst : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x =>
          periodicFirstDerivative u k j x) i y))
    (hcross : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x * periodicFirstDerivative u j i x))
    (hsecond : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      u x j * periodicSecondDerivative u i j i x))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0)
    (hmixed : ∀ (i k j : Fin 3) (x : Torus3),
      periodicSecondDerivative u i k j x =
        periodicSecondDerivative u k i j x)
    (hcurl : Integrable (fun x : Torus3 =>
      ‖periodicCoordinateCurl u x‖ ^ 2)) :
    torusPalinstrophy u = 2 * torusEnstrophy w := by
  calc
    torusPalinstrophy u = torusGradientEnergy u :=
      torusPalinstrophy_eq_torusGradientEnergy u huLift
    _ = torusVectorSecondMoment w :=
      torusGradientEnergy_eq_torusVectorSecondMoment_of_curl_divergence_mixed
        u w huLift hw hu hfirst hcross hsecond hdiv hmixed hcurl
    _ = 2 * torusEnstrophy w :=
      torusVectorSecondMoment_eq_two_torusEnstrophy w

/-- The kinetic-energy functional is continuous in the velocity sup norm. -/
theorem continuous_torusKineticEnergy :
    Continuous (torusKineticEnergy : C(Torus3, Vec3) → ℝ) := by
  have hfun :
      (torusKineticEnergy : C(Torus3, Vec3) → ℝ) =
        torusIntegralCLM ∘ vorticityEnergyField := by
    funext u
    simp [torusKineticEnergy, torusEnstrophy]
  rw [hfun]
  exact torusIntegralCLM.continuous.comp continuous_vorticityEnergyField

/-- Fundamental-theorem-of-calculus form of the kinetic-energy identity. -/
theorem torusKineticEnergy_identity_of_hasDerivAt_balance
    {ν a t : ℝ} {u : ℝ → C(Torus3, Vec3)}
    (hat : a ≤ t)
    (hu : ContinuousOn u (Icc a t))
    (hbalance : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusKineticEnergy (u r))
        (-ν * torusPalinstrophy (u s)) s)
    (hint : IntervalIntegrable (fun s => torusPalinstrophy (u s)) volume a t) :
    torusKineticEnergy (u t) +
        ν * (∫ s in a..t, torusPalinstrophy (u s)) =
      torusKineticEnergy (u a) := by
  have hKcont : ContinuousOn (fun s => torusKineticEnergy (u s)) (Icc a t) :=
    continuous_torusKineticEnergy.comp_continuousOn hu
  have hscaled : IntervalIntegrable
      (fun s => -ν * torusPalinstrophy (u s)) volume a t :=
    hint.const_mul (-ν)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hat hKcont hbalance hscaled
  rw [intervalIntegral.integral_const_mul] at hFTC
  linarith

/-- The exact identity immediately pays the time integral of palinstrophy. -/
theorem torusPalinstrophy_budget_of_hasDerivAt_balance
    {ν a t : ℝ} {u : ℝ → C(Torus3, Vec3)}
    (hat : a ≤ t)
    (hu : ContinuousOn u (Icc a t))
    (hbalance : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusKineticEnergy (u r))
        (-ν * torusPalinstrophy (u s)) s)
    (hint : IntervalIntegrable (fun s => torusPalinstrophy (u s)) volume a t) :
    ν * (∫ s in a..t, torusPalinstrophy (u s)) ≤
      torusKineticEnergy (u a) := by
  have hid := torusKineticEnergy_identity_of_hasDerivAt_balance
    hat hu hbalance hint
  nlinarith [torusKineticEnergy_nonneg (u t)]

/-- If palinstrophy is the squared `L²` norm of the curl, the kinetic-energy
identity supplies exactly the `L¹_t` enstrophy budget used by the logarithmic
continuation argument. -/
theorem torusEnstrophy_budget_of_curl_energy
    {ν a t : ℝ} {u w : ℝ → C(Torus3, Vec3)}
    (hν : 0 < ν) (hat : a ≤ t)
    (hu : ContinuousOn u (Icc a t))
    (hbalance : ∀ s ∈ Ioo a t,
      HasDerivAt (fun r => torusKineticEnergy (u r))
        (-ν * torusPalinstrophy (u s)) s)
    (hint : IntervalIntegrable (fun s => torusPalinstrophy (u s)) volume a t)
    (hcurlEnergy : ∀ s ∈ Ioo a t,
      torusPalinstrophy (u s) = 2 * torusEnstrophy (w s)) :
    (∫ s in a..t, torusEnstrophy (w s)) ≤
      torusKineticEnergy (u a) / (2 * ν) := by
  have hbudget := torusPalinstrophy_budget_of_hasDerivAt_balance
    hat hu hbalance hint
  have hintegral :
      (∫ s in a..t, torusPalinstrophy (u s)) =
        2 * ∫ s in a..t, torusEnstrophy (w s) := by
    calc
      (∫ s in a..t, torusPalinstrophy (u s)) =
          ∫ s in a..t, 2 * torusEnstrophy (w s) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hat
        intro s hs
        exact hcurlEnergy s hs
      _ = 2 * ∫ s in a..t, torusEnstrophy (w s) := by
        rw [intervalIntegral.integral_const_mul]
  rw [hintegral] at hbudget
  apply (le_div_iff₀ (mul_pos (by norm_num) hν)).2
  nlinarith
