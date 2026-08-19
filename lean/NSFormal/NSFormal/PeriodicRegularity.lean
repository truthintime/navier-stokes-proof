import NSFormal.PeriodicSobolevEuclidean
import NSFormal.VectorCalculus

/-!
# Routine regularity of smooth periodic fields

This module discharges coordinate-slice and integrability side conditions from
ordinary smoothness of the Euclidean periodic lift.
-/

open Filter Function MeasureTheory Set

noncomputable section

/-- A smooth torus field equal to the curl of a `C²` velocity is divergence
free in the concrete Haar-coordinate convention.  The proof passes through
the periodic Euclidean lifts, where this is symmetry of the Hessian. -/
theorem torusCoordinateDivergence_eq_zero_of_eq_torusCurl
    (u w : C(Torus3, Vec3))
    (hu : ContDiff ℝ 2 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hcurl : ∀ x : Torus3, w x = torusCurl u x)
    (x : Torus3) :
    torusCoordinateDivergence w x = 0 := by
  rw [torusCoordinateDivergence_eq_torusDivergence w x hw,
    torusDivergence_eq_euclideanDivergence]
  have hlift : torusLift w = fun y => euclideanCurl (torusLift u) y := by
    funext y
    exact torusLift_eq_euclideanCurl_of_curl u w
      (hu.of_le (by norm_num)) hcurl y
  rw [hlift]
  exact euclideanDivergence_curl_eq_zero hu _

/-- The canonical `Ico` representative used by the pointwise PDE operators is measurable. -/
theorem measurable_torus3Representative : Measurable torus3Representative := by
  have hraw : Measurable (fun x : Torus3 => fun i : Fin 3 =>
      (AddCircle.equivIco ((2 : ℝ) * Real.pi) 0 (x i) : ℝ)) :=
    measurable_pi_lambda _ fun i =>
      measurable_subtype_coe.comp
        ((AddCircle.measurableEquivIco ((2 : ℝ) * Real.pi) 0).measurable.comp
          (measurable_pi_apply i))
  exact (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp hraw

/-- Smoothness of a scalar periodic lift restricts to every real coordinate
slice of the quotient torus. -/
theorem contDiff_torusCoordinateSliceLift_of_contDiff_torusLift
    {n : WithTop ℕ∞} (f : C(Torus3, ℝ)) (i : Fin 3)
    (y : TorusCoordinateComplement)
    (hf : ContDiff ℝ n (torusLift f)) :
    ContDiff ℝ n (torusCoordinateSliceLift f i y) := by
  let x₀ : Torus3 := i.insertNth 0 y
  have hline : ContDiff ℝ n (fun s : ℝ =>
      torusLift f (coordinateLine (torus3Representative x₀) i s)) :=
    hf.comp (by unfold coordinateLine; fun_prop)
  convert hline using 1
  funext s
  change f (i.insertNth (s : AddCircle ((2 : ℝ) * Real.pi)) y) =
    f (torus3Mk (coordinateLine (torus3Representative x₀) i s))
  rw [torus3Mk_coordinateLine_representative]
  simp [x₀, torus3Representative]

/-- The same restriction fact for a scalar component of a vector field. -/
theorem contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
    {n : WithTop ℕ∞} (u : C(Torus3, Vec3)) (i j : Fin 3)
    (y : TorusCoordinateComplement)
    (hu : ContDiff ℝ n (torusLift u)) :
    ContDiff ℝ n
      (torusCoordinateSliceLift (fun x => u x j) i y) := by
  have hucomp : ContDiff ℝ n (torusLift (torusVectorComponent u j)) := by
    change ContDiff ℝ n (fun z => torusLift u z j)
    exact ContDiff.continuousLinearMap_comp (EuclideanSpace.proj j) hu
  exact contDiff_torusCoordinateSliceLift_of_contDiff_torusLift
    (torusVectorComponent u j) i y hucomp

/-- A descended first derivative of a `C²` periodic vector field is `C¹` on
every quotient-coordinate slice. -/
theorem contDiff_torusCoordinateSliceLift_periodicFirstDerivative_of_contDiff
    (u : C(Torus3, Vec3)) (i k j : Fin 3)
    (y : TorusCoordinateComplement)
    (hu : ContDiff ℝ 2 (torusLift u)) :
    ContDiff ℝ 1
      (torusCoordinateSliceLift
        (fun x => periodicFirstDerivative u k j x) i y) := by
  let x₀ : Torus3 := i.insertNth 0 y
  let line : ℝ → Vec3 := fun s =>
    coordinateLine (torus3Representative x₀) i s
  have hpartial : ContDiff ℝ 1
      (fun z => euclideanPartial (torusLift u) k z) :=
    hu.euclideanPartial k
  have hcomponent : ContDiff ℝ 1
      (fun z => euclideanPartial (torusLift u) k z j) :=
    ContDiff.continuousLinearMap_comp (EuclideanSpace.proj j) hpartial
  have hline : ContDiff ℝ 1
      (fun s => euclideanPartial (torusLift u) k (line s) j) :=
    hcomponent.comp (by unfold line coordinateLine; fun_prop)
  convert hline using 1
  funext s
  let z : Torus3 :=
    i.insertNth (s : AddCircle ((2 : ℝ) * Real.pi)) y
  have hmkLine : torus3Mk (line s) = z := by
    dsimp [line, z]
    rw [torus3Mk_coordinateLine_representative]
    simp [x₀, torus3Representative]
  have hrepLine :
      torus3Mk (torus3Representative z) = torus3Mk (line s) := by
    rw [torus3Mk_representative, hmkLine]
  have hfd := fderiv_torusLift_eq_of_torus3Mk_eq u
    (hu.of_le (by norm_num)) hrepLine
  change periodicFirstDerivative u k j z =
    euclideanPartial (torusLift u) k (line s) j
  rw [show periodicFirstDerivative u k j z = torusPartial u z k j by
    exact torusCoordinateDerivative_component_eq_torusPartial
      u k j z (hu.of_le (by norm_num))]
  exact congrArg
    (fun D : Vec3 →L[ℝ] Vec3 => D (EuclideanSpace.single k (1 : ℝ)) j)
    hfd

/-- Iterating the concrete quotient-coordinate derivative agrees with the
corresponding entry of the Euclidean Hessian at the measurable `Ioc`
representative. -/
theorem periodicSecondDerivative_eq_euclideanHessian_iocRepresentative
    (u : C(Torus3, Vec3)) (i k j : Fin 3) (x : Torus3)
    (hu : ContDiff ℝ 2 (torusLift u)) :
    periodicSecondDerivative u i k j x =
      euclideanHessian (torusLift u) (torus3IocRepresentative x) i k j := by
  rw [periodicSecondDerivative,
    torusCoordinateDerivative_eq_deriv_slice_iocRepresentative]
  let q : ℝ → ℝ :=
    torusCoordinateSliceLift
      (fun z => periodicFirstDerivative u k j z) i (Fin.removeNth i x)
  let r : ℝ := torus3IocRepresentative x i
  let e : Vec3 := EuclideanSpace.single i (1 : ℝ)
  have hshift : deriv q r = deriv (fun s : ℝ => q (r + s)) 0 := by
    rw [deriv_comp_const_add]
    simp
  rw [show deriv
      (torusCoordinateSliceLift
        (fun z => periodicFirstDerivative u k j z) i (Fin.removeNth i x))
      (torus3IocRepresentative x i) = deriv q r by rfl, hshift]
  have hfun : (fun s : ℝ => q (r + s)) = fun s =>
      euclideanPartial (torusLift u) k
        (torus3IocRepresentative x + s • e) j := by
    funext s
    let z : Torus3 := i.insertNth
      ((r + s : ℝ) : AddCircle ((2 : ℝ) * Real.pi))
      (Fin.removeNth i x)
    have hmk : torus3Mk (torus3IocRepresentative x + s • e) = z := by
      change torus3Mk (coordinateLine (torus3IocRepresentative x) i s) = z
      rw [torus3Mk_coordinateLine_iocRepresentative]
    have hmkIoc : torus3Mk (torus3IocRepresentative z) = z := by
      ext l
      change (((AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (z l) : ℝ) :
        AddCircle ((2 : ℝ) * Real.pi))) = z l
      exact AddCircle.coe_equivIoc
    have hrep : torus3Mk (torus3IocRepresentative z) =
        torus3Mk (torus3IocRepresentative x + s • e) := by
      exact hmkIoc.trans hmk.symm
    have hfd := fderiv_torusLift_eq_of_torus3Mk_eq u
      (hu.of_le (by norm_num)) hrep
    change periodicFirstDerivative u k j z =
      euclideanPartial (torusLift u) k
        (torus3IocRepresentative x + s • e) j
    rw [periodicFirstDerivative_eq_torusFDerivIoc_apply_single
      u k j z (hu.of_le (by norm_num))]
    exact congrArg
      (fun D : Vec3 →L[ℝ] Vec3 => D (EuclideanSpace.single k (1 : ℝ)) j)
      hfd
  rw [hfun]
  have hpartial : ContDiff ℝ 1
      (fun y => euclideanPartial (torusLift u) k y) :=
    hu.euclideanPartial k
  have hcomponent : DifferentiableAt ℝ
      (fun y => euclideanPartial (torusLift u) k y j)
      (torus3IocRepresentative x + (0 : ℝ) • e) := by
    exact ((ContDiff.continuousLinearMap_comp
      (EuclideanSpace.proj j) hpartial).differentiable (by norm_num)).differentiableAt
  have hline := hcomponent.deriv_comp_add_smul
    (x := torus3IocRepresentative x) (y := e) (t := (0 : ℝ))
  have hline' : deriv (fun s : ℝ =>
      euclideanPartial (torusLift u) k
        (torus3IocRepresentative x + s • e) j) 0 =
      euclideanPartial
        (fun y => euclideanPartial (torusLift u) k y j) i
        (torus3IocRepresentative x) := by
    simpa [euclideanPartial, e] using hline
  have hpartialAt : DifferentiableAt ℝ
      (fun y => euclideanPartial (torusLift u) k y)
      (torus3IocRepresentative x) :=
    (hpartial.differentiable (by norm_num)).differentiableAt
  have hcompEq := euclideanPartial_component hpartialAt i j
  simpa [euclideanHessian, e] using (hline'.trans hcompEq)

/-- Mixed concrete second derivatives of a `C²` periodic field commute. -/
theorem periodicSecondDerivative_comm_of_contDiff
    (u : C(Torus3, Vec3)) (hu : ContDiff ℝ 2 (torusLift u))
    (i k j : Fin 3) (x : Torus3) :
    periodicSecondDerivative u i k j x =
      periodicSecondDerivative u k i j x := by
  rw [periodicSecondDerivative_eq_euclideanHessian_iocRepresentative
      u i k j x hu,
    periodicSecondDerivative_eq_euclideanHessian_iocRepresentative
      u k i j x hu]
  exact euclideanHessian_symm hu _ i k j

/-- Every concrete mixed second derivative of a `C²` periodic vector field
is integrable on the physical torus. -/
theorem integrable_periodicSecondDerivative_of_contDiff
    (u : C(Torus3, Vec3)) (i k j : Fin 3)
    (hu : ContDiff ℝ 2 (torusLift u)) :
    Integrable (periodicSecondDerivative u i k j) := by
  let D₂ : Vec3 → ℝ := fun y =>
    euclideanHessian (torusLift u) y i k j
  have hfirst : ContDiff ℝ 1
      (fun y => euclideanPartial (torusLift u) k y) :=
    hu.euclideanPartial k
  have hsecond : ContDiff ℝ 0
      (fun y => euclideanPartial
        (fun z => euclideanPartial (torusLift u) k z) i y) :=
    hfirst.euclideanPartial i
  have hD₂ : Continuous D₂ := by
    dsimp [D₂, euclideanHessian]
    exact (ContDiff.continuousLinearMap_comp
      (EuclideanSpace.proj j) hsecond).continuous
  have hcompact : IsCompact
      (Metric.closedBall torus3FundamentalCubeCenter
        torusSobolevCutoff.rIn) :=
    isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hD₂.norm.continuousOn
  have hrepCube : ∀ x : Torus3,
      torus3IocRepresentative x ∈ torus3FundamentalCube := by
    intro x l
    change (torus3MeasurableEquivFundamentalCube x).1 l ∈
      Ioc 0 ((2 : ℝ) * Real.pi)
    simpa only [zero_add] using
      (torus3MeasurableEquivFundamentalCube x).2 l
  have hbound : ∀ x : Torus3,
      ‖D₂ (torus3IocRepresentative x)‖ ≤ C := by
    intro x
    apply hC
    exact ⟨torus3IocRepresentative x,
      torus3FundamentalCube_subset_cutoff_closedBall (hrepCube x), rfl⟩
  have hmem : MemLp (fun x : Torus3 =>
      D₂ (torus3IocRepresentative x)) 1 volume :=
    MemLp.of_bound
      (hD₂.measurable.comp
        measurable_torus3IocRepresentative).aestronglyMeasurable
      C (Eventually.of_forall hbound)
  have hint : Integrable (fun x : Torus3 =>
      D₂ (torus3IocRepresentative x)) :=
    hmem.integrable (by norm_num)
  exact hint.congr (Eventually.of_forall fun x =>
    (periodicSecondDerivative_eq_euclideanHessian_iocRepresentative
      u i k j x hu).symm)

/-- Every smooth descended first derivative belongs to every finite `Lᵖ`
space.  The proof bounds the continuous Euclidean derivative on the compact
closed ball containing the chosen fundamental-domain representatives. -/
theorem memLp_torusFDerivIoc_of_contDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (f : C(Torus3, F)) (p : ENNReal)
    (hf : ContDiff ℝ 1 (torusLift f)) :
    MemLp (torusFDerivIoc f) p volume := by
  have hcompact : IsCompact
      (Metric.closedBall torus3FundamentalCubeCenter
        torusSobolevCutoff.rIn) :=
    isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image
    (hf.continuous_fderiv one_ne_zero).norm.continuousOn
  have hrepCube : ∀ x : Torus3,
      torus3IocRepresentative x ∈ torus3FundamentalCube := by
    intro x i
    change (torus3MeasurableEquivFundamentalCube x).1 i ∈
      Ioc 0 ((2 : ℝ) * Real.pi)
    simpa only [zero_add] using
      (torus3MeasurableEquivFundamentalCube x).2 i
  have hbound : ∀ x : Torus3, ‖torusFDerivIoc f x‖ ≤ C := by
    intro x
    apply hC
    exact ⟨torus3IocRepresentative x,
      torus3FundamentalCube_subset_cutoff_closedBall (hrepCube x), rfl⟩
  exact MemLp.of_bound (aestronglyMeasurable_torusFDerivIoc f hf) C
    (Eventually.of_forall hbound)

/-- Every squared coordinate derivative of a smooth periodic vector field is
integrable on the physical torus. -/
theorem integrable_periodicFirstDerivative_sq_of_contDiff
    (u : C(Torus3, Vec3)) (i j : Fin 3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    Integrable (fun x : Torus3 => periodicFirstDerivative u i j x ^ 2) := by
  let e : Vec3 := EuclideanSpace.single i (1 : ℝ)
  have hD : MemLp (torusFDerivIoc u) 2 volume :=
    memLp_torusFDerivIoc_of_contDiff u 2 hu
  have hEval : MemLp (fun x : Torus3 => torusFDerivIoc u x e) 2 volume :=
    hD.continuousLinearMap_comp ((ContinuousLinearMap.apply ℝ Vec3) e)
  have hEntry : MemLp (fun x : Torus3 => torusFDerivIoc u x e j) 2 volume :=
    by
      simpa using hEval.continuousLinearMap_comp
        (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
  have hperiodicMeas : AEStronglyMeasurable (fun x : Torus3 =>
      periodicFirstDerivative u i j x) volume := by
    have hA : AEStronglyMeasurable (fun x : Torus3 =>
        torusFDerivIoc u x e) volume :=
      (aestronglyMeasurable_torusFDerivIoc u hu).apply_continuousLinearMap e
    have hentry : AEStronglyMeasurable (fun x : Torus3 =>
        torusFDerivIoc u x e j) volume :=
      (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hA
    exact hentry.congr (Eventually.of_forall fun x =>
      (periodicFirstDerivative_eq_torusFDerivIoc_apply_single
        u i j x hu).symm)
  have hperiodic : MemLp (fun x : Torus3 =>
      periodicFirstDerivative u i j x) 2 volume :=
    hEntry.congr_norm hperiodicMeas (Eventually.of_forall fun x => by
      rw [periodicFirstDerivative_eq_torusFDerivIoc_apply_single u i j x hu])
  exact (memLp_two_iff_integrable_sq hperiodicMeas).1 hperiodic

/-- A descended coordinate derivative is genuinely measurable, not merely
almost-everywhere measurable. -/
@[fun_prop]
theorem measurable_periodicFirstDerivative_of_contDiff
    (u : C(Torus3, Vec3)) (i j : Fin 3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    Measurable (fun x : Torus3 => periodicFirstDerivative u i j x) := by
  have hD : Measurable (torusFDerivIoc u) :=
    (hu.continuous_fderiv one_ne_zero).measurable.comp
      measurable_torus3IocRepresentative
  have hEval : Measurable (fun x : Torus3 =>
      torusFDerivIoc u x (EuclideanSpace.single i (1 : ℝ))) :=
    hD.apply_continuousLinearMap _
  have hEntry : Measurable (fun x : Torus3 =>
      torusFDerivIoc u x (EuclideanSpace.single i (1 : ℝ)) j) :=
    (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ).measurable.comp hEval
  have hfun : (fun x : Torus3 => periodicFirstDerivative u i j x) =
      fun x : Torus3 =>
        torusFDerivIoc u x (EuclideanSpace.single i (1 : ℝ)) j := by
    funext x
    exact periodicFirstDerivative_eq_torusFDerivIoc_apply_single u i j x hu
  rw [hfun]
  exact hEntry

/-- The full coordinate-gradient density of a smooth periodic field is integrable. -/
theorem integrable_periodicGradientFrobeniusSq_of_contDiff
    (u : C(Torus3, Vec3)) (hu : ContDiff ℝ 1 (torusLift u)) :
    Integrable (periodicGradientFrobeniusSq u) := by
  unfold periodicGradientFrobeniusSq
  exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
    MeasureTheory.integrable_finsetSum Finset.univ fun j _ =>
      integrable_periodicFirstDerivative_sq_of_contDiff u i j hu

/-- The periodic div--curl energy identity is automatic for a `C²`
incompressible velocity and its concrete curl.  Every slice, mixed-partial,
and integrability premise of the coordinate integration proof is discharged
from smoothness and compactness. -/
theorem torusGradientEnergy_eq_torusVectorSecondMoment_of_curl_of_contDiff
    (u w : C(Torus3, Vec3))
    (hu : ContDiff ℝ 2 (torusLift u))
    (hwCurl : ∀ x : Torus3, w x = torusCurl u x)
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0) :
    torusGradientEnergy u = torusVectorSecondMoment w := by
  have hu₁ : ContDiff ℝ 1 (torusLift u) := hu.of_le (by norm_num)
  apply torusGradientEnergy_eq_torusVectorSecondMoment_of_curl_divergence_mixed
    u w hu₁ hwCurl
  · exact fun i j y =>
      contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
        u i j y hu₁
  · exact fun i k j y =>
      contDiff_torusCoordinateSliceLift_periodicFirstDerivative_of_contDiff
        u i k j y hu
  · intro i j
    have hiMeas : AEStronglyMeasurable (fun x : Torus3 =>
        periodicFirstDerivative u i j x) volume :=
      (measurable_periodicFirstDerivative_of_contDiff
        u i j hu₁).aestronglyMeasurable
    have hjMeas : AEStronglyMeasurable (fun x : Torus3 =>
        periodicFirstDerivative u j i x) volume :=
      (measurable_periodicFirstDerivative_of_contDiff
        u j i hu₁).aestronglyMeasurable
    have hi : MemLp (fun x : Torus3 =>
        periodicFirstDerivative u i j x) 2 volume :=
      (memLp_two_iff_integrable_sq hiMeas).2
        (integrable_periodicFirstDerivative_sq_of_contDiff u i j hu₁)
    have hj : MemLp (fun x : Torus3 =>
        periodicFirstDerivative u j i x) 2 volume :=
      (memLp_two_iff_integrable_sq hjMeas).2
        (integrable_periodicFirstDerivative_sq_of_contDiff u j i hu₁)
    exact hi.integrable_mul hj
  · intro i j
    have hsecond := integrable_periodicSecondDerivative_of_contDiff
      u i j i hu
    exact hsecond.bdd_mul
      (by fun_prop : Continuous (fun x : Torus3 => u x j)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        exact (PiLp.norm_apply_le (u x) j).trans
          (ContinuousMap.norm_coe_le_norm u x))
  · exact hdiv
  · exact fun i k j x =>
      periodicSecondDerivative_comm_of_contDiff u hu i k j x
  · have hint : Integrable (fun x : Torus3 => ‖w x‖ ^ 2) := by
      have hc : Continuous (fun x : Torus3 => ‖w x‖ ^ 2) :=
        w.continuous.norm.pow 2
      simpa only [IntegrableOn, Measure.restrict_univ] using
        hc.continuousOn.integrableOn_compact
          (μ := (volume : Measure Torus3))
          (isCompact_univ : IsCompact (Set.univ : Set Torus3))
    exact hint.congr (Eventually.of_forall fun x => by
      change ‖w x‖ ^ 2 = ‖periodicCoordinateCurl u x‖ ^ 2
      rw [periodicCoordinateCurl_eq_torusCurl u x hu₁, ← hwCurl x])

/-- The lifted palinstrophy density is integrable under ordinary first-order
smoothness of the periodic lift. -/
theorem integrable_torusPalinstrophyDensity_of_contDiff
    (u : C(Torus3, Vec3)) (hu : ContDiff ℝ 1 (torusLift u)) :
    Integrable (torusPalinstrophyDensity u) := by
  exact (integrable_periodicGradientFrobeniusSq_of_contDiff u hu).congr
    (Eventually.of_forall fun x =>
      (torusPalinstrophyDensity_eq_periodicGradientFrobeniusSq u x hu).symm)

/-- The zero-safe self-transport quotient is measurable for a smooth field. -/
theorem measurable_periodicVorticitySelfTransportQuotientSq_of_contDiff
    (w : C(Torus3, Vec3)) (hw : ContDiff ℝ 1 (torusLift w)) :
    Measurable (periodicVorticitySelfTransportQuotientSq w) := by
  unfold periodicVorticitySelfTransportQuotientSq
    vorticitySelfTransportQuotientJet vorticitySelfTransportJet
  fun_prop

/-- The coordinatewise self-transport vector is measurable for a smooth
periodic field. -/
theorem measurable_periodicVorticitySelfTransportVector_of_contDiff
    (w : C(Torus3, Vec3)) (hw : ContDiff ℝ 1 (torusLift w)) :
    Measurable (periodicVorticitySelfTransportVector w) := by
  have hcomponent : ∀ i : Fin 3, Measurable (fun x : Torus3 =>
      torusScalarTransport w (fun y => w y i) x) := by
    intro i
    unfold torusScalarTransport
    apply Finset.measurable_sum
    intro j _hj
    exact ((by fun_prop : Continuous (fun x : Torus3 => w x j)).measurable).mul
      (measurable_periodicFirstDerivative_of_contDiff w j i hw)
  have hraw : Measurable (fun x : Torus3 => fun i : Fin 3 =>
      torusScalarTransport w (fun y => w y i) x) :=
    measurable_pi_lambda _ hcomponent
  exact (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp hraw

/-- The zero-safe normalized self-transport vector is measurable under the
same ordinary first-order smoothness. -/
theorem measurable_periodicNormalizedVorticitySelfTransportVector_of_contDiff
    (w : C(Torus3, Vec3)) (hw : ContDiff ℝ 1 (torusLift w)) :
    Measurable (periodicNormalizedVorticitySelfTransportVector w) := by
  unfold periodicNormalizedVorticitySelfTransportVector
  exact (w.continuous.norm.measurable.inv).smul
    (measurable_periodicVorticitySelfTransportVector_of_contDiff w hw)

/-- Smoothness alone supplies the `L²` quotient input used by the exact
Cauchy factorization, because the quotient is pointwise bounded by the full
gradient density. -/
theorem memLp_sqrt_periodicVorticitySelfTransportQuotientSq_of_contDiff
    (w : C(Torus3, Vec3)) (hw : ContDiff ℝ 1 (torusLift w)) :
    MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq w x)) 2 volume := by
  have hQmeas :=
    measurable_periodicVorticitySelfTransportQuotientSq_of_contDiff w hw
  have hGint := integrable_periodicGradientFrobeniusSq_of_contDiff w hw
  have hQint : Integrable
      (periodicVorticitySelfTransportQuotientSq w) := by
    apply hGint.mono' hQmeas.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (periodicVorticitySelfTransportQuotientSq_nonneg w x)]
      exact periodicVorticitySelfTransportQuotientSq_le_gradientFrobeniusSq w x
  have hsqrtMeas : AEStronglyMeasurable (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq w x)) volume :=
    (Real.continuous_sqrt.measurable.comp hQmeas).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hsqrtMeas).2
  simpa only [Real.sq_sqrt
    (periodicVorticitySelfTransportQuotientSq_nonneg w _)] using hQint

/-- A scalar descended coordinate derivative is integrable on the compact torus. -/
theorem integrable_torusCoordinateDerivative_of_contDiff
    (f : C(Torus3, ℝ)) (i : Fin 3)
    (hf : ContDiff ℝ 1 (torusLift f)) :
    Integrable (torusCoordinateDerivative f i) := by
  let e : Vec3 := EuclideanSpace.single i (1 : ℝ)
  have hD : MemLp (torusFDerivIoc f) 1 volume :=
    memLp_torusFDerivIoc_of_contDiff f 1 hf
  have hEval : MemLp (fun x : Torus3 => torusFDerivIoc f x e) 1 volume :=
    hD.continuousLinearMap_comp ((ContinuousLinearMap.apply ℝ ℝ) e)
  have hcoordMeas : AEStronglyMeasurable
      (torusCoordinateDerivative f i) volume := by
    have hA : AEStronglyMeasurable (fun x : Torus3 =>
        torusFDerivIoc f x e) volume :=
      (aestronglyMeasurable_torusFDerivIoc f hf).apply_continuousLinearMap e
    exact hA.congr (Eventually.of_forall fun x =>
      (torusCoordinateDerivative_eq_torusFDerivIoc_apply_single
        f i x hf).symm)
  have hcoord : MemLp (torusCoordinateDerivative f i) 1 volume :=
    hEval.congr_norm hcoordMeas (Eventually.of_forall fun x => by
      rw [torusCoordinateDerivative_eq_torusFDerivIoc_apply_single f i x hf])
  exact hcoord.integrable (by norm_num)

/-- Half-squared magnitude preserves smoothness of a periodic lift. -/
theorem contDiff_torusLift_vorticityEnergyField
    {n : WithTop ℕ∞} (w : C(Torus3, Vec3))
    (hw : ContDiff ℝ n (torusLift w)) :
    ContDiff ℝ n (torusLift (vorticityEnergyField w)) := by
  change ContDiff ℝ n (fun y => vorticityEnergy (torusLift w y))
  simpa [vorticityEnergy, real_inner_self_eq_norm_sq] using
    (hw.inner ℝ hw).div_const (2 : ℝ)

/-- Coordinate transport of a smooth scalar by a continuous periodic vector
field is integrable. -/
theorem integrable_torusScalarTransport_of_contDiff
    (u : C(Torus3, Vec3)) (f : C(Torus3, ℝ))
    (hf : ContDiff ℝ 1 (torusLift f)) :
    Integrable (torusScalarTransport u f) := by
  unfold torusScalarTransport
  exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ => by
    have hderiv := integrable_torusCoordinateDerivative_of_contDiff f i hf
    apply hderiv.bdd_mul
    · exact (by fun_prop : Continuous (fun x : Torus3 => u x i)).aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        calc
          ‖u x i‖ ≤ ‖u x‖ := PiLp.norm_apply_le (u x) i
          _ ≤ ‖u‖ := ContinuousMap.norm_coe_le_norm u x

/-- A smooth divergence-free periodic velocity has zero integral against the
transport of any smooth periodic scalar.  All Fubini obligations are derived
from compactness and smoothness here. -/
theorem integral_torusScalarTransport_eq_zero_of_contDiff
    (u : C(Torus3, Vec3)) (f : C(Torus3, ℝ))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hf : ContDiff ℝ 1 (torusLift f))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0) :
    (∫ x : Torus3, torusScalarTransport u f x) = 0 := by
  apply integral_torusScalarTransport_eq_zero u f
  · intro i y
    exact contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
      u i i y hu
  · intro i y
    exact contDiff_torusCoordinateSliceLift_of_contDiff_torusLift f i y hf
  · intro i
    have hderiv := integrable_torusCoordinateDerivative_of_contDiff f i hf
    simpa only [one_mul] using hderiv.bdd_mul
      (by fun_prop : Continuous (fun x : Torus3 => u x i)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        calc
          ‖u x i‖ ≤ ‖u x‖ := PiLp.norm_apply_le (u x) i
          _ ≤ ‖u‖ := ContinuousMap.norm_coe_le_norm u x)
  · intro i
    have hdu : Integrable (fun x : Torus3 =>
        torusCoordinateDerivative (fun z => u z i) i x) := by
      simpa only [periodicFirstDerivative] using
        integrable_periodicFirstDerivative_of_integrable_sq u i i hu
          (integrable_periodicFirstDerivative_sq_of_contDiff u i i hu)
    simpa only [one_mul] using hdu.mul_bdd
      f.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)
  · exact hdiv

/-- Smooth divergence-free scalar transport is skew-adjoint in the Haar
pairing, with all slice and integrability obligations discharged from ordinary
first-order smoothness of the periodic lifts. -/
theorem integral_mul_torusScalarTransport_eq_neg_of_contDiff
    (u : C(Torus3, Vec3)) (f g : C(Torus3, ℝ))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hf : ContDiff ℝ 1 (torusLift f))
    (hg : ContDiff ℝ 1 (torusLift g))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence u x = 0) :
    (∫ x : Torus3, f x * torusScalarTransport u g x) =
      -(∫ x : Torus3, torusScalarTransport u f x * g x) := by
  apply torus3_divergenceFree_transport_skew u f g
  · intro i y
    exact contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
      u i i y hu
  · intro i y
    exact contDiff_torusCoordinateSliceLift_of_contDiff_torusLift f i y hf
  · intro i y
    exact contDiff_torusCoordinateSliceLift_of_contDiff_torusLift g i y hg
  · intro i
    have hd := integrable_torusCoordinateDerivative_of_contDiff g i hg
    apply hd.bdd_mul
    · exact (by fun_prop : Continuous
        (fun x : Torus3 => f x * u x i)).aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        calc
          ‖f x * u x i‖ ≤ ‖f‖ * ‖u x‖ := by
            rw [norm_mul]
            exact mul_le_mul
              (ContinuousMap.norm_coe_le_norm f x)
              (PiLp.norm_apply_le (u x) i)
              (norm_nonneg _) (norm_nonneg _)
          _ ≤ ‖f‖ * ‖u‖ :=
            mul_le_mul_of_nonneg_left
              (ContinuousMap.norm_coe_le_norm u x) (norm_nonneg _)
  · intro i
    let product : C(Torus3, ℝ) := f * torusVectorComponent u i
    have hucomp : ContDiff ℝ 1 (torusLift (torusVectorComponent u i)) := by
      change ContDiff ℝ 1 (fun z => torusLift u z i)
      exact ContDiff.continuousLinearMap_comp (EuclideanSpace.proj i) hu
    have hproduct : ContDiff ℝ 1 (torusLift product) := by
      change ContDiff ℝ 1 (fun z => torusLift f z * torusLift u z i)
      exact hf.mul hucomp
    have hd := integrable_torusCoordinateDerivative_of_contDiff product i hproduct
    have hmul : Integrable (fun x : Torus3 =>
        torusCoordinateDerivative product i x * g x) :=
      hd.mul_bdd g.continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm g x)
    exact hmul.congr (Eventually.of_forall fun x => by rfl)
  · exact hdiv

/-- The vector assembled from coordinatewise vorticity self-transport is
exactly the intrinsic PDE transport `(w·∇)w` for a smooth periodic field. -/
theorem periodicVorticitySelfTransportVector_eq_torusTransport
    (w : C(Torus3, Vec3)) (x : Torus3)
    (hw : ContDiff ℝ 1 (torusLift w)) :
    periodicVorticitySelfTransportVector w x = torusTransport w w x := by
  rw [torusTransport, torusDirectionalDerivative_eq_sum_partial]
  ext i
  simp only [periodicVorticitySelfTransportVector, torusScalarTransport,
    PiLp.toLp_apply]
  change (∑ j : Fin 3, w x j *
      torusCoordinateDerivative (fun y => w y i) j x) =
    ∑ j : Fin 3, w x j * torusPartial w x j i
  apply Finset.sum_congr rfl
  intro j _hj
  rw [torusCoordinateDerivative_component_eq_torusPartial w j i x hw]

/-- Pairing the concrete coordinate self-transport with vorticity recovers
the intrinsic advective production from the vorticity equation. -/
theorem inner_periodicVorticitySelfTransportVector_eq_torusVorticityTransportProduction
    (w : C(Torus3, Vec3)) (x : Torus3)
    (hw : ContDiff ℝ 1 (torusLift w)) :
    inner ℝ (w x) (periodicVorticitySelfTransportVector w x) =
      torusVorticityTransportProduction w w x := by
  rw [periodicVorticitySelfTransportVector_eq_torusTransport w x hw]
  rfl

/-- The logarithm of half-squared vorticity with a positive zero-set
regularization, packaged as a continuous scalar field on the torus. -/
def regularizedLogVorticityEnergyField
    (w : C(Torus3, Vec3)) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    C(Torus3, ℝ) :=
  ⟨fun x => Real.log (vorticityEnergyField w x + epsilon),
    ((vorticityEnergyField w).continuous.add continuous_const).log
      (fun x => (add_pos_of_nonneg_of_pos
        (vorticityEnergyField_nonneg w x) hepsilon).ne')⟩

@[simp]
theorem regularizedLogVorticityEnergyField_apply
    (w : C(Torus3, Vec3)) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (x : Torus3) :
    regularizedLogVorticityEnergyField w epsilon hepsilon x =
      Real.log (vorticityEnergyField w x + epsilon) := rfl

/-- Positive regularization makes the logarithmic energy lift as smooth as
the underlying first-order vorticity energy. -/
theorem contDiff_torusLift_regularizedLogVorticityEnergyField
    (w : C(Torus3, Vec3)) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hw : ContDiff ℝ 1 (torusLift w)) :
    ContDiff ℝ 1
      (torusLift (regularizedLogVorticityEnergyField w epsilon hepsilon)) := by
  have henergy : ContDiff ℝ 1 (torusLift (vorticityEnergyField w)) :=
    contDiff_torusLift_vorticityEnergyField w hw
  change ContDiff ℝ 1 (fun y : Vec3 =>
    Real.log (vorticityEnergy (torusLift w y) + epsilon))
  exact (henergy.add contDiff_const).log fun y =>
    (add_pos_of_nonneg_of_pos
      (vorticityEnergyField_nonneg w (torus3Mk y)) hepsilon).ne'

/-- Exact chain rule identifying transport of the regularized logarithmic
energy with vorticity self-transport production divided by the regularized
energy. -/
theorem torusScalarTransport_regularizedLogVorticityEnergyField
    (w : C(Torus3, Vec3)) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hw : ContDiff ℝ 1 (torusLift w)) (x : Torus3) :
    torusScalarTransport w
        (regularizedLogVorticityEnergyField w epsilon hepsilon) x =
      torusVorticityTransportProduction w w x /
        (vorticityEnergyField w x + epsilon) := by
  let logEnergy := regularizedLogVorticityEnergyField w epsilon hepsilon
  change torusScalarTransport w logEnergy x =
    torusVorticityTransportProduction w w x /
      (vorticityEnergyField w x + epsilon)
  have henergy : ContDiff ℝ 1 (torusLift (vorticityEnergyField w)) :=
    contDiff_torusLift_vorticityEnergyField w hw
  have hlog : ContDiff ℝ 1 (torusLift logEnergy) :=
    contDiff_torusLift_regularizedLogVorticityEnergyField
      w epsilon hepsilon hw
  have hcoord : ∀ i : Fin 3,
      torusCoordinateDerivative logEnergy i x =
        (vorticityEnergyField w x + epsilon)⁻¹ *
          torusCoordinateDerivative (vorticityEnergyField w) i x := by
    intro i
    rw [torusCoordinateDerivative_eq_torusPartial logEnergy i x hlog,
      torusCoordinateDerivative_eq_torusPartial
        (vorticityEnergyField w) i x henergy]
    change fderiv ℝ (fun y : Vec3 =>
        Real.log (vorticityEnergy (torusLift w y) + epsilon))
        (torus3Representative x) (EuclideanSpace.single i (1 : ℝ)) = _
    have henergyPlus : ContDiff ℝ 1 (fun y : Vec3 =>
        vorticityEnergy (torusLift w y) + epsilon) :=
      henergy.add contDiff_const
    have hdiff : DifferentiableAt ℝ
        (fun y : Vec3 => vorticityEnergy (torusLift w y) + epsilon)
        (torus3Representative x) :=
      (henergyPlus.differentiable one_ne_zero).differentiableAt
    have hrepNe :
        vorticityEnergy (torusLift w (torus3Representative x)) + epsilon ≠ 0 := by
      simpa [torusLift] using
        (add_pos_of_nonneg_of_pos
          (vorticityEnergyField_nonneg w x) hepsilon).ne'
    rw [fderiv.log hdiff hrepNe]
    simp only [torusLift, torus3Mk_representative]
    rw [smul_apply]
    change (vorticityEnergyField w x + epsilon)⁻¹ *
        fderiv ℝ
          (fun y : Vec3 => torusLift (vorticityEnergyField w) y + epsilon)
          (torus3Representative x) (EuclideanSpace.single i (1 : ℝ)) = _
    rw [fderiv_add_const]
    rfl
  rw [torusVorticityTransportProduction_eq_scalarTransport w w x hw]
  unfold torusScalarTransport
  simp_rw [hcoord]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Exact error identity for an arbitrary smooth localization weight.  Failure
of `phi` to be a first integral is measured only by its vorticity transport
against the regularized logarithmic vorticity energy. -/
theorem integral_mul_regularized_torusVorticityTransportProduction_div_eq_neg_transport_log
    (w : C(Torus3, Vec3)) (phi : C(Torus3, ℝ)) (epsilon : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w))
    (hphi : ContDiff ℝ 1 (torusLift phi))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hepsilon : 0 < epsilon) :
    (∫ x : Torus3, phi x *
      (torusVorticityTransportProduction w w x /
        (vorticityEnergyField w x + epsilon))) =
      -(∫ x : Torus3, torusScalarTransport w phi x *
        regularizedLogVorticityEnergyField w epsilon hepsilon x) := by
  let logEnergy := regularizedLogVorticityEnergyField w epsilon hepsilon
  have hlog : ContDiff ℝ 1 (torusLift logEnergy) :=
    contDiff_torusLift_regularizedLogVorticityEnergyField
      w epsilon hepsilon hw
  calc
    (∫ x : Torus3, phi x *
      (torusVorticityTransportProduction w w x /
        (vorticityEnergyField w x + epsilon))) =
        ∫ x : Torus3, phi x * torusScalarTransport w logEnergy x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change phi x *
            (torusVorticityTransportProduction w w x /
              (vorticityEnergyField w x + epsilon)) =
          phi x * torusScalarTransport w
            (regularizedLogVorticityEnergyField w epsilon hepsilon) x
        rw [torusScalarTransport_regularizedLogVorticityEnergyField
          w epsilon hepsilon hw x]
    _ = -(∫ x : Torus3, torusScalarTransport w phi x * logEnergy x) :=
      integral_mul_torusScalarTransport_eq_neg_of_contDiff
        w phi logEnergy hw hphi hlog hdiv

/-- The logarithmic transport error is unchanged after subtracting any
constant from the logarithm.  This removes the additive amplitude logarithm
under Navier--Stokes concentration scaling. -/
theorem integral_transport_mul_regularizedLog_eq_centered
    (w : C(Torus3, Vec3)) (phi : C(Torus3, ℝ)) (epsilon k : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w))
    (hphi : ContDiff ℝ 1 (torusLift phi))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hepsilon : 0 < epsilon) :
    (∫ x : Torus3, torusScalarTransport w phi x *
        regularizedLogVorticityEnergyField w epsilon hepsilon x) =
      ∫ x : Torus3, torusScalarTransport w phi x *
        (regularizedLogVorticityEnergyField w epsilon hepsilon x - k) := by
  let logEnergy := regularizedLogVorticityEnergyField w epsilon hepsilon
  let centeredLog : C(Torus3, ℝ) :=
    logEnergy - ContinuousMap.const Torus3 k
  have htransport : Integrable (torusScalarTransport w phi) :=
    integrable_torusScalarTransport_of_contDiff w phi hphi
  have hcenteredProduct : Integrable (fun x : Torus3 =>
      torusScalarTransport w phi x * centeredLog x) :=
    htransport.mul_bdd centeredLog.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x =>
        ContinuousMap.norm_coe_le_norm centeredLog x)
  have htransportZero : (∫ x : Torus3,
      torusScalarTransport w phi x) = 0 :=
    integral_torusScalarTransport_eq_zero_of_contDiff
      w phi hw hphi hdiv
  calc
    (∫ x : Torus3, torusScalarTransport w phi x * logEnergy x) =
        ∫ x : Torus3,
          torusScalarTransport w phi x * centeredLog x +
            k * torusScalarTransport w phi x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp [centeredLog, logEnergy]
        ring
    _ = (∫ x : Torus3,
          torusScalarTransport w phi x * centeredLog x) +
        ∫ x : Torus3, k * torusScalarTransport w phi x := by
      rw [integral_add hcenteredProduct (htransport.const_mul k)]
    _ = (∫ x : Torus3,
          torusScalarTransport w phi x * centeredLog x) +
        k * (∫ x : Torus3, torusScalarTransport w phi x) := by
      rw [integral_const_mul]
    _ = ∫ x : Torus3,
          torusScalarTransport w phi x * centeredLog x := by
      rw [htransportZero, mul_zero, add_zero]
    _ = ∫ x : Torus3, torusScalarTransport w phi x *
        (regularizedLogVorticityEnergyField w epsilon hepsilon x - k) := by
      rfl

/-- Scale-aware `L¹` bound for the approximate-first-integral error.  The
centering constant is free, so only oscillation of the regularized logarithm,
not its absolute amplitude, needs to be paid. -/
theorem abs_integral_transport_mul_regularizedLog_le_centeredSup
    (w : C(Torus3, Vec3)) (phi : C(Torus3, ℝ)) (epsilon k : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w))
    (hphi : ContDiff ℝ 1 (torusLift phi))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hepsilon : 0 < epsilon) :
    |∫ x : Torus3, torusScalarTransport w phi x *
        regularizedLogVorticityEnergyField w epsilon hepsilon x| ≤
      (∫ x : Torus3, |torusScalarTransport w phi x|) *
        ‖regularizedLogVorticityEnergyField w epsilon hepsilon -
          ContinuousMap.const Torus3 k‖ := by
  let centeredLog : C(Torus3, ℝ) :=
    regularizedLogVorticityEnergyField w epsilon hepsilon -
      ContinuousMap.const Torus3 k
  have htransport : Integrable (torusScalarTransport w phi) :=
    integrable_torusScalarTransport_of_contDiff w phi hphi
  have hcenteredProduct : Integrable (fun x : Torus3 =>
      torusScalarTransport w phi x * centeredLog x) :=
    htransport.mul_bdd centeredLog.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x =>
        ContinuousMap.norm_coe_le_norm centeredLog x)
  rw [integral_transport_mul_regularizedLog_eq_centered
    w phi epsilon k hw hphi hdiv hepsilon]
  calc
    |∫ x : Torus3, torusScalarTransport w phi x * centeredLog x| ≤
        ∫ x : Torus3,
          |torusScalarTransport w phi x * centeredLog x| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := (volume : Measure Torus3))
          (fun x : Torus3 => torusScalarTransport w phi x * centeredLog x))
    _ ≤ ∫ x : Torus3,
        |torusScalarTransport w phi x| * ‖centeredLog‖ := by
      apply integral_mono hcenteredProduct.norm
        (htransport.norm.mul_const ‖centeredLog‖)
      intro x
      change |torusScalarTransport w phi x * centeredLog x| ≤
        |torusScalarTransport w phi x| * ‖centeredLog‖
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (ContinuousMap.norm_coe_le_norm centeredLog x) (abs_nonneg _)
    _ = (∫ x : Torus3, |torusScalarTransport w phi x|) *
        ‖centeredLog‖ := by
      rw [integral_mul_const]
    _ = (∫ x : Torus3, |torusScalarTransport w phi x|) *
        ‖regularizedLogVorticityEnergyField w epsilon hepsilon -
          ContinuousMap.const Torus3 k‖ := by
      rfl

/-- A scalar first integral of a divergence-free vorticity flow annihilates
the weighted regularized logarithmic self-transport.  This prevents global
helicity cancellation between dynamically invariant vortex regions. -/
theorem integral_mul_regularized_torusVorticityTransportProduction_div_eq_zero_of_firstIntegral
    (w : C(Torus3, Vec3)) (phi : C(Torus3, ℝ)) (epsilon : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w))
    (hphi : ContDiff ℝ 1 (torusLift phi))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hfirst : ∀ x : Torus3, torusScalarTransport w phi x = 0)
    (hepsilon : 0 < epsilon) :
    (∫ x : Torus3, phi x *
      (torusVorticityTransportProduction w w x /
        (vorticityEnergyField w x + epsilon))) = 0 := by
  rw [integral_mul_regularized_torusVorticityTransportProduction_div_eq_neg_transport_log
    w phi epsilon hw hphi hdiv hepsilon]
  simp_rw [hfirst]
  simp

/-- Division by a positive regularized vorticity energy preserves
integrability of the self-transport production. -/
theorem integrable_regularized_torusVorticityTransportProduction_div_of_contDiff
    (w : C(Torus3, Vec3)) (epsilon : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w)) (hepsilon : 0 < epsilon) :
    Integrable (fun x : Torus3 =>
      torusVorticityTransportProduction w w x /
        (vorticityEnergyField w x + epsilon)) := by
  have henergy : ContDiff ℝ 1 (torusLift (vorticityEnergyField w)) :=
    contDiff_torusLift_vorticityEnergyField w hw
  have htransport : Integrable (torusVorticityTransportProduction w w) :=
    (integrable_torusScalarTransport_of_contDiff
      w (vorticityEnergyField w) henergy).congr
        (Eventually.of_forall fun x =>
          (torusVorticityTransportProduction_eq_scalarTransport w w x hw).symm)
  let denominatorInv : C(Torus3, ℝ) :=
    ⟨fun x => (vorticityEnergyField w x + epsilon)⁻¹,
      ((vorticityEnergyField w).continuous.add continuous_const).inv₀
        (fun x => (add_pos_of_nonneg_of_pos
          (vorticityEnergyField_nonneg w x) hepsilon).ne')⟩
  have hmul : Integrable (fun x : Torus3 =>
      torusVorticityTransportProduction w w x * denominatorInv x) :=
    htransport.mul_bdd denominatorInv.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm denominatorInv x)
  simpa [denominatorInv, div_eq_mul_inv] using hmul

/-- A regularized logarithmic chain rule and periodic transport cancellation.
For every positive `epsilon`, divergence-free self-transport has zero integral
after division by the regularized half-squared vorticity.  This is the
zero-safe replacement for formally dividing by `|w|²` on the vortex set. -/
theorem integral_regularized_torusVorticityTransportProduction_div_eq_zero_of_contDiff
    (w : C(Torus3, Vec3)) (epsilon : ℝ)
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0)
    (hepsilon : 0 < epsilon) :
    (∫ x : Torus3,
      torusVorticityTransportProduction w w x /
        (vorticityEnergyField w x + epsilon)) = 0 := by
  let energyPlus : C(Torus3, ℝ) :=
    vorticityEnergyField w + ContinuousMap.const Torus3 epsilon
  have henergyPlusPos : ∀ x : Torus3, 0 < energyPlus x := by
    intro x
    dsimp [energyPlus]
    exact add_pos_of_nonneg_of_pos (vorticityEnergyField_nonneg w x) hepsilon
  let logEnergy : C(Torus3, ℝ) :=
    ⟨fun x => Real.log (energyPlus x),
      energyPlus.continuous.log (fun x => (henergyPlusPos x).ne')⟩
  have henergy : ContDiff ℝ 1 (torusLift (vorticityEnergyField w)) :=
    contDiff_torusLift_vorticityEnergyField w hw
  have henergyPlus : ContDiff ℝ 1 (torusLift energyPlus) := by
    change ContDiff ℝ 1
      (fun y : Vec3 => vorticityEnergy (torusLift w y) + epsilon)
    exact henergy.add contDiff_const
  have hlog : ContDiff ℝ 1 (torusLift logEnergy) := by
    change ContDiff ℝ 1 (fun y : Vec3 => Real.log (torusLift energyPlus y))
    exact henergyPlus.log (fun y => (henergyPlusPos (torus3Mk y)).ne')
  have hcoord : ∀ (i : Fin 3) (x : Torus3),
      torusCoordinateDerivative logEnergy i x =
        (energyPlus x)⁻¹ *
          torusCoordinateDerivative (vorticityEnergyField w) i x := by
    intro i x
    rw [torusCoordinateDerivative_eq_torusPartial logEnergy i x hlog,
      torusCoordinateDerivative_eq_torusPartial
        (vorticityEnergyField w) i x henergy]
    change fderiv ℝ (fun y : Vec3 => Real.log (torusLift energyPlus y))
        (torus3Representative x) (EuclideanSpace.single i (1 : ℝ)) = _
    have hdiff : DifferentiableAt ℝ (torusLift energyPlus)
        (torus3Representative x) :=
      (henergyPlus.differentiable one_ne_zero).differentiableAt
    have hrepNe : torusLift energyPlus (torus3Representative x) ≠ 0 := by
      simpa [torusLift] using (henergyPlusPos x).ne'
    rw [fderiv.log hdiff hrepNe]
    simp only [torusLift, torus3Mk_representative]
    change ((energyPlus x)⁻¹ •
        fderiv ℝ (torusLift energyPlus) (torus3Representative x))
          (EuclideanSpace.single i (1 : ℝ)) = _
    rw [smul_apply]
    change (energyPlus x)⁻¹ *
        fderiv ℝ (torusLift energyPlus) (torus3Representative x)
          (EuclideanSpace.single i (1 : ℝ)) = _
    congr 1
    change fderiv ℝ
        (fun y : Vec3 => torusLift (vorticityEnergyField w) y + epsilon)
          (torus3Representative x) (EuclideanSpace.single i (1 : ℝ)) = _
    rw [fderiv_add_const]
    rfl
  have hpoint : ∀ x : Torus3,
      torusScalarTransport w logEnergy x =
        torusVorticityTransportProduction w w x /
          (vorticityEnergyField w x + epsilon) := by
    intro x
    rw [torusVorticityTransportProduction_eq_scalarTransport w w x hw]
    unfold torusScalarTransport
    simp_rw [hcoord]
    dsimp [energyPlus]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  calc
    (∫ x : Torus3,
      torusVorticityTransportProduction w w x /
        (vorticityEnergyField w x + epsilon)) =
        ∫ x : Torus3, torusScalarTransport w logEnergy x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (hpoint x).symm
    _ = 0 := integral_torusScalarTransport_eq_zero_of_contDiff
      w logEnergy hw hlog hdiv

/-- Vortex-stretching production is integrable whenever the differentiated
velocity lift is smooth; the two undifferentiated vorticity factors are
bounded continuous fields on the compact torus. -/
theorem integrable_torusStretchingProduction_of_contDiff
    (u w : C(Torus3, Vec3)) (hu : ContDiff ℝ 1 (torusLift u)) :
    Integrable (torusStretchingProduction u w) := by
  have hperiodic : Integrable (periodicVortexStretchingDensity u w) := by
    unfold periodicVortexStretchingDensity torusScalarTransport
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro i _hi
    have hsum : Integrable (fun x : Torus3 =>
        ∑ j : Fin 3,
          (w x i * w x j) * periodicFirstDerivative u j i x) :=
      MeasureTheory.integrable_finsetSum Finset.univ fun j _ => by
        have hdu : Integrable (fun x : Torus3 =>
            periodicFirstDerivative u j i x) :=
          integrable_periodicFirstDerivative_of_integrable_sq u j i hu
            (integrable_periodicFirstDerivative_sq_of_contDiff u j i hu)
        have hmul : Integrable (fun x : Torus3 =>
            (w x i * w x j) * periodicFirstDerivative u j i x) := by
          apply hdu.bdd_mul
          · exact (by fun_prop : Continuous
              (fun x : Torus3 => w x i * w x j)).aestronglyMeasurable
          · exact Eventually.of_forall fun x => by
              rw [norm_mul]
              exact mul_le_mul
                ((PiLp.norm_apply_le (w x) i).trans
                  (ContinuousMap.norm_coe_le_norm w x))
                ((PiLp.norm_apply_le (w x) j).trans
                  (ContinuousMap.norm_coe_le_norm w x))
                (norm_nonneg _) (norm_nonneg _)
        exact hmul
    exact hsum.congr (Eventually.of_forall fun x => by
      change (∑ j : Fin 3,
        (w x i * w x j) * periodicFirstDerivative u j i x) =
          w x i * ∑ j : Fin 3,
            w x j * torusCoordinateDerivative (fun y => u y i) j x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [periodicFirstDerivative]
      ring)
  exact hperiodic.congr (Eventually.of_forall fun x =>
    (torusStretchingProduction_eq_periodicVortexStretchingDensity u w x hu).symm)

/-- The self-transport density paired with any constant-frame velocity is integrable
under ordinary first-order smoothness of the vorticity lift. -/
theorem integrable_periodicVorticitySelfTransportDensity_centered_of_contDiff
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hw : ContDiff ℝ 1 (torusLift w)) :
    Integrable
      (periodicVorticitySelfTransportDensity (centeredVelocity u frame) w) := by
  unfold periodicVorticitySelfTransportDensity
  apply MeasureTheory.integrable_finsetSum Finset.univ
  intro i _hi
  let wcomp : C(Torus3, ℝ) := torusVectorComponent w i
  let ucomp : C(Torus3, ℝ) :=
    torusVectorComponent u i - ContinuousMap.const Torus3 (frame i)
  have hwcomp : ContDiff ℝ 1 (torusLift wcomp) := by
      dsimp [wcomp]
      change ContDiff ℝ 1 (fun z => torusLift w z i)
      exact ContDiff.continuousLinearMap_comp (EuclideanSpace.proj i) hw
  have htransport : Integrable (torusScalarTransport w wcomp) :=
    integrable_torusScalarTransport_of_contDiff w wcomp hwcomp
  have hmul : Integrable (fun x : Torus3 =>
      torusScalarTransport w wcomp x * ucomp x) := by
    apply htransport.mul_bdd
    · exact ucomp.continuous.aestronglyMeasurable
    · exact Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm ucomp x
  exact hmul.congr (Eventually.of_forall fun x => by
    rfl)

/-- Smooth periodic integration by parts identifies total stretching with minus
centered velocity paired against vorticity self-transport.  All slice and
integrability premises are discharged from smoothness and compactness. -/
theorem integral_torusStretchingProduction_eq_neg_selfTransport_of_contDiff
    (u w : C(Torus3, Vec3)) (frame : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ContDiff ℝ 1 (torusLift w))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence w x = 0) :
    (∫ x : Torus3, torusStretchingProduction u w x) =
      -∫ x : Torus3,
        periodicVorticitySelfTransportDensity (centeredVelocity u frame) w x := by
  have hwtransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => w x j) j y) :=
    fun j y => contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
      w j j y hw
  have hwslices : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => w x i) j y) :=
    fun i j y => contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
      w j i y hw
  have hucentered : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun x => centeredVelocity u frame x i) j y) := by
    intro i j y
    have hui := contDiff_torusVectorComponentSliceLift_of_contDiff_torusLift
      u j i y hu
    convert hui.sub (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => frame i)) using 1
    funext s
    rfl
  have hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((w x i) * w x j) *
        periodicFirstDerivative (centeredVelocity u frame) j i x) := by
    intro i j
    have hdu : Integrable (fun x : Torus3 =>
        periodicFirstDerivative u j i x) :=
      integrable_periodicFirstDerivative_of_integrable_sq u j i hu
        (integrable_periodicFirstDerivative_sq_of_contDiff u j i hu)
    have hbase : Integrable (fun x : Torus3 =>
        ((w x i) * w x j) * periodicFirstDerivative u j i x) := by
      apply hdu.bdd_mul
      · exact (by fun_prop : Continuous
          (fun x : Torus3 => (w x i) * w x j)).aestronglyMeasurable
      · exact Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul
            ((PiLp.norm_apply_le (w x) i).trans
              (ContinuousMap.norm_coe_le_norm w x))
            ((PiLp.norm_apply_le (w x) j).trans
              (ContinuousMap.norm_coe_le_norm w x))
            (norm_nonneg _) (norm_nonneg _)
    exact hbase.congr (Eventually.of_forall fun x =>
      congrArg (fun r : ℝ => ((w x i) * w x j) * r)
        (periodicFirstDerivative_centeredVelocity u frame j i x).symm)
  have hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => w z i * w z j) j x *
        centeredVelocity u frame x i) := by
    intro i j
    let product : C(Torus3, ℝ) :=
      torusVectorComponent w i * torusVectorComponent w j
    let ucomp : C(Torus3, ℝ) :=
      torusVectorComponent u i - ContinuousMap.const Torus3 (frame i)
    have hproduct : ContDiff ℝ 1 (torusLift product) := by
      change ContDiff ℝ 1 (fun z => torusLift w z i * torusLift w z j)
      exact
        (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj i) hw).mul
          (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj j) hw)
    have hd : Integrable (torusCoordinateDerivative product j) :=
      integrable_torusCoordinateDerivative_of_contDiff product j hproduct
    have hmul : Integrable (fun x : Torus3 =>
        torusCoordinateDerivative product j x *
          ucomp x) := by
      apply hd.mul_bdd
      · exact ucomp.continuous.aestronglyMeasurable
      · exact Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm ucomp x
    exact hmul.congr (Eventually.of_forall fun x => by rfl)
  have hkinematic := integral_periodicVortexStretching_eq_neg_selfTransport
    (centeredVelocity u frame) w hwtransport hwslices hucentered
      hleft hright hdiv
  calc
    (∫ x : Torus3, torusStretchingProduction u w x) =
        ∫ x : Torus3, periodicVortexStretchingDensity u w x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        torusStretchingProduction_eq_periodicVortexStretchingDensity u w x hu
    _ = ∫ x : Torus3,
        periodicVortexStretchingDensity (centeredVelocity u frame) w x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        (periodicVortexStretchingDensity_centeredVelocity u w frame x).symm
    _ = -∫ x : Torus3,
        periodicVorticitySelfTransportDensity (centeredVelocity u frame) w x :=
      hkinematic

/-- The coordinate-line definition of a second derivative agrees with twice
applying the Fréchet derivative in the same Euclidean basis direction. -/
theorem torusLiftCoordinateSecond_eq_fderiv_apply_fderiv_apply
    (f : C(Torus3, ℝ)) (x : Vec3) (i : Fin 3)
    (hf : ContDiff ℝ 2 (torusLift f)) :
    torusLiftCoordinateSecond f x i =
      fderiv ℝ
        (fun y : Vec3 =>
          fderiv ℝ (torusLift f) y (EuclideanSpace.single i (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ)) := by
  let e : Vec3 := EuclideanSpace.single i (1 : ℝ)
  let g : ℝ → ℝ := fun s => torusLift f (x + s • e)
  have hgDeriv : deriv g = fun s : ℝ => fderiv ℝ (torusLift f) (x + s • e) e := by
    funext s
    have hd : DifferentiableAt ℝ (torusLift f) (x + s • e) :=
      (hf.differentiable (by norm_num)).differentiableAt
    simpa [g] using hd.deriv_comp_add_smul
  have hfirst : ContDiff ℝ 1
      (fun y : Vec3 => fderiv ℝ (torusLift f) y e) := by
    have hpair := hf.contDiff_fderiv_apply (m := 1) (by norm_num)
    exact hpair.comp (contDiff_id.prodMk contDiff_const)
  have hfirstAt : DifferentiableAt ℝ
      (fun y : Vec3 => fderiv ℝ (torusLift f) y e)
      (x + (0 : ℝ) • e) := by
    simpa using (hfirst.differentiable (by norm_num)).differentiableAt
  have hline := hfirstAt.deriv_comp_add_smul
    (x := x) (y := e) (t := (0 : ℝ))
  rw [torusLiftCoordinateSecond]
  change iteratedDeriv 2 g 0 = _
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ',
    iteratedDeriv_one, hgDeriv]
  simpa [e] using hline

/-- Every descended second coordinate derivative of a `C²` periodic scalar
lift is integrable. -/
theorem integrable_torusCoordinateSecondDerivative_of_contDiff
    (f : C(Torus3, ℝ)) (i : Fin 3)
    (hf : ContDiff ℝ 2 (torusLift f)) :
    Integrable (torusCoordinateSecondDerivative f i) := by
  let e : Vec3 := EuclideanSpace.single i (1 : ℝ)
  let D₁ : Vec3 → ℝ := fun y => fderiv ℝ (torusLift f) y e
  let D₂ : Vec3 → ℝ := fun y => fderiv ℝ D₁ y e
  have hD₁ : ContDiff ℝ 1 D₁ := by
    have hpair := hf.contDiff_fderiv_apply (m := 1) (by norm_num)
    exact hpair.comp (contDiff_id.prodMk contDiff_const)
  have hD₂ : Continuous D₂ := by
    have hpair := hD₁.contDiff_fderiv_apply (m := 0) (by norm_num)
    exact (hpair.comp (contDiff_id.prodMk contDiff_const)).continuous
  have hcompact : IsCompact
      (Metric.closedBall torus3FundamentalCubeCenter
        torusSobolevCutoff.rIn) :=
    isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hD₂.norm.continuousOn
  have hrepBall : ∀ x : Torus3,
      torus3Representative x ∈
        Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rIn := by
    intro x
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hcoord : ∀ j : Fin 3,
        (torus3Representative x j - Real.pi) ^ 2 ≤ Real.pi ^ 2 := by
      intro j
      have hj := (AddCircle.equivIco
        ((2 : ℝ) * Real.pi) 0 (x j)).property
      change 0 ≤ torus3Representative x j ∧
        torus3Representative x j < 0 + (2 : ℝ) * Real.pi at hj
      nlinarith [Real.pi_pos]
    have hsq : ‖torus3Representative x - torus3FundamentalCubeCenter‖ ^ 2 ≤
        (2 * Real.pi) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change ∑ j : Fin 3,
          (torus3Representative x j - Real.pi) ^ 2 ≤ (2 * Real.pi) ^ 2
      calc
        _ ≤ ∑ _j : Fin 3, Real.pi ^ 2 :=
          Finset.sum_le_sum fun j _ => hcoord j
        _ = 3 * Real.pi ^ 2 := by norm_num
        _ ≤ (2 * Real.pi) ^ 2 := by nlinarith [sq_nonneg Real.pi]
    exact (sq_le_sq₀ (norm_nonneg _)
      (by positivity : 0 ≤ 2 * Real.pi)).mp hsq
  have hbound : ∀ x : Torus3, ‖D₂ (torus3Representative x)‖ ≤ C := by
    intro x
    apply hC
    exact ⟨torus3Representative x, hrepBall x, rfl⟩
  have hmem : MemLp (fun x : Torus3 =>
      D₂ (torus3Representative x)) 1 volume :=
    MemLp.of_bound
      (hD₂.measurable.comp measurable_torus3Representative).aestronglyMeasurable
      C (Eventually.of_forall hbound)
  have hint : Integrable (fun x : Torus3 =>
      D₂ (torus3Representative x)) := hmem.integrable (by norm_num)
  exact hint.congr (Eventually.of_forall fun x => by
    rw [← torusLiftCoordinateSecond_eq_torusCoordinateSecondDerivative f i x,
      torusLiftCoordinateSecond_eq_fderiv_apply_fderiv_apply f
        (torus3Representative x) i hf])
