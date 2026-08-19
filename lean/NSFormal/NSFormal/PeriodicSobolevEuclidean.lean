import NSFormal.PeriodicSobolev
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Euclidean transfer for periodic Sobolev estimates

This file connects the concrete Haar three-torus to a Euclidean fundamental cube.  It is the
bridge needed to apply Mathlib's proved Gagliardo--Nirenberg--Sobolev theorem to a compactly
supported cutoff of a periodic lift.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- The half-open fundamental cube in raw product coordinates. -/
def torus3RawFundamentalCube : Set (Fin 3 → ℝ) :=
  {x | ∀ i, x i ∈ Ioc 0 (0 + (2 : ℝ) * Real.pi)}

/-- The half-open fundamental cube in the Euclidean-space model used by `torusLift`. -/
def torus3FundamentalCube : Set Vec3 :=
  {x | ∀ i, x i ∈ Ioc 0 ((2 : ℝ) * Real.pi)}

/-- Coordinatewise representatives identify the physical torus measurably with its half-open
fundamental cube. -/
def torus3MeasurableEquivFundamentalCube :
    Torus3 ≃ᵐ {x : Fin 3 → ℝ // x ∈ torus3RawFundamentalCube} :=
  (MeasurableEquiv.piCongrRight fun _ : Fin 3 =>
      AddCircle.measurableEquivIoc ((2 : ℝ) * Real.pi) 0).trans
    MeasurableEquiv.subtypePiEquivPi.symm

@[simp]
theorem torus3MeasurableEquivFundamentalCube_apply (x : Torus3) :
    torus3MeasurableEquivFundamentalCube x =
      ⟨fun i => (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x i)).1,
        fun i => (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (x i)).2⟩ := rfl

@[simp]
theorem torus3MeasurableEquivFundamentalCube_symm_apply
    (y : {x : Fin 3 → ℝ // x ∈ torus3RawFundamentalCube}) :
    torus3MeasurableEquivFundamentalCube.symm y =
      fun i => (y.1 i : AddCircle ((2 : ℝ) * Real.pi)) := rfl

theorem torus3MeasurableEquivFundamentalCube_coe_symm :
    ⇑torus3MeasurableEquivFundamentalCube.symm =
      fun y i => (y.1 i : AddCircle ((2 : ℝ) * Real.pi)) := rfl

/-- The coordinatewise half-open `(0, 2π]` representative, packaged in `Vec3`.  Unlike the
`Ico` representative used for pointwise PDE definitions, this version matches the measurable
fundamental cube used by the transfer argument. -/
def torus3IocRepresentative (x : Torus3) : Vec3 :=
  WithLp.toLp 2 (torus3MeasurableEquivFundamentalCube x).1

theorem measurable_torus3IocRepresentative : Measurable torus3IocRepresentative := by
  exact (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp
    (measurable_subtype_coe.comp
      torus3MeasurableEquivFundamentalCube.measurable)

/-- The measurable fundamental-domain equivalence preserves the unnormalized Haar volume. -/
theorem torus3MeasurableEquivFundamentalCube_measurePreserving :
    MeasurePreserving torus3MeasurableEquivFundamentalCube volume
      (Measure.comap Subtype.val volume) := by
  let S : Set (Fin 3 → ℝ) := torus3RawFundamentalCube
  let q : (Fin 3 → ℝ) → Torus3 :=
    fun x i => (x i : AddCircle ((2 : ℝ) * Real.pi))
  let val : {x : Fin 3 → ℝ // x ∈ S} → Fin 3 → ℝ := Subtype.val
  have hS : MeasurableSet S := by
    unfold S torus3RawFundamentalCube
    exact MeasurableSet.univ_pi' (fun _ : Fin 3 => measurableSet_Ioc)
  have hvalMap :
      Measure.map val (Measure.comap val volume) =
        volume.restrict S := by
    exact map_comap_subtype_coe hS volume
  have hval : MeasurePreserving
      val (Measure.comap val volume) (volume.restrict S) :=
    ⟨measurable_subtype_coe, hvalMap⟩
  have hpi := measurePreserving_pi _ _ (fun _ : Fin 3 =>
    AddCircle.measurePreserving_mk ((2 : ℝ) * Real.pi) 0)
  have hsource :
      (Measure.pi fun _ : Fin 3 =>
        volume.restrict (Ioc (0 : ℝ) (0 + (2 : ℝ) * Real.pi))) =
        volume.restrict S := by
    calc
      _ = (Measure.pi fun _ : Fin 3 => volume).restrict
          (Set.univ.pi fun _ : Fin 3 =>
            Ioc (0 : ℝ) (0 + (2 : ℝ) * Real.pi)) :=
        (Measure.restrict_pi_pi (fun _ : Fin 3 => volume)
          (fun _ => Ioc (0 : ℝ) (0 + (2 : ℝ) * Real.pi))).symm
      _ = volume.restrict S := by
        rw [← MeasureTheory.volume_pi]
        congr 1
        ext x
        simp [S, torus3RawFundamentalCube]
  have htarget :
      (Measure.pi fun _ : Fin 3 =>
        (volume : Measure (AddCircle ((2 : ℝ) * Real.pi)))) =
        (volume : Measure Torus3) := MeasureTheory.volume_pi.symm
  have hq : MeasurePreserving q (volume.restrict S) volume := by
    refine ⟨hpi.measurable, ?_⟩
    rw [← hsource, ← htarget]
    exact hpi.map_eq
  have hcomp := hq.comp hval
  have heSymm : MeasurePreserving
      torus3MeasurableEquivFundamentalCube.symm
      (Measure.comap Subtype.val volume) volume := by
    have hfun : q ∘ val = ⇑torus3MeasurableEquivFundamentalCube.symm := by
      funext y i
      rfl
    rw [← hfun]
    exact hcomp
  exact MeasurePreserving.symm torus3MeasurableEquivFundamentalCube.symm heSymm

/-- The coordinatewise quotient map from the raw fundamental cube carries restricted Lebesgue
volume to Haar volume on the torus. -/
theorem torus3RawMk_measurePreserving_fundamentalCube :
    MeasurePreserving
      (fun x : Fin 3 → ℝ =>
        fun i => (x i : AddCircle ((2 : ℝ) * Real.pi)))
      (volume.restrict torus3RawFundamentalCube) volume := by
  have hpi := measurePreserving_pi _ _ (fun _ : Fin 3 =>
    AddCircle.measurePreserving_mk ((2 : ℝ) * Real.pi) 0)
  have hsource :
      (Measure.pi fun _ : Fin 3 =>
        volume.restrict (Ioc (0 : ℝ) (0 + (2 : ℝ) * Real.pi))) =
        volume.restrict torus3RawFundamentalCube := by
    calc
      _ = (Measure.pi fun _ : Fin 3 => volume).restrict
          (Set.univ.pi fun _ : Fin 3 =>
            Ioc (0 : ℝ) (0 + (2 : ℝ) * Real.pi)) :=
        (Measure.restrict_pi_pi (fun _ : Fin 3 => volume)
          (fun _ => Ioc (0 : ℝ) (0 + (2 : ℝ) * Real.pi))).symm
      _ = volume.restrict torus3RawFundamentalCube := by
        rw [← MeasureTheory.volume_pi]
        congr 1
        ext x
        simp [torus3RawFundamentalCube]
  have htarget :
      (Measure.pi fun _ : Fin 3 =>
        (volume : Measure (AddCircle ((2 : ℝ) * Real.pi)))) =
        (volume : Measure Torus3) := MeasureTheory.volume_pi.symm
  refine ⟨hpi.measurable, ?_⟩
  rw [← hsource, ← htarget]
  exact hpi.map_eq

/-- The actual quotient map `torus3Mk` is measure preserving from the Euclidean fundamental
cube to the physical torus. -/
theorem torus3Mk_measurePreserving_fundamentalCube :
    MeasurePreserving torus3Mk
      (volume.restrict torus3FundamentalCube) volume := by
  have hof := (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
    torus3RawFundamentalCube
  have hpre : (WithLp.ofLp : Vec3 → Fin 3 → ℝ) ⁻¹'
      torus3RawFundamentalCube = torus3FundamentalCube := by
    ext x
    simp [torus3RawFundamentalCube, torus3FundamentalCube]
  have hcomp := torus3RawMk_measurePreserving_fundamentalCube.comp hof
  have hfun :
      (fun x : Fin 3 → ℝ =>
        fun i => (x i : AddCircle ((2 : ℝ) * Real.pi))) ∘ WithLp.ofLp =
        torus3Mk := by
    funext x
    rfl
  simpa only [hpre, hfun] using hcomp

/-! ## Arbitrary translated period cells -/

/-- A coordinate product of arbitrary half-open intervals of one torus period. -/
def torus3RawPeriodCell (a : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {x | ∀ i, x i ∈ Ioc (a i) (a i + (2 : ℝ) * Real.pi)}

/-- The same translated period cell in the Euclidean-space model used by `torusLift`. -/
def torus3PeriodCell (a : Fin 3 → ℝ) : Set Vec3 :=
  {x | ∀ i, x i ∈ Ioc (a i) (a i + (2 : ℝ) * Real.pi)}

/-- The raw quotient map sends every translated period cell, not only the standard one, to
the torus with exactly its Haar measure. -/
theorem torus3RawMk_measurePreserving_periodCell (a : Fin 3 → ℝ) :
    MeasurePreserving
      (fun x : Fin 3 → ℝ =>
        fun i => (x i : AddCircle ((2 : ℝ) * Real.pi)))
      (volume.restrict (torus3RawPeriodCell a)) volume := by
  have hpi := measurePreserving_pi _ _ (fun i : Fin 3 =>
    AddCircle.measurePreserving_mk ((2 : ℝ) * Real.pi) (a i))
  have hsource :
      (Measure.pi fun i : Fin 3 =>
        volume.restrict (Ioc (a i) (a i + (2 : ℝ) * Real.pi))) =
        volume.restrict (torus3RawPeriodCell a) := by
    calc
      _ = (Measure.pi fun _ : Fin 3 => volume).restrict
          (Set.univ.pi fun i : Fin 3 =>
            Ioc (a i) (a i + (2 : ℝ) * Real.pi)) :=
        (Measure.restrict_pi_pi (fun _ : Fin 3 => volume)
          (fun i => Ioc (a i) (a i + (2 : ℝ) * Real.pi))).symm
      _ = volume.restrict (torus3RawPeriodCell a) := by
        rw [← MeasureTheory.volume_pi]
        congr 1
        ext x
        simp [torus3RawPeriodCell]
  have htarget :
      (Measure.pi fun _ : Fin 3 =>
        (volume : Measure (AddCircle ((2 : ℝ) * Real.pi)))) =
        (volume : Measure Torus3) := MeasureTheory.volume_pi.symm
  refine ⟨hpi.measurable, ?_⟩
  rw [← hsource, ← htarget]
  exact hpi.map_eq

/-- The Euclidean quotient map is measure preserving on every translated period cell. -/
theorem torus3Mk_measurePreserving_periodCell (a : Fin 3 → ℝ) :
    MeasurePreserving torus3Mk
      (volume.restrict (torus3PeriodCell a)) volume := by
  have hof := (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
    (torus3RawPeriodCell a)
  have hpre : (WithLp.ofLp : Vec3 → Fin 3 → ℝ) ⁻¹'
      torus3RawPeriodCell a = torus3PeriodCell a := by
    ext x
    simp [torus3RawPeriodCell, torus3PeriodCell]
  have hcomp := (torus3RawMk_measurePreserving_periodCell a).comp hof
  have hfun :
      (fun x : Fin 3 → ℝ =>
        fun i => (x i : AddCircle ((2 : ℝ) * Real.pi))) ∘ WithLp.ofLp =
        torus3Mk := by
    funext x
    rfl
  simpa only [hpre, hfun] using hcomp

/-- Torus integration equals integration of the coordinatewise periodic lift over the raw
fundamental cube. -/
theorem torus3_integral_rawFundamentalCube
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Torus3 → E) :
    (∫ x : Torus3, f x) =
      ∫ x : Fin 3 → ℝ in torus3RawFundamentalCube,
        f (fun i => (x i : AddCircle ((2 : ℝ) * Real.pi))) := by
  convert! integral_map_equiv
    (μ := volume.comap Subtype.val)
    torus3MeasurableEquivFundamentalCube.symm f
  · exact torus3MeasurableEquivFundamentalCube_measurePreserving.symm.map_eq.symm
  · unfold torus3RawFundamentalCube
    rw [← integral_subtype_comap
      (MeasurableSet.univ_pi' (fun _ : Fin 3 => measurableSet_Ioc))]
    rfl

/-- The same fundamental-domain formula in the Euclidean-space model used by the PDE lift. -/
theorem torus3_integral_fundamentalCube
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Torus3 → E) :
    (∫ x : Torus3, f x) =
      ∫ x : Vec3 in torus3FundamentalCube, torusLift f x := by
  have hpre : (WithLp.toLp 2) ⁻¹' torus3FundamentalCube =
      torus3RawFundamentalCube := by
    ext x
    simp [torus3FundamentalCube, torus3RawFundamentalCube]
  have hmk (x : Fin 3 → ℝ) :
      torus3Mk (WithLp.toLp 2 x) =
        fun i => (x i : AddCircle ((2 : ℝ) * Real.pi)) := by
    rfl
  have htransfer := (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    (torusLift f) torus3FundamentalCube
  calc
    (∫ x : Torus3, f x) =
        ∫ x : Fin 3 → ℝ in torus3RawFundamentalCube,
          f (fun i => (x i : AddCircle ((2 : ℝ) * Real.pi))) :=
      torus3_integral_rawFundamentalCube f
    _ = ∫ x : Vec3 in torus3FundamentalCube, torusLift f x := by
      simpa only [hpre, torusLift, hmk] using htransfer

/-! ## A fixed cutoff around the fundamental cube -/

/-- Center of the standard fundamental cube. -/
def torus3FundamentalCubeCenter : Vec3 :=
  WithLp.toLp 2 fun _ : Fin 3 => Real.pi

/-- A fixed smooth bump which is one on a ball large enough to contain the fundamental cube. -/
def torusSobolevCutoff : ContDiffBump torus3FundamentalCubeCenter where
  rIn := 2 * Real.pi
  rOut := 3 * Real.pi
  rIn_pos := by positivity
  rIn_lt_rOut := by nlinarith [Real.pi_pos]

/-- The fundamental cube lies in the inner ball of the fixed Sobolev cutoff. -/
theorem torus3FundamentalCube_subset_cutoff_closedBall :
    torus3FundamentalCube ⊆
      Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rIn := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hcoord : ∀ i : Fin 3, (x i - Real.pi) ^ 2 ≤ Real.pi ^ 2 := by
    intro i
    have hi := hx i
    simp only [mem_Ioc] at hi
    nlinarith [Real.pi_pos]
  have hsq : ‖x - torus3FundamentalCubeCenter‖ ^ 2 ≤
      (2 * Real.pi) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change ∑ i : Fin 3, (x i - Real.pi) ^ 2 ≤ (2 * Real.pi) ^ 2
    calc
      _ ≤ ∑ _i : Fin 3, Real.pi ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = 3 * Real.pi ^ 2 := by norm_num
      _ ≤ (2 * Real.pi) ^ 2 := by nlinarith [sq_nonneg Real.pi]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * Real.pi)).mp hsq

/-- The fixed cutoff is identically one on the fundamental cube. -/
theorem torusSobolevCutoff_eq_one_on_fundamentalCube
    {x : Vec3} (hx : x ∈ torus3FundamentalCube) :
    torusSobolevCutoff x = 1 :=
  torusSobolevCutoff.one_of_mem_closedBall
    (torus3FundamentalCube_subset_cutoff_closedBall hx)

/-- A five-period cube containing the entire outer cutoff ball, with room at both endpoints. -/
def torus3FivePeriodCube : Set Vec3 :=
  {x | ∀ i, x i ∈ Ioc
    (-2 * ((2 : ℝ) * Real.pi)) (3 * ((2 : ℝ) * Real.pi))}

/-- Left endpoint of the `j`th cell in the five-period interval, indexed from `0` to `4`. -/
def torusFivePeriodStart (j : Fin 5) : ℝ :=
  ((j : ℕ) : ℝ) * ((2 : ℝ) * Real.pi) -
    2 * ((2 : ℝ) * Real.pi)

/-- Translation vector carrying the standard period cell to the cell indexed by `k`. -/
def torus3FivePeriodShift (k : Fin 3 → Fin 5) : Vec3 :=
  WithLp.toLp 2 fun i => torusFivePeriodStart (k i)

/-- Every one of the `125` cell translations is an integer-period translation on the torus. -/
@[simp]
theorem torus3Mk_add_fivePeriodShift (k : Fin 3 → Fin 5) (x : Vec3) :
    torus3Mk (x + torus3FivePeriodShift k) = torus3Mk x := by
  ext i
  change ((x i + torusFivePeriodStart (k i) : ℝ) :
      AddCircle ((2 : ℝ) * Real.pi)) = (x i : AddCircle ((2 : ℝ) * Real.pi))
  have hs : ((torusFivePeriodStart (k i) : ℝ) :
      AddCircle ((2 : ℝ) * Real.pi)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨((k i : ℕ) : ℤ) - 2, ?_⟩
    unfold torusFivePeriodStart
    norm_num
    ring
  rw [AddCircle.coe_add, hs, add_zero]

/-- Consequently every torus lift is invariant under all `125` cell translations. -/
@[simp]
theorem torusLift_add_fivePeriodShift
    {F : Type*} (f : Torus3 → F) (k : Fin 3 → Fin 5) (x : Vec3) :
    torusLift f (x + torus3FivePeriodShift k) = torusLift f x := by
  simp [torusLift]

/-- The Fréchet derivative of a smooth torus lift has the same finite-period invariance. -/
theorem fderiv_torusLift_add_fivePeriodShift
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f))
    (k : Fin 3 → Fin 5) (x : Vec3) :
    fderiv ℝ (torusLift f) (x + torus3FivePeriodShift k) =
      fderiv ℝ (torusLift f) x := by
  let τ : Vec3 → Vec3 := fun y => y + torus3FivePeriodShift k
  have hfun : torusLift f ∘ τ = torusLift f := by
    funext y
    exact torusLift_add_fivePeriodShift f k y
  have hτ : DifferentiableAt ℝ τ x := by
    dsimp [τ]
    fun_prop
  have hflift : DifferentiableAt ℝ (torusLift f) (τ x) :=
    (hf.differentiable one_ne_zero).differentiableAt
  have hfd := congrArg (fun g : Vec3 → F => fderiv ℝ g x) hfun
  rw [fderiv_comp x hflift hτ] at hfd
  have hτfd : fderiv ℝ τ x = ContinuousLinearMap.id ℝ Vec3 := by
    dsimp [τ]
    rw [fderiv_add_const]
    exact (hasFDerivAt_id x).fderiv
  rw [hτfd, ContinuousLinearMap.comp_id] at hfd
  exact hfd

/-- The five consecutive one-period intervals cover the one-dimensional interval used above. -/
theorem exists_fivePeriodCell_of_mem_Ioc {y : ℝ}
    (hy : y ∈ Ioc
      (-2 * ((2 : ℝ) * Real.pi)) (3 * ((2 : ℝ) * Real.pi))) :
    ∃ j : Fin 5, y ∈ Ioc (torusFivePeriodStart j)
      (torusFivePeriodStart j + (2 : ℝ) * Real.pi) := by
  by_cases h0 : y ≤ -((2 : ℝ) * Real.pi)
  · refine ⟨⟨0, by decide⟩, ?_⟩
    constructor <;> norm_num [torusFivePeriodStart] at * <;>
      nlinarith [Real.pi_pos]
  by_cases h1 : y ≤ 0
  · refine ⟨⟨1, by decide⟩, ?_⟩
    constructor <;> norm_num [torusFivePeriodStart] at * <;>
      nlinarith [Real.pi_pos]
  by_cases h2 : y ≤ (2 : ℝ) * Real.pi
  · refine ⟨⟨2, by decide⟩, ?_⟩
    constructor <;> norm_num [torusFivePeriodStart] at * <;>
      nlinarith [Real.pi_pos]
  by_cases h3 : y ≤ 2 * ((2 : ℝ) * Real.pi)
  · refine ⟨⟨3, by decide⟩, ?_⟩
    constructor <;> norm_num [torusFivePeriodStart] at * <;>
      nlinarith [Real.pi_pos]
  · refine ⟨⟨4, by decide⟩, ?_⟩
    constructor <;> norm_num [torusFivePeriodStart] at * <;>
      nlinarith [Real.pi_pos]

/-- The five-period cube is covered by the `5³ = 125` translated fundamental cells. -/
theorem torus3FivePeriodCube_subset_iUnion_periodCell :
    torus3FivePeriodCube ⊆
      ⋃ k : Fin 3 → Fin 5,
        torus3PeriodCell (fun i => torusFivePeriodStart (k i)) := by
  intro x hx
  have hi : ∀ i : Fin 3, ∃ j : Fin 5,
      x i ∈ Ioc (torusFivePeriodStart j)
        (torusFivePeriodStart j + (2 : ℝ) * Real.pi) :=
    fun i => exists_fivePeriodCell_of_mem_Ioc (hx i)
  choose k hk using hi
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  exact hk

/-- On a translated period cell, the measurable `Ioc` representative is obtained by subtracting
that cell's integer-period translation vector. -/
theorem torus3IocRepresentative_torus3Mk_eq_sub_fivePeriodShift
    (k : Fin 3 → Fin 5) {x : Vec3}
    (hx : x ∈ torus3PeriodCell (fun i => torusFivePeriodStart (k i))) :
    torus3IocRepresentative (torus3Mk x) = x - torus3FivePeriodShift k := by
  have hq : torus3Mk (x - torus3FivePeriodShift k) = torus3Mk x := by
    have h := torus3Mk_add_fivePeriodShift k (x - torus3FivePeriodShift k)
    simpa using h.symm
  ext i
  have hy : x i - torusFivePeriodStart (k i) ∈
      Ioc (0 : ℝ) (0 + (2 : ℝ) * Real.pi) := by
    have hi := hx i
    change torusFivePeriodStart (k i) < x i ∧
      x i ≤ torusFivePeriodStart (k i) + (2 : ℝ) * Real.pi at hi
    constructor <;> linarith [hi.1, hi.2]
  change (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0 (torus3Mk x i) : ℝ) =
    x i - torusFivePeriodStart (k i)
  rw [← congrFun hq i]
  change (AddCircle.equivIoc ((2 : ℝ) * Real.pi) 0
    ((x i - torusFivePeriodStart (k i) : ℝ) :
      AddCircle ((2 : ℝ) * Real.pi)) : ℝ) = _
  exact AddCircle.equivIoc_coe_of_mem hy

/-- The Fréchet derivative of the periodic lift, descended measurably to the torus through the
`Ioc` representative. -/
def torusFDerivIoc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) : Torus3 → (Vec3 →L[ℝ] F) :=
  fun q => fderiv ℝ (torusLift f) (torus3IocRepresentative q)

/-- Smoothness of the Euclidean lift makes the descended derivative strongly measurable. -/
theorem aestronglyMeasurable_torusFDerivIoc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f)) :
    AEStronglyMeasurable (torusFDerivIoc f) volume := by
  exact ((hf.continuous_fderiv one_ne_zero).measurable.comp
    measurable_torus3IocRepresentative).aestronglyMeasurable

/-- On each of the `125` cells, the Euclidean derivative agrees exactly with its descended
torus field. -/
theorem fderiv_torusLift_eq_torusFDerivIoc_on_periodCell
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f))
    (k : Fin 3 → Fin 5) {x : Vec3}
    (hx : x ∈ torus3PeriodCell (fun i => torusFivePeriodStart (k i))) :
    fderiv ℝ (torusLift f) x = torusFDerivIoc f (torus3Mk x) := by
  rw [torusFDerivIoc,
    torus3IocRepresentative_torus3Mk_eq_sub_fivePeriodShift k hx]
  have hperiod := fderiv_torusLift_add_fivePeriodShift
    f hf k (x - torus3FivePeriodShift k)
  simpa using hperiod

/-- Hence the derivative factorization holds pointwise throughout the five-period cube. -/
theorem fderiv_torusLift_eq_torusFDerivIoc_on_fivePeriodCube
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f))
    {x : Vec3} (hx : x ∈ torus3FivePeriodCube) :
    fderiv ℝ (torusLift f) x = torusFDerivIoc f (torus3Mk x) := by
  have hxUnion := torus3FivePeriodCube_subset_iUnion_periodCell hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hxUnion
  exact fderiv_torusLift_eq_torusFDerivIoc_on_periodCell f hf k hk

theorem measurableSet_torus3FivePeriodCube :
    MeasurableSet torus3FivePeriodCube := by
  unfold torus3FivePeriodCube
  measurability

/-- Pushing the five-period cube to the torus counts at most its `125` period cells.  This
measure inequality is the finite-multiplicity core of the periodic cutoff argument. -/
theorem map_torus3Mk_restrict_fivePeriodCube_le :
    Measure.map torus3Mk (volume.restrict torus3FivePeriodCube) ≤
      (125 : ℝ≥0∞) • (volume : Measure Torus3) := by
  let C : (Fin 3 → Fin 5) → Set Vec3 :=
    fun k => torus3PeriodCell (fun i => torusFivePeriodStart (k i))
  have hcover : torus3FivePeriodCube ⊆ ⋃ k, C k := by
    simpa only [C] using torus3FivePeriodCube_subset_iUnion_periodCell
  have hrestrict : volume.restrict torus3FivePeriodCube ≤
      Measure.sum fun k : Fin 3 → Fin 5 => volume.restrict (C k) := by
    exact (Measure.restrict_mono_set volume hcover).trans
      Measure.restrict_iUnion_le
  calc
    Measure.map torus3Mk (volume.restrict torus3FivePeriodCube) ≤
        Measure.map torus3Mk
          (Measure.sum fun k : Fin 3 → Fin 5 => volume.restrict (C k)) :=
      Measure.map_mono hrestrict continuous_torus3Mk.measurable
    _ = Measure.sum fun k : Fin 3 → Fin 5 =>
          Measure.map torus3Mk (volume.restrict (C k)) := by
      rw [Measure.map_sum continuous_torus3Mk.measurable.aemeasurable]
    _ = Measure.sum fun _ : Fin 3 → Fin 5 => (volume : Measure Torus3) := by
      congr 1
      funext k
      exact (torus3Mk_measurePreserving_periodCell
        (fun i => torusFivePeriodStart (k i))).map_eq
    _ = (125 : ℝ≥0∞) • (volume : Measure Torus3) := by
      calc
        Measure.sum (fun _ : Fin 3 → Fin 5 => (volume : Measure Torus3)) =
            Fintype.card (Fin 3 → Fin 5) • (volume : Measure Torus3) := by
          rw [Measure.sum_fintype, Finset.sum_const, Finset.card_univ]
        _ = 125 • (volume : Measure Torus3) := by
          norm_num [Fintype.card_fun]
        _ = (125 : ℝ≥0∞) • (volume : Measure Torus3) :=
          (Nat.cast_smul_eq_nsmul ℝ≥0∞ 125 volume).symm

theorem cutoff_closedBall_subset_torus3FivePeriodCube :
    Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut ⊆
      torus3FivePeriodCube := by
  intro x hx i
  have hnorm : ‖x - torus3FundamentalCubeCenter‖ ≤ 3 * Real.pi := by
    simpa [torusSobolevCutoff, dist_eq_norm] using hx
  have hi := (PiLp.norm_apply_le (x - torus3FundamentalCubeCenter) i).trans hnorm
  have habs : |x i - Real.pi| ≤ 3 * Real.pi := by
    simpa [torus3FundamentalCubeCenter, Real.norm_eq_abs] using hi
  rw [abs_le] at habs
  constructor <;> nlinarith [Real.pi_pos]

/-- Any continuous periodic field has at most the `125`-fold measure-scaling loss when its
Euclidean lift is restricted to the five-period cube. -/
theorem eLpNorm_torusLift_restrict_fivePeriodCube_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : C(Torus3, F)) (p : ℝ≥0∞) :
    eLpNorm (torusLift f) p (volume.restrict torus3FivePeriodCube) ≤
      (125 : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm f p volume := by
  have hfmap : AEStronglyMeasurable (f : Torus3 → F)
      (Measure.map torus3Mk (volume.restrict torus3FivePeriodCube)) :=
    f.continuous.aestronglyMeasurable
  calc
    eLpNorm (torusLift f) p (volume.restrict torus3FivePeriodCube) =
        eLpNorm f p
          (Measure.map torus3Mk (volume.restrict torus3FivePeriodCube)) := by
      change eLpNorm (f ∘ torus3Mk) p
        (volume.restrict torus3FivePeriodCube) = _
      exact (eLpNorm_map_measure hfmap
        continuous_torus3Mk.measurable.aemeasurable).symm
    _ ≤ (125 : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm f p volume :=
      eLpNorm_le_of_measure_le_smul map_torus3Mk_restrict_fivePeriodCube_le

/-- The same finite-multiplicity estimate on the smaller ball that supports the cutoff. -/
theorem eLpNorm_torusLift_restrict_cutoffBall_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : C(Torus3, F)) (p : ℝ≥0∞) :
    eLpNorm (torusLift f) p
        (volume.restrict
          (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) ≤
      (125 : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm f p volume := by
  exact (eLpNorm_mono_measure (torusLift f)
    (Measure.restrict_mono_set volume
      cutoff_closedBall_subset_torus3FivePeriodCube)).trans
    (eLpNorm_torusLift_restrict_fivePeriodCube_le f p)

/-- The derivative lift obeys the same finite-multiplicity estimate, now against the genuinely
descended measurable derivative field on the torus. -/
theorem eLpNorm_fderiv_torusLift_restrict_fivePeriodCube_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (f : C(Torus3, F)) (hf : ContDiff ℝ 1 (torusLift f)) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ (torusLift f)) p
        (volume.restrict torus3FivePeriodCube) ≤
      (125 : ℝ≥0∞) ^ (1 / p).toReal *
        eLpNorm (torusFDerivIoc f) p volume := by
  have heq : eLpNorm (fderiv ℝ (torusLift f)) p
      (volume.restrict torus3FivePeriodCube) =
      eLpNorm (torusFDerivIoc f ∘ torus3Mk) p
        (volume.restrict torus3FivePeriodCube) := by
    apply eLpNorm_congr_ae
    filter_upwards
      [ae_restrict_mem measurableSet_torus3FivePeriodCube] with x hx
    exact fderiv_torusLift_eq_torusFDerivIoc_on_fivePeriodCube f hf hx
  have hgmap : AEStronglyMeasurable (torusFDerivIoc f)
      (Measure.map torus3Mk (volume.restrict torus3FivePeriodCube)) :=
    ((hf.continuous_fderiv one_ne_zero).measurable.comp
      measurable_torus3IocRepresentative).aestronglyMeasurable
  calc
    eLpNorm (fderiv ℝ (torusLift f)) p
        (volume.restrict torus3FivePeriodCube) =
        eLpNorm (torusFDerivIoc f ∘ torus3Mk) p
          (volume.restrict torus3FivePeriodCube) := heq
    _ = eLpNorm (torusFDerivIoc f) p
          (Measure.map torus3Mk (volume.restrict torus3FivePeriodCube)) :=
      (eLpNorm_map_measure hgmap
        continuous_torus3Mk.measurable.aemeasurable).symm
    _ ≤ (125 : ℝ≥0∞) ^ (1 / p).toReal *
          eLpNorm (torusFDerivIoc f) p volume :=
      eLpNorm_le_of_measure_le_smul map_torus3Mk_restrict_fivePeriodCube_le

/-- Derivative finite-multiplicity estimate on the actual cutoff support ball. -/
theorem eLpNorm_fderiv_torusLift_restrict_cutoffBall_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (f : C(Torus3, F)) (hf : ContDiff ℝ 1 (torusLift f)) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ (torusLift f)) p
        (volume.restrict
          (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) ≤
      (125 : ℝ≥0∞) ^ (1 / p).toReal *
        eLpNorm (torusFDerivIoc f) p volume := by
  exact (eLpNorm_mono_measure (fderiv ℝ (torusLift f))
    (Measure.restrict_mono_set volume
      cutoff_closedBall_subset_torus3FivePeriodCube)).trans
    (eLpNorm_fderiv_torusLift_restrict_fivePeriodCube_le f hf p)

/-- At an integer exponent, the corresponding power of the real `Lᵖ` seminorm is the
ordinary integral of the norm power. -/
theorem lpNorm_natCast_pow_eq_integral_norm_pow
    {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F]
    (g : X → F) (n : ℕ) (hn : n ≠ 0) (mu : Measure X)
    (hg : AEStronglyMeasurable g mu) :
    lpNorm g ((n : ℝ≥0) : ℝ≥0∞) mu ^ n = ∫ x, ‖g x‖ ^ n ∂mu := by
  rw [lpNorm_nnreal_eq_integral_norm_rpow
    (p := (n : ℝ≥0)) (by exact_mod_cast hn) hg]
  simp only [NNReal.coe_natCast, Real.rpow_natCast]
  exact Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _) hn

/-! ## Compatibility with the concrete coordinate derivatives -/

/-- The measured-circle coordinate derivative is the slice derivative at the `Ioc`
representative used in this file. -/
theorem torusCoordinateDerivative_eq_deriv_slice_iocRepresentative
    (f : Torus3 → ℝ) (i : Fin 3) (x : Torus3) :
    torusCoordinateDerivative f i x =
      deriv (torusCoordinateSliceLift f i (Fin.removeNth i x))
        (torus3IocRepresentative x i) := by
  have hrep : torus3IocRepresentative x i ∈
      Ioc (0 : ℝ) (0 + (2 : ℝ) * Real.pi) :=
    (torus3MeasurableEquivFundamentalCube x).2 i
  have hcoe : ((torus3IocRepresentative x i : ℝ) :
      AddCircle ((2 : ℝ) * Real.pi)) = x i := by
    exact AddCircle.coe_equivIoc
  rw [torusCoordinateDerivative, torusCoordinateSliceDerivative]
  change AddCircle.liftIoc ((2 : ℝ) * Real.pi) 0
      (deriv (torusCoordinateSliceLift f i (Fin.removeNth i x))) (x i) = _
  rw [← hcoe, AddCircle.liftIoc_coe_apply hrep]

/-- Moving along a coordinate line based at the `Ioc` representative is the corresponding
coordinate slice of the quotient torus. -/
theorem torus3Mk_coordinateLine_iocRepresentative
    (x : Torus3) (i : Fin 3) (s : ℝ) :
    torus3Mk (coordinateLine (torus3IocRepresentative x) i s) =
      i.insertNth
        (((torus3IocRepresentative x i + s : ℝ) :
          AddCircle ((2 : ℝ) * Real.pi)))
        (Fin.removeNth i x) := by
  symm
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [torus3Mk, coordinateLine]
  · ext j
    simp [Fin.removeNth_apply, torus3Mk, coordinateLine,
      torus3IocRepresentative]

/-- A scalar coordinate derivative is exactly the descended Fréchet derivative evaluated on
the corresponding Euclidean basis vector. -/
theorem torusCoordinateDerivative_eq_torusFDerivIoc_apply_single
    (f : C(Torus3, ℝ)) (i : Fin 3) (x : Torus3)
    (hf : ContDiff ℝ 1 (torusLift f)) :
    torusCoordinateDerivative f i x =
      torusFDerivIoc f x (EuclideanSpace.single i (1 : ℝ)) := by
  rw [torusCoordinateDerivative_eq_deriv_slice_iocRepresentative]
  let q : ℝ → ℝ := torusCoordinateSliceLift f i (Fin.removeNth i x)
  let r : ℝ := torus3IocRepresentative x i
  have hfun : (fun s : ℝ => q (r + s)) =
      fun s : ℝ => torusLift f
        (coordinateLine (torus3IocRepresentative x) i s) := by
    funext s
    change f (i.insertNth
        (((torus3IocRepresentative x i + s : ℝ) :
          AddCircle ((2 : ℝ) * Real.pi)))
        (Fin.removeNth i x)) =
      f (torus3Mk (coordinateLine (torus3IocRepresentative x) i s))
    rw [torus3Mk_coordinateLine_iocRepresentative]
  have hshift : deriv q r = deriv (fun s : ℝ => q (r + s)) 0 := by
    rw [deriv_comp_const_add]
    simp
  rw [show deriv (torusCoordinateSliceLift f i (Fin.removeNth i x))
      (torus3IocRepresentative x i) = deriv q r by rfl, hshift, hfun]
  have hdifferentiable : DifferentiableAt ℝ (torusLift f)
      (torus3IocRepresentative x) :=
    (hf.differentiable one_ne_zero).differentiableAt
  rw [show (fun s : ℝ => torusLift f
      (coordinateLine (torus3IocRepresentative x) i s)) =
        fun s : ℝ => torusLift f
          (torus3IocRepresentative x +
            s • EuclideanSpace.single i (1 : ℝ)) by rfl]
  have hdifferentiable0 : DifferentiableAt ℝ (torusLift f)
      (torus3IocRepresentative x +
        (0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
    simpa using hdifferentiable
  rw [hdifferentiable0.deriv_comp_add_smul]
  simp [torusFDerivIoc]

/-- Descending the derivative commutes with taking a scalar component of a vector field. -/
theorem torusFDerivIoc_vectorComponent
    (u : C(Torus3, Vec3)) (j : Fin 3) (x : Torus3) (v : Vec3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    torusFDerivIoc (torusVectorComponent u j) x v =
      torusFDerivIoc u x v j := by
  have hudiff : DifferentiableAt ℝ (torusLift u)
      (torus3IocRepresentative x) :=
    (hu.differentiable one_ne_zero).differentiableAt
  have hcomp := (EuclideanSpace.proj j).hasFDerivAt.comp
    (torus3IocRepresentative x) hudiff.hasFDerivAt
  have hfd := hcomp.fderiv
  have hfun : torusLift (torusVectorComponent u j) =
      (EuclideanSpace.proj j) ∘ torusLift u := by
    rfl
  unfold torusFDerivIoc
  rw [hfun, hfd, ContinuousLinearMap.comp_apply]
  rfl

/-- Matrix entries of the descended derivative are the concrete periodic first derivatives. -/
theorem periodicFirstDerivative_eq_torusFDerivIoc_apply_single
    (u : C(Torus3, Vec3)) (i j : Fin 3) (x : Torus3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    periodicFirstDerivative u i j x =
      torusFDerivIoc u x (EuclideanSpace.single i (1 : ℝ)) j := by
  have hucomp : ContDiff ℝ 1
      (torusLift (torusVectorComponent u j)) := by
    change ContDiff ℝ 1 (fun y => torusLift u y j)
    exact ContDiff.continuousLinearMap_comp (EuclideanSpace.proj j) hu
  unfold periodicFirstDerivative
  change torusCoordinateDerivative (torusVectorComponent u j) i x = _
  rw [torusCoordinateDerivative_eq_torusFDerivIoc_apply_single
    (torusVectorComponent u j) i x hucomp]
  exact torusFDerivIoc_vectorComponent u j x
    (EuclideanSpace.single i (1 : ℝ)) hu

/-- The coordinate-line derivative used in the enstrophy/palinstrophy calculus is the
PDE directional derivative when evaluated at the canonical representative. -/
theorem torusLiftCoordinateFirstVector_representative_eq_torusPartial
    (u : C(Torus3, Vec3)) (x : Torus3) (i : Fin 3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    torusLiftCoordinateFirstVector u (torus3Representative x) i =
      torusPartial u x i := by
  have hudiff : DifferentiableAt ℝ (torusLift u) (torus3Representative x) :=
    (hu.differentiable one_ne_zero).differentiableAt
  have hudiff0 : DifferentiableAt ℝ (torusLift u)
      (torus3Representative x +
        (0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
    simpa using hudiff
  unfold torusLiftCoordinateFirstVector
  rw [show (fun s : ℝ =>
      torusLift u (coordinateLine (torus3Representative x) i s)) =
        fun s : ℝ => torusLift u
          (torus3Representative x +
            s • EuclideanSpace.single i (1 : ℝ)) by rfl]
  rw [hudiff0.deriv_comp_add_smul]
  simp [torusPartial, torusDirectionalDerivative]

/-- The palinstrophy density and the coordinate-gradient Frobenius density are exactly the
same quantity.  This identifies the two derivative conventions developed independently in
the enstrophy and periodic-integration layers. -/
theorem torusPalinstrophyDensity_eq_periodicGradientFrobeniusSq
    (u : C(Torus3, Vec3)) (x : Torus3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    torusPalinstrophyDensity u x = periodicGradientFrobeniusSq u x := by
  unfold torusPalinstrophyDensity torusLiftGradientSq
    periodicGradientFrobeniusSq
  apply Finset.sum_congr rfl
  intro i _hi
  rw [torusLiftCoordinateFirstVector_representative_eq_torusPartial u x i hu,
    EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← torusCoordinateDerivative_component_eq_torusPartial u i j x hu]
  rfl

/-- Square-integrability of one periodic gradient entry implies its integrability.  The
measurability input comes from the descended Fréchet derivative, while finiteness of Haar
volume supplies the `L² ⊆ L¹` inclusion. -/
theorem integrable_periodicFirstDerivative_of_integrable_sq
    (u : C(Torus3, Vec3)) (i j : Fin 3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hsq : Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2)) :
    Integrable (fun x : Torus3 => periodicFirstDerivative u i j x) := by
  have hA : AEStronglyMeasurable (fun x : Torus3 =>
      torusFDerivIoc u x (EuclideanSpace.single i (1 : ℝ))) volume :=
    (aestronglyMeasurable_torusFDerivIoc u hu).apply_continuousLinearMap
      (EuclideanSpace.single i (1 : ℝ))
  have hentry : AEStronglyMeasurable (fun x : Torus3 =>
      torusFDerivIoc u x (EuclideanSpace.single i (1 : ℝ)) j) volume :=
    (EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable hA
  have hperiodic : AEStronglyMeasurable (fun x : Torus3 =>
      periodicFirstDerivative u i j x) volume :=
    hentry.congr (Eventually.of_forall fun x =>
      (periodicFirstDerivative_eq_torusFDerivIoc_apply_single u i j x hu).symm)
  exact ((memLp_two_iff_integrable_sq hperiodic).2 hsq).integrable (by norm_num)

/-- Every square-integrable derivative of a smooth periodic component has zero spatial
mean.  This is the three-dimensional boundary cancellation with the other factor set to
the constant one field. -/
theorem integral_periodicFirstDerivative_eq_zero
    (u : C(Torus3, Vec3)) (i j : Fin 3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hslice : ∀ y : TorusCoordinateComplement,
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hsq : Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2)) :
    (∫ x : Torus3, periodicFirstDerivative u i j x) = 0 := by
  have hint : Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x) :=
    integrable_periodicFirstDerivative_of_integrable_sq u i j hu hsq
  have hparts := torus3_integral_mul_coordinateDerivative_eq_neg
    (fun _ : Torus3 => (1 : ℝ)) (fun x => u x j) i
    (fun _ => contDiff_const) hslice
    (by simpa [periodicFirstDerivative] using hint)
    (by simp)
  simpa [periodicFirstDerivative] using hparts

/-- A classical periodic curl has zero mean in every component.  This is proved from the
coordinate boundary cancellation rather than assumed as an extra normalization. -/
theorem integral_torusCurl_component_eq_zero
    (u : C(Torus3, Vec3)) (j : Fin 3)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hslice : ∀ (i k : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x k) i y))
    (hsq : ∀ i k : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i k x ^ 2)) :
    (∫ x : Torus3, torusCurl u x j) = 0 := by
  have hint : ∀ i k : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i k x) := fun i k =>
    integrable_periodicFirstDerivative_of_integrable_sq u i k hu (hsq i k)
  have hzero : ∀ i k : Fin 3,
      (∫ x : Torus3, periodicFirstDerivative u i k x) = 0 := fun i k =>
    integral_periodicFirstDerivative_eq_zero u i k hu (hslice i k) (hsq i k)
  calc
    (∫ x : Torus3, torusCurl u x j) =
        ∫ x : Torus3, periodicCoordinateCurl u x j := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        exact congrArg (fun z : Vec3 => z j)
          (periodicCoordinateCurl_eq_torusCurl u x hu).symm
    _ = 0 := by
      fin_cases j
      · change (∫ x : Torus3,
            periodicFirstDerivative u 1 2 x -
              periodicFirstDerivative u 2 1 x) = 0
        rw [integral_sub (hint 1 2) (hint 2 1), hzero, hzero, sub_self]
      · change (∫ x : Torus3,
            periodicFirstDerivative u 2 0 x -
              periodicFirstDerivative u 0 2 x) = 0
        rw [integral_sub (hint 2 0) (hint 0 2), hzero, hzero, sub_self]
      · change (∫ x : Torus3,
            periodicFirstDerivative u 0 1 x -
              periodicFirstDerivative u 1 0 x) = 0
        rw [integral_sub (hint 0 1) (hint 1 0), hzero, hzero, sub_self]

/-- Any continuous field identified pointwise with the curl inherits the zero-mean condition
needed by the homogeneous periodic Sobolev theorem. -/
theorem torusCurlField_mean_zero
    (u w : C(Torus3, Vec3))
    (hw : ∀ x : Torus3, w x = torusCurl u x)
    (hu : ContDiff ℝ 1 (torusLift u))
    (hslice : ∀ (i k : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x k) i y))
    (hsq : ∀ i k : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i k x ^ 2)) :
    ∀ j : Fin 3, (∫ x : Torus3, w x j) = 0 := by
  intro j
  calc
    (∫ x : Torus3, w x j) = ∫ x : Torus3, torusCurl u x j := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => congrArg (fun z : Vec3 => z j) (hw x)
    _ = 0 := integral_torusCurl_component_eq_zero u j hu hslice hsq

/-- In dimension three, the operator norm is bounded by the sum of the images of the standard
basis vectors. -/
theorem norm_clm_vec3_le_sum_basis
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Vec3 →L[ℝ] F) :
    ‖A‖ ≤ ‖A (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ +
      ‖A (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))‖ +
      ‖A (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ := by
  apply A.opNorm_le_bound
  · positivity
  intro x
  have hx : x =
      x (0 : Fin 3) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      x (1 : Fin 3) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
      x (2 : Fin 3) • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hx, map_add, map_add, map_smul, map_smul, map_smul]
  calc
    ‖x (0 : Fin 3) • A (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) +
        x (1 : Fin 3) • A (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) +
        x (2 : Fin 3) • A (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ≤
        ‖x (0 : Fin 3) • A (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ +
        ‖x (1 : Fin 3) • A (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))‖ +
        ‖x (2 : Fin 3) • A (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖x (0 : Fin 3)‖ *
          ‖A (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ +
        ‖x (1 : Fin 3)‖ *
          ‖A (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))‖ +
        ‖x (2 : Fin 3)‖ *
          ‖A (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ := by
      rw [norm_smul, norm_smul, norm_smul]
    _ ≤ ‖x‖ * ‖A (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ +
        ‖x‖ * ‖A (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))‖ +
        ‖x‖ * ‖A (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ := by
      gcongr <;> exact PiLp.norm_apply_le x _
    _ = (‖A (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ +
          ‖A (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))‖ +
          ‖A (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖) * ‖x‖ := by
      ring

/-- Squaring the previous estimate gives a crude but sufficient Frobenius bound. -/
theorem norm_clm_vec3_sq_le_three_mul_basis_sq_sum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Vec3 →L[ℝ] F) :
    ‖A‖ ^ 2 ≤ 3 *
      (‖A (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ ^ 2 +
        ‖A (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))‖ ^ 2 +
        ‖A (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ^ 2) := by
  have hnorm := norm_clm_vec3_le_sum_basis A
  have hsq : ‖A‖ ^ 2 ≤
      (‖A (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ +
        ‖A (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))‖ +
        ‖A (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  exact hsq.trans (sq_add_add_le_three_mul_sum_sq _ _ _)

/-- For a vector field, the descended derivative's operator norm is controlled pointwise by
the concrete Frobenius gradient density already used in the Navier--Stokes development. -/
theorem norm_torusFDerivIoc_sq_le_three_mul_periodicGradientFrobeniusSq
    (u : C(Torus3, Vec3)) (x : Torus3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    ‖torusFDerivIoc u x‖ ^ 2 ≤
      3 * periodicGradientFrobeniusSq u x := by
  have hbasis (i : Fin 3) :
      ‖torusFDerivIoc u x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
        ∑ j : Fin 3, periodicFirstDerivative u i j x ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [periodicFirstDerivative_eq_torusFDerivIoc_apply_single u i j x hu]
    simp [Real.norm_eq_abs]
  have hop := norm_clm_vec3_sq_le_three_mul_basis_sq_sum (torusFDerivIoc u x)
  rw [hbasis (0 : Fin 3), hbasis (1 : Fin 3), hbasis (2 : Fin 3)] at hop
  unfold periodicGradientFrobeniusSq
  rw [Fin.sum_univ_three]
  exact hop

/-- Componentwise square-integrability automatically supplies square-integrability of the
descended derivative operator norm. -/
theorem integrable_norm_torusFDerivIoc_sq_of_periodicFirstDerivative
    (u : C(Torus3, Vec3))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2)) :
    Integrable (fun x : Torus3 => ‖torusFDerivIoc u x‖ ^ 2) := by
  have hgrad : Integrable (fun x : Torus3 =>
      periodicGradientFrobeniusSq u x) := by
    unfold periodicGradientFrobeniusSq
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun j _ => hderiv i j
  have hmeas : AEStronglyMeasurable (fun x : Torus3 =>
      ‖torusFDerivIoc u x‖ ^ 2) volume :=
    (continuous_pow 2).comp_aestronglyMeasurable
      (continuous_norm.comp_aestronglyMeasurable
        (aestronglyMeasurable_torusFDerivIoc u hu))
  apply Integrable.mono' (hgrad.const_mul 3) hmeas
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact norm_torusFDerivIoc_sq_le_three_mul_periodicGradientFrobeniusSq u x hu

/-- Conversely, the nine coordinate entries of the Frobenius density are each bounded by the
operator norm of the descended derivative. -/
theorem periodicGradientFrobeniusSq_le_nine_mul_norm_torusFDerivIoc_sq
    (u : C(Torus3, Vec3)) (x : Torus3)
    (hu : ContDiff ℝ 1 (torusLift u)) :
    periodicGradientFrobeniusSq u x ≤
      9 * ‖torusFDerivIoc u x‖ ^ 2 := by
  have hentry (i j : Fin 3) :
      periodicFirstDerivative u i j x ^ 2 ≤
        ‖torusFDerivIoc u x‖ ^ 2 := by
    rw [periodicFirstDerivative_eq_torusFDerivIoc_apply_single u i j x hu]
    have hcomponent := PiLp.norm_apply_le
      (torusFDerivIoc u x (EuclideanSpace.single i (1 : ℝ))) j
    have hopen := (torusFDerivIoc u x).le_opNorm
      (EuclideanSpace.single i (1 : ℝ))
    have hsingle : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
    rw [hsingle, mul_one] at hopen
    have habs :
        |torusFDerivIoc u x (EuclideanSpace.single i (1 : ℝ)) j| ≤
          ‖torusFDerivIoc u x‖ := by
      rw [← Real.norm_eq_abs]
      exact hcomponent.trans hopen
    simpa [sq_abs] using
      ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 habs)
  unfold periodicGradientFrobeniusSq
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, periodicFirstDerivative u i j x ^ 2) ≤
        ∑ i : Fin 3, ∑ _j : Fin 3, ‖torusFDerivIoc u x‖ ^ 2 := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = 9 * ‖torusFDerivIoc u x‖ ^ 2 := by
      simp
      ring

/-- Componentwise tensorization of scalar Poincare gives the vector-valued mean-zero estimate
in exactly the Frobenius convention used by `torusGradientEnergy`. -/
theorem integral_torus_norm_sq_le_three_mul_period_sq_mul_gradientEnergy
    (u : C(Torus3, Vec3))
    (hmean : ∀ j : Fin 3, (∫ x : Torus3, u x j) = 0)
    (hsmooth : ∀ (j i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2)) :
    (∫ x : Torus3, ‖u x‖ ^ 2) ≤
      3 * ((2 : ℝ) * Real.pi) ^ 2 * torusGradientEnergy u := by
  let C : ℝ := 3 * ((2 : ℝ) * Real.pi) ^ 2
  have huInt (j : Fin 3) : Integrable (fun x : Torus3 => u x j ^ 2) :=
    continuous_integrable_torus3 ((torusVectorComponent u j).continuous.pow 2)
  have hcomponent (j : Fin 3) :
      (∫ x : Torus3, u x j ^ 2) ≤
        C * ∑ i : Fin 3,
          ∫ x : Torus3, periodicFirstDerivative u i j x ^ 2 := by
    have hderiv' (i : Fin 3) : Integrable (fun x : Torus3 =>
        torusCoordinateDerivative (torusVectorComponent u j) i x ^ 2) := by
      have hfun : (⇑(torusVectorComponent u j)) = (fun y : Torus3 => u y j) := rfl
      rw [hfun]
      simpa only [periodicFirstDerivative] using hderiv i j
    have h := integral_torus_sq_le_three_mul_period_sq_mul_coordinateDerivative_sum
      (torusVectorComponent u j) (hmean j) (hsmooth j)
      hderiv'
    simpa [C, torusVectorComponent, periodicFirstDerivative, Fin.sum_univ_three] using h
  have hgrad : torusGradientEnergy u =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : Torus3, periodicFirstDerivative u i j x ^ 2 := by
    unfold torusGradientEnergy periodicGradientFrobeniusSq
    calc
      (∫ x : Torus3,
          ∑ i : Fin 3, ∑ j : Fin 3,
            periodicFirstDerivative u i j x ^ 2) =
          ∑ i : Fin 3, ∫ x : Torus3,
            ∑ j : Fin 3, periodicFirstDerivative u i j x ^ 2 := by
        exact MeasureTheory.integral_finsetSum Finset.univ
          (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
            (fun j _ => hderiv i j))
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x : Torus3, periodicFirstDerivative u i j x ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact MeasureTheory.integral_finsetSum Finset.univ
          (fun j _ => hderiv i j)
  calc
    (∫ x : Torus3, ‖u x‖ ^ 2) =
        ∫ x : Torus3, ∑ j : Fin 3, u x j ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => EuclideanSpace.real_norm_sq_eq (u x)
    _ = ∑ j : Fin 3, ∫ x : Torus3, u x j ^ 2 :=
      MeasureTheory.integral_finsetSum Finset.univ (fun j _ => huInt j)
    _ ≤ ∑ j : Fin 3, C * ∑ i : Fin 3,
          ∫ x : Torus3, periodicFirstDerivative u i j x ^ 2 :=
      Finset.sum_le_sum fun j _ => hcomponent j
    _ = C * torusGradientEnergy u := by
      rw [hgrad]
      simp only [Fin.sum_univ_three]
      ring
    _ = 3 * ((2 : ℝ) * Real.pi) ^ 2 * torusGradientEnergy u := by rfl

/-- Integrated operator norm is bounded by three times the concrete Frobenius energy. -/
theorem integral_norm_torusFDerivIoc_sq_le_three_mul_gradientEnergy
    (u : C(Torus3, Vec3)) (hu : ContDiff ℝ 1 (torusLift u))
    (hD : Integrable (fun x : Torus3 => ‖torusFDerivIoc u x‖ ^ 2))
    (hgrad : Integrable (fun x : Torus3 => periodicGradientFrobeniusSq u x)) :
    (∫ x : Torus3, ‖torusFDerivIoc u x‖ ^ 2) ≤
      3 * torusGradientEnergy u := by
  unfold torusGradientEnergy
  calc
    (∫ x : Torus3, ‖torusFDerivIoc u x‖ ^ 2) ≤
        ∫ x : Torus3, 3 * periodicGradientFrobeniusSq u x := by
      exact integral_mono hD (hgrad.const_mul 3) fun x =>
        norm_torusFDerivIoc_sq_le_three_mul_periodicGradientFrobeniusSq u x hu
    _ = 3 * ∫ x : Torus3, periodicGradientFrobeniusSq u x := by
      rw [MeasureTheory.integral_const_mul]

/-- Integrated Frobenius energy is bounded by nine times the descended operator-derivative
energy. -/
theorem torusGradientEnergy_le_nine_mul_integral_norm_torusFDerivIoc_sq
    (u : C(Torus3, Vec3)) (hu : ContDiff ℝ 1 (torusLift u))
    (hD : Integrable (fun x : Torus3 => ‖torusFDerivIoc u x‖ ^ 2))
    (hgrad : Integrable (fun x : Torus3 => periodicGradientFrobeniusSq u x)) :
    torusGradientEnergy u ≤
      9 * ∫ x : Torus3, ‖torusFDerivIoc u x‖ ^ 2 := by
  unfold torusGradientEnergy
  calc
    (∫ x : Torus3, periodicGradientFrobeniusSq u x) ≤
        ∫ x : Torus3, 9 * ‖torusFDerivIoc u x‖ ^ 2 := by
      exact integral_mono hgrad (hD.const_mul 9) fun x =>
        periodicGradientFrobeniusSq_le_nine_mul_norm_torusFDerivIoc_sq u x hu
    _ = 9 * ∫ x : Torus3, ‖torusFDerivIoc u x‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul]

/-- Mean-zero vector Poincare expressed directly in the descended operator-derivative energy. -/
theorem integral_torus_norm_sq_le_twentyseven_mul_period_sq_mul_fderiv_sq
    (u : C(Torus3, Vec3))
    (hmean : ∀ j : Fin 3, (∫ x : Torus3, u x j) = 0)
    (hsmooth : ∀ (j i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hD : Integrable (fun x : Torus3 => ‖torusFDerivIoc u x‖ ^ 2)) :
    (∫ x : Torus3, ‖u x‖ ^ 2) ≤
      27 * ((2 : ℝ) * Real.pi) ^ 2 *
        ∫ x : Torus3, ‖torusFDerivIoc u x‖ ^ 2 := by
  have hgrad : Integrable (fun x : Torus3 => periodicGradientFrobeniusSq u x) := by
    unfold periodicGradientFrobeniusSq
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun j _ => hderiv i j
  have hP := integral_torus_norm_sq_le_three_mul_period_sq_mul_gradientEnergy
    u hmean hsmooth hderiv
  have hGD := torusGradientEnergy_le_nine_mul_integral_norm_torusFDerivIoc_sq
    u hu hD hgrad
  calc
    (∫ x : Torus3, ‖u x‖ ^ 2) ≤
        3 * ((2 : ℝ) * Real.pi) ^ 2 * torusGradientEnergy u := hP
    _ ≤ 3 * ((2 : ℝ) * Real.pi) ^ 2 *
          (9 * ∫ x : Torus3, ‖torusFDerivIoc u x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hGD (by positivity)
    _ = 27 * ((2 : ℝ) * Real.pi) ^ 2 *
          ∫ x : Torus3, ‖torusFDerivIoc u x‖ ^ 2 := by ring

/-- Real `L²` seminorm form of the preceding vector Poincare estimate. -/
theorem lpNorm_torus_two_le_poincareFactor_mul_fderiv_two
    (u : C(Torus3, Vec3))
    (hmean : ∀ j : Fin 3, (∫ x : Torus3, u x j) = 0)
    (hsmooth : ∀ (j i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hD : Integrable (fun x : Torus3 => ‖torusFDerivIoc u x‖ ^ 2)) :
    lpNorm u 2 volume ≤
      Real.sqrt (27 * ((2 : ℝ) * Real.pi) ^ 2) *
        lpNorm (torusFDerivIoc u) 2 volume := by
  have huSq : lpNorm u 2 volume ^ 2 = ∫ x : Torus3, ‖u x‖ ^ 2 := by
    simpa using lpNorm_natCast_pow_eq_integral_norm_pow
      u 2 (by norm_num) (volume : Measure Torus3)
        u.continuous.aestronglyMeasurable
  have hDSq : lpNorm (torusFDerivIoc u) 2 volume ^ 2 =
      ∫ x : Torus3, ‖torusFDerivIoc u x‖ ^ 2 := by
    simpa using lpNorm_natCast_pow_eq_integral_norm_pow
      (torusFDerivIoc u) 2 (by norm_num) (volume : Measure Torus3)
        (aestronglyMeasurable_torusFDerivIoc u hu)
  have hsq : lpNorm u 2 volume ^ 2 ≤
      27 * ((2 : ℝ) * Real.pi) ^ 2 *
        lpNorm (torusFDerivIoc u) 2 volume ^ 2 := by
    rw [huSq, hDSq]
    exact integral_torus_norm_sq_le_twentyseven_mul_period_sq_mul_fderiv_sq
      u hmean hsmooth hderiv hu hD
  apply (sq_le_sq₀ lpNorm_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) lpNorm_nonneg)).mp
  calc
    lpNorm u 2 volume ^ 2 ≤
        27 * ((2 : ℝ) * Real.pi) ^ 2 *
          lpNorm (torusFDerivIoc u) 2 volume ^ 2 := hsq
    _ = Real.sqrt (27 * ((2 : ℝ) * Real.pi) ^ 2) ^ 2 *
          lpNorm (torusFDerivIoc u) 2 volume ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
    _ = (Real.sqrt (27 * ((2 : ℝ) * Real.pi) ^ 2) *
          lpNorm (torusFDerivIoc u) 2 volume) ^ 2 := by ring

/-! ## Application of Euclidean Gagliardo--Nirenberg--Sobolev -/

/-- Compactly supported Euclidean extension obtained by cutting off the periodic lift. -/
def torusCutoffLift
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) (x : Vec3) : F :=
  torusSobolevCutoff x • torusLift f x

theorem torusCutoffLift_eq_on_fundamentalCube
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) {x : Vec3} (hx : x ∈ torus3FundamentalCube) :
    torusCutoffLift f x = torusLift f x := by
  simp [torusCutoffLift,
    torusSobolevCutoff_eq_one_on_fundamentalCube hx]

/-- The cutoff extension is `C¹` whenever the periodic lift is `C¹`. -/
theorem contDiff_torusCutoffLift
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f)) :
    ContDiff ℝ 1 (torusCutoffLift f) := by
  have hcutoff : ContDiff ℝ 1 (torusSobolevCutoff : Vec3 → ℝ) :=
    torusSobolevCutoff.contDiff
  exact hcutoff.smul hf

/-- The cutoff extension really has compact support, independently of the periodic field. -/
theorem hasCompactSupport_torusCutoffLift
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) : HasCompactSupport (torusCutoffLift f) := by
  exact torusSobolevCutoff.hasCompactSupport.smul_right

theorem measurableSet_torus3FundamentalCube :
    MeasurableSet torus3FundamentalCube := by
  unfold torus3FundamentalCube
  measurability

/-- The `Lᵖ` seminorm of a torus field is exactly the restricted Euclidean seminorm of its
periodic lift on one fundamental cube. -/
theorem eLpNorm_torus_eq_restrict_fundamentalCube
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : C(Torus3, F)) (p : ℝ≥0∞) :
    eLpNorm (torusLift f) p (volume.restrict torus3FundamentalCube) =
      eLpNorm f p volume := by
  change eLpNorm (f ∘ torus3Mk) p
      (volume.restrict torus3FundamentalCube) = eLpNorm f p volume
  exact eLpNorm_comp_measurePreserving (p := p)
    f.continuous.aestronglyMeasurable
    torus3Mk_measurePreserving_fundamentalCube

/-- Since the cutoff equals one on the cube, the torus `L⁶` seminorm is no larger than the
global Euclidean `L⁶` seminorm of the cutoff lift. -/
theorem eLpNorm_torus_six_le_cutoffLift
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : C(Torus3, F)) :
    eLpNorm f 6 volume ≤ eLpNorm (torusCutoffLift f) 6 volume := by
  calc
    eLpNorm f 6 volume =
        eLpNorm (torusLift f) 6
          (volume.restrict torus3FundamentalCube) :=
      (eLpNorm_torus_eq_restrict_fundamentalCube f 6).symm
    _ = eLpNorm (torusCutoffLift f) 6
          (volume.restrict torus3FundamentalCube) := by
      apply eLpNorm_congr_ae
      filter_upwards
        [ae_restrict_mem measurableSet_torus3FundamentalCube] with x hx
      exact (torusCutoffLift_eq_on_fundamentalCube f hx).symm
    _ ≤ eLpNorm (torusCutoffLift f) 6 volume :=
      eLpNorm_restrict_le _ _ _ _

/-- Euclidean `H¹ → L⁶` for the fixed cutoff extension.  This invokes Mathlib's proved
Gagliardo--Nirenberg--Sobolev theorem with the checked exponent identity
`1/6 = 1/2 - 1/3`. -/
theorem eLpNorm_torusCutoffLift_six_le_fderiv_two
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f)) :
    eLpNorm (torusCutoffLift f) 6 volume ≤
      SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 *
        eLpNorm (fderiv ℝ (torusCutoffLift f)) 2 volume := by
  apply eLpNorm_le_eLpNorm_fderiv_of_eq
    (volume : Measure Vec3)
    (contDiff_torusCutoffLift f hf)
    (hasCompactSupport_torusCutoffLift f)
    (p := (2 : ℝ≥0)) (p' := (6 : ℝ≥0))
  · norm_num
  · norm_num [finrank_euclideanSpace_fin]
  · norm_num [finrank_euclideanSpace_fin]

/-- Immediate periodic consequence of cutoff comparison and Euclidean Sobolev. -/
theorem eLpNorm_torus_six_le_cutoff_fderiv_two
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (f : C(Torus3, F)) (hf : ContDiff ℝ 1 (torusLift f)) :
    eLpNorm f 6 volume ≤
      SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 *
        eLpNorm (fderiv ℝ (torusCutoffLift f)) 2 volume :=
  (eLpNorm_torus_six_le_cutoffLift f).trans
    (eLpNorm_torusCutoffLift_six_le_fderiv_two f hf)

/-- The derivative of the one fixed cutoff has a finite global operator-norm bound. -/
theorem exists_torusSobolevCutoff_fderiv_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B := by
  have hcutoff : ContDiff ℝ 1 (torusSobolevCutoff : Vec3 → ℝ) :=
    torusSobolevCutoff.contDiff
  obtain ⟨C, hC⟩ :=
    (hcutoff.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      (torusSobolevCutoff.hasCompactSupport.fderiv ℝ)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Pointwise product-rule bound for the cutoff extension. -/
theorem norm_fderiv_torusCutoffLift_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f)) (x : Vec3) :
    ‖fderiv ℝ (torusCutoffLift f) x‖ ≤
      ‖fderiv ℝ (torusLift f) x‖ + B * ‖torusLift f x‖ := by
  have hcutoff : ContDiff ℝ 1 (torusSobolevCutoff : Vec3 → ℝ) :=
    torusSobolevCutoff.contDiff
  change ‖fderiv ℝ
    ((torusSobolevCutoff : Vec3 → ℝ) • torusLift f) x‖ ≤ _
  rw [fderiv_smul
    (hcutoff.differentiable one_ne_zero x)
    (hf.differentiable one_ne_zero x)]
  calc
    ‖torusSobolevCutoff x • fderiv ℝ (torusLift f) x +
        (fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x).smulRight
          (torusLift f x)‖ ≤
        ‖torusSobolevCutoff x • fderiv ℝ (torusLift f) x‖ +
          ‖(fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x).smulRight
            (torusLift f x)‖ := norm_add_le _ _
    _ = ‖torusSobolevCutoff x‖ * ‖fderiv ℝ (torusLift f) x‖ +
          ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ *
            ‖torusLift f x‖ := by
      rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ 1 * ‖fderiv ℝ (torusLift f) x‖ + B * ‖torusLift f x‖ := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [Real.norm_eq_abs,
          abs_of_nonneg (torusSobolevCutoff.nonneg' x)]
        exact torusSobolevCutoff.le_one
      · exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
    _ = _ := by rw [one_mul]

/-- A type-explicit wrapper around restriction by support, used below to keep elaboration of
operator-valued derivatives predictable. -/
theorem eLpNorm_eq_restrict_of_support_subset_vec3
    {E : Type*} [NormedAddCommGroup E]
    (g : Vec3 → E) (p : ℝ≥0∞) {s : Set Vec3} (hs : support g ⊆ s) :
    eLpNorm g p volume = eLpNorm g p (volume.restrict s) :=
  (eLpNorm_restrict_eq_of_support_subset (p := p) (μ := volume) hs).symm

/-- The derivative of the cutoff extension is supported in the cutoff's explicit outer ball. -/
theorem support_fderiv_torusCutoffLift_subset
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) :
    support (fderiv ℝ (torusCutoffLift f)) ⊆
      Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut := by
  refine (support_fderiv_subset ℝ).trans ?_
  refine (tsupport_smul_subset_left
    (torusSobolevCutoff : Vec3 → ℝ) (torusLift f)).trans ?_
  exact torusSobolevCutoff.tsupport_eq.le

/-- Restricting to the outer cutoff ball does not change the derivative seminorm. -/
theorem eLpNorm_fderiv_torusCutoffLift_eq_restrict
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus3 → F) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ (torusCutoffLift f)) p volume =
      eLpNorm (fderiv ℝ (torusCutoffLift f)) p
        (volume.restrict
          (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) := by
  exact eLpNorm_eq_restrict_of_support_subset_vec3
    (fderiv ℝ (torusCutoffLift f)) p (support_fderiv_torusCutoffLift_subset f)

/-- Pointwise product rule transferred to an `L²` comparison on the cutoff ball. -/
theorem eLpNorm_fderiv_torusCutoffLift_two_le_pointwiseSum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f)) :
    eLpNorm (fderiv ℝ (torusCutoffLift f)) 2
        (volume.restrict
          (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) ≤
      eLpNorm (fun x : Vec3 =>
        ‖fderiv ℝ (torusLift f) x‖ + B * ‖torusLift f x‖) 2
        (volume.restrict
          (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) := by
  apply eLpNorm_mono_real
  intro x
  exact norm_fderiv_torusCutoffLift_le B hB f hf x

/-- Minkowski's inequality separates the two terms in the pointwise product-rule bound. -/
theorem eLpNorm_pointwiseSum_two_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : ℝ) (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f)) :
    eLpNorm (fun x : Vec3 =>
        ‖fderiv ℝ (torusLift f) x‖ + B * ‖torusLift f x‖) 2
        (volume.restrict
          (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) ≤
      eLpNorm (fderiv ℝ (torusLift f)) 2
          (volume.restrict
            (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) +
        ‖B‖ₑ * eLpNorm (torusLift f) 2
          (volume.restrict
            (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) := by
  let K : Set Vec3 :=
    Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut
  have hderivMeas : AEStronglyMeasurable
      (fun x : Vec3 => ‖fderiv ℝ (torusLift f) x‖)
      (volume.restrict K) :=
    (hf.continuous_fderiv one_ne_zero).norm.aestronglyMeasurable
  have hliftMeas : AEStronglyMeasurable
      (fun x : Vec3 => B * ‖torusLift f x‖)
      (volume.restrict K) :=
    (hf.continuous.norm.const_mul B).aestronglyMeasurable
  have htriangle := eLpNorm_add_le hderivMeas hliftMeas
    (p := (2 : ℝ≥0∞)) (by norm_num)
  calc
    eLpNorm (fun x : Vec3 =>
        ‖fderiv ℝ (torusLift f) x‖ + B * ‖torusLift f x‖) 2
        (volume.restrict K) ≤
      eLpNorm (fun x : Vec3 => ‖fderiv ℝ (torusLift f) x‖) 2
          (volume.restrict K) +
        eLpNorm (fun x : Vec3 => B * ‖torusLift f x‖) 2
          (volume.restrict K) := htriangle
    _ = eLpNorm (fderiv ℝ (torusLift f)) 2 (volume.restrict K) +
        ‖B‖ₑ * eLpNorm (torusLift f) 2 (volume.restrict K) := by
      rw [eLpNorm_norm]
      change _ + eLpNorm (B • fun x : Vec3 => ‖torusLift f x‖) 2
          (volume.restrict K) = _
      rw [eLpNorm_const_smul, eLpNorm_norm]

/-- `L²` product-rule estimate, localized to the explicit outer ball of the cutoff. -/
theorem eLpNorm_fderiv_torusCutoffLift_two_le_restrict
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (f : Torus3 → F) (hf : ContDiff ℝ 1 (torusLift f)) :
    eLpNorm (fderiv ℝ (torusCutoffLift f)) 2 volume ≤
      eLpNorm (fderiv ℝ (torusLift f)) 2
          (volume.restrict
            (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) +
        ‖B‖ₑ *
          eLpNorm (torusLift f) 2
            (volume.restrict
              (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) := by
  rw [eLpNorm_fderiv_torusCutoffLift_eq_restrict f 2]
  exact (eLpNorm_fderiv_torusCutoffLift_two_le_pointwiseSum B hB f hf).trans
    (eLpNorm_pointwiseSum_two_le B f hf)

/-- The finite multiplicity factor incurred by covering the cutoff support with `125` period
cells at exponent `2`. -/
def torusSobolevL2Multiplicity : ℝ≥0∞ :=
  (125 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal

/-- All Euclidean terms in the cutoff product rule are now controlled by norms on the physical
torus. -/
theorem eLpNorm_fderiv_torusCutoffLift_two_le_torus
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (f : C(Torus3, F)) (hf : ContDiff ℝ 1 (torusLift f)) :
    eLpNorm (fderiv ℝ (torusCutoffLift f)) 2 volume ≤
      torusSobolevL2Multiplicity *
        (eLpNorm (torusFDerivIoc f) 2 volume +
          ‖B‖ₑ * eLpNorm f 2 volume) := by
  have hlocal := eLpNorm_fderiv_torusCutoffLift_two_le_restrict B hB f hf
  have hderiv := eLpNorm_fderiv_torusLift_restrict_cutoffBall_le f hf 2
  have hlift := eLpNorm_torusLift_restrict_cutoffBall_le f 2
  calc
    eLpNorm (fderiv ℝ (torusCutoffLift f)) 2 volume ≤
        eLpNorm (fderiv ℝ (torusLift f)) 2
            (volume.restrict
              (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) +
          ‖B‖ₑ * eLpNorm (torusLift f) 2
            (volume.restrict
              (Metric.closedBall torus3FundamentalCubeCenter torusSobolevCutoff.rOut)) :=
      hlocal
    _ ≤ torusSobolevL2Multiplicity * eLpNorm (torusFDerivIoc f) 2 volume +
          ‖B‖ₑ * (torusSobolevL2Multiplicity * eLpNorm f 2 volume) := by
      exact add_le_add hderiv (mul_le_mul_of_nonneg_left hlift bot_le)
    _ = torusSobolevL2Multiplicity *
          (eLpNorm (torusFDerivIoc f) 2 volume +
            ‖B‖ₑ * eLpNorm f 2 volume) := by
      rw [mul_add]
      ac_rfl

/-- A proved periodic `H¹ → L⁶` inequality for finite-dimensional fields on the concrete
three-torus.  The only constant parameter `B` is a global derivative bound for the one fixed
cutoff, whose existence was proved above. -/
theorem eLpNorm_torus_six_le_torus_h1
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (f : C(Torus3, F)) (hf : ContDiff ℝ 1 (torusLift f)) :
    eLpNorm f 6 volume ≤
      SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 *
        torusSobolevL2Multiplicity *
          (eLpNorm (torusFDerivIoc f) 2 volume +
            ‖B‖ₑ * eLpNorm f 2 volume) := by
  calc
    eLpNorm f 6 volume ≤
        SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 *
          eLpNorm (fderiv ℝ (torusCutoffLift f)) 2 volume :=
      eLpNorm_torus_six_le_cutoff_fderiv_two f hf
    _ ≤ SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 *
          (torusSobolevL2Multiplicity *
            (eLpNorm (torusFDerivIoc f) 2 volume +
              ‖B‖ₑ * eLpNorm f 2 volume)) :=
      mul_le_mul_of_nonneg_left
        (eLpNorm_fderiv_torusCutoffLift_two_le_torus B hB f hf) bot_le
    _ = _ := by rw [mul_assoc]

/-- Fully closed constant form: the fixed cutoff supplies a single finite `B` that works for
every smooth finite-dimensional torus field. -/
theorem exists_eLpNorm_torus_six_le_torus_h1_cutoffBound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀
      (F : Type*) (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
      (_ : FiniteDimensional ℝ F)
      (f : C(Torus3, F)),
      ContDiff ℝ 1 (torusLift f) →
      eLpNorm f 6 volume ≤
        SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 *
          torusSobolevL2Multiplicity *
            (eLpNorm (torusFDerivIoc f) 2 volume +
              ‖B‖ₑ * eLpNorm f 2 volume) := by
  obtain ⟨B, hB0, hB⟩ := exists_torusSobolevCutoff_fderiv_bound
  refine ⟨B, hB0, ?_⟩
  intro F _ _ _ f hf
  exact eLpNorm_torus_six_le_torus_h1 B hB f hf

/-- Continuous fields on the compact physical torus belong to every `Lᵖ`. -/
theorem ContinuousMap.memLp_torus_volume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : C(Torus3, F)) (p : ℝ≥0∞) : MemLp f p volume := by
  apply MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
  exact Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x

/-- Real-valued `Lᵖ`-norm form of periodic `H¹ → L⁶`.  The extra `MemLp` premise for the
descended derivative is precisely the finiteness condition needed to pass from `ENNReal` to
ordinary real norms. -/
theorem lpNorm_torus_six_le_torus_h1
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (f : C(Torus3, F)) (hf : ContDiff ℝ 1 (torusLift f))
    (hD : MemLp (torusFDerivIoc f) 2 volume) :
    lpNorm f 6 volume ≤
      (SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 : ℝ≥0∞).toReal *
        torusSobolevL2Multiplicity.toReal *
          (lpNorm (torusFDerivIoc f) 2 volume +
            ‖B‖ * lpNorm f 2 volume) := by
  have hF6 := ContinuousMap.memLp_torus_volume f 6
  have hF2 := ContinuousMap.memLp_torus_volume f 2
  have hS :
      (SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 : ℝ≥0∞) ≠ ∞ := by
    simp
  have hM : torusSobolevL2Multiplicity ≠ ∞ := by
    unfold torusSobolevL2Multiplicity
    finiteness
  have hBF : ‖B‖ₑ * eLpNorm f 2 volume ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hF2.eLpNorm_ne_top
  have hinner : eLpNorm (torusFDerivIoc f) 2 volume +
      ‖B‖ₑ * eLpNorm f 2 volume ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hD.eLpNorm_ne_top, hBF⟩
  have hrhs :
      (SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 : ℝ≥0∞) *
        torusSobolevL2Multiplicity *
          (eLpNorm (torusFDerivIoc f) 2 volume +
            ‖B‖ₑ * eLpNorm f 2 volume) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hS hM) hinner
  have hto := ENNReal.toReal_mono hrhs
    (eLpNorm_torus_six_le_torus_h1 B hB f hf)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add hD.eLpNorm_ne_top hBF,
    ENNReal.toReal_mul,
    toReal_eLpNorm hF6.aestronglyMeasurable,
    toReal_eLpNorm hD.aestronglyMeasurable,
    toReal_eLpNorm hF2.aestronglyMeasurable] at hto
  simpa using hto

/-- Ordinary sixth-moment form of the proved inhomogeneous periodic Sobolev inequality. -/
theorem integral_norm_pow_six_le_torus_h1
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (f : C(Torus3, F)) (hf : ContDiff ℝ 1 (torusLift f))
    (hD : MemLp (torusFDerivIoc f) 2 volume) :
    (∫ x : Torus3, ‖f x‖ ^ 6) ≤
      ((SNormLESNormFDerivOfEqConst F (volume : Measure Vec3) 2 : ℝ≥0∞).toReal *
        torusSobolevL2Multiplicity.toReal *
          (lpNorm (torusFDerivIoc f) 2 volume +
            ‖B‖ * lpNorm f 2 volume)) ^ 6 := by
  have hmoment : lpNorm f 6 volume ^ 6 = ∫ x : Torus3, ‖f x‖ ^ 6 := by
    simpa using lpNorm_natCast_pow_eq_integral_norm_pow
      f 6 (by norm_num) (volume : Measure Torus3)
        f.continuous.aestronglyMeasurable
  rw [← hmoment]
  exact pow_le_pow_left₀ lpNorm_nonneg
    (lpNorm_torus_six_le_torus_h1 B hB f hf hD) 6

/-! ## Homogeneous mean-zero vector Sobolev estimate -/

/-- Explicit real norm constant obtained after absorbing the lower-order cutoff term by vector
Poincare. -/
def torusVectorSobolevNormConstant (B : ℝ) : ℝ :=
  (SNormLESNormFDerivOfEqConst Vec3 (volume : Measure Vec3) 2 : ℝ≥0∞).toReal *
    torusSobolevL2Multiplicity.toReal *
      (1 + ‖B‖ * Real.sqrt (27 * ((2 : ℝ) * Real.pi) ^ 2))

/-- Sixth-moment constant in the existing Frobenius gradient-energy convention. -/
def torusVectorSobolevMomentConstant (B : ℝ) : ℝ :=
  27 * torusVectorSobolevNormConstant B ^ 6

theorem torusVectorSobolevNormConstant_nonneg (B : ℝ) :
    0 ≤ torusVectorSobolevNormConstant B := by
  unfold torusVectorSobolevNormConstant
  positivity

theorem torusVectorSobolevMomentConstant_nonneg (B : ℝ) :
    0 ≤ torusVectorSobolevMomentConstant B := by
  unfold torusVectorSobolevMomentConstant
  positivity

/-- Homogeneous real `L⁶` estimate for a mean-zero vector field. -/
theorem lpNorm_torus_vector_six_le_homogeneous_fderiv_two
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u : C(Torus3, Vec3))
    (hmean : ∀ j : Fin 3, (∫ x : Torus3, u x j) = 0)
    (hsmooth : ∀ (j i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hD : Integrable (fun x : Torus3 => ‖torusFDerivIoc u x‖ ^ 2)) :
    lpNorm u 6 volume ≤
      torusVectorSobolevNormConstant B *
        lpNorm (torusFDerivIoc u) 2 volume := by
  have hDmem : MemLp (torusFDerivIoc u) 2 volume :=
    (memLp_two_iff_integrable_sq_norm
      (aestronglyMeasurable_torusFDerivIoc u hu)).2 hD
  have hH1 := lpNorm_torus_six_le_torus_h1 B hB u hu hDmem
  have hP := lpNorm_torus_two_le_poincareFactor_mul_fderiv_two
    u hmean hsmooth hderiv hu hD
  have hlower :
      lpNorm (torusFDerivIoc u) 2 volume + ‖B‖ * lpNorm u 2 volume ≤
        (1 + ‖B‖ * Real.sqrt (27 * ((2 : ℝ) * Real.pi) ^ 2)) *
          lpNorm (torusFDerivIoc u) 2 volume := by
    calc
      lpNorm (torusFDerivIoc u) 2 volume + ‖B‖ * lpNorm u 2 volume ≤
          lpNorm (torusFDerivIoc u) 2 volume +
            ‖B‖ * (Real.sqrt (27 * ((2 : ℝ) * Real.pi) ^ 2) *
              lpNorm (torusFDerivIoc u) 2 volume) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hP (norm_nonneg B))
      _ = (1 + ‖B‖ * Real.sqrt (27 * ((2 : ℝ) * Real.pi) ^ 2)) *
            lpNorm (torusFDerivIoc u) 2 volume := by ring
  calc
    lpNorm u 6 volume ≤
        (SNormLESNormFDerivOfEqConst Vec3 (volume : Measure Vec3) 2 : ℝ≥0∞).toReal *
          torusSobolevL2Multiplicity.toReal *
            (lpNorm (torusFDerivIoc u) 2 volume +
              ‖B‖ * lpNorm u 2 volume) := hH1
    _ ≤ (SNormLESNormFDerivOfEqConst Vec3 (volume : Measure Vec3) 2 : ℝ≥0∞).toReal *
          torusSobolevL2Multiplicity.toReal *
            ((1 + ‖B‖ * Real.sqrt (27 * ((2 : ℝ) * Real.pi) ^ 2)) *
              lpNorm (torusFDerivIoc u) 2 volume) := by
      exact mul_le_mul_of_nonneg_left hlower (by positivity)
    _ = torusVectorSobolevNormConstant B *
          lpNorm (torusFDerivIoc u) 2 volume := by
      unfold torusVectorSobolevNormConstant
      ring

/-- The first of the two homogeneous sixth-moment estimates required by
`SpatialInterpolation.lean`, in its existing `torusGradientEnergy` convention. -/
theorem integral_torus_vector_norm_pow_six_le_gradientEnergy_cubic
    (B : ℝ)
    (hB : ∀ x : Vec3,
      ‖fderiv ℝ (torusSobolevCutoff : Vec3 → ℝ) x‖ ≤ B)
    (u : C(Torus3, Vec3))
    (hmean : ∀ j : Fin 3, (∫ x : Torus3, u x j) = 0)
    (hsmooth : ∀ (j i : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hderiv : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      periodicFirstDerivative u i j x ^ 2))
    (hu : ContDiff ℝ 1 (torusLift u)) :
    (∫ x : Torus3, ‖u x‖ ^ 6) ≤
      torusVectorSobolevMomentConstant B * torusGradientEnergy u ^ 3 := by
  have hD : Integrable (fun x : Torus3 => ‖torusFDerivIoc u x‖ ^ 2) :=
    integrable_norm_torusFDerivIoc_sq_of_periodicFirstDerivative u hu hderiv
  have hgrad : Integrable (fun x : Torus3 => periodicGradientFrobeniusSq u x) := by
    unfold periodicGradientFrobeniusSq
    exact MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun j _ => hderiv i j
  have hmoment : lpNorm u 6 volume ^ 6 = ∫ x : Torus3, ‖u x‖ ^ 6 := by
    simpa using lpNorm_natCast_pow_eq_integral_norm_pow
      u 6 (by norm_num) (volume : Measure Torus3)
        u.continuous.aestronglyMeasurable
  have hDSq : lpNorm (torusFDerivIoc u) 2 volume ^ 2 =
      ∫ x : Torus3, ‖torusFDerivIoc u x‖ ^ 2 := by
    simpa using lpNorm_natCast_pow_eq_integral_norm_pow
      (torusFDerivIoc u) 2 (by norm_num) (volume : Measure Torus3)
        (aestronglyMeasurable_torusFDerivIoc u hu)
  have hDG : lpNorm (torusFDerivIoc u) 2 volume ^ 2 ≤
      3 * torusGradientEnergy u := by
    rw [hDSq]
    exact integral_norm_torusFDerivIoc_sq_le_three_mul_gradientEnergy
      u hu hD hgrad
  have hD6 : lpNorm (torusFDerivIoc u) 2 volume ^ 6 ≤
      27 * torusGradientEnergy u ^ 3 := by
    calc
      lpNorm (torusFDerivIoc u) 2 volume ^ 6 =
          (lpNorm (torusFDerivIoc u) 2 volume ^ 2) ^ 3 := by ring
      _ ≤ (3 * torusGradientEnergy u) ^ 3 :=
        pow_le_pow_left₀ (sq_nonneg _) hDG 3
      _ = 27 * torusGradientEnergy u ^ 3 := by ring
  calc
    (∫ x : Torus3, ‖u x‖ ^ 6) = lpNorm u 6 volume ^ 6 := hmoment.symm
    _ ≤ (torusVectorSobolevNormConstant B *
          lpNorm (torusFDerivIoc u) 2 volume) ^ 6 :=
      pow_le_pow_left₀ lpNorm_nonneg
        (lpNorm_torus_vector_six_le_homogeneous_fderiv_two
          B hB u hmean hsmooth hderiv hu hD) 6
    _ = torusVectorSobolevNormConstant B ^ 6 *
          lpNorm (torusFDerivIoc u) 2 volume ^ 6 := by ring
    _ ≤ torusVectorSobolevNormConstant B ^ 6 *
          (27 * torusGradientEnergy u ^ 3) :=
      mul_le_mul_of_nonneg_left hD6 (pow_nonneg (torusVectorSobolevNormConstant_nonneg B) 6)
    _ = torusVectorSobolevMomentConstant B * torusGradientEnergy u ^ 3 := by
      unfold torusVectorSobolevMomentConstant
      ring
