import Mathlib

/-!
# Finite orbit averages as approximate first integrals

For a continuous real flow `flow` and a scalar seed `seed`, average the seed
over an orbit segment of length `L`.  Differentiating the average along the
same flow produces only the two endpoints, divided by `L`.  This is the basic
construction behind approximate vortex-line first integrals; the remaining
Navier--Stokes question is whether an averaged helicity seed retains enough
correlation while its endpoint leakage becomes small.
-/

open MeasureTheory
open scoped Interval
open scoped Topology

noncomputable section

/-- The normalized forward average of a scalar observable along a flow. -/
def orbitAverage {α : Type*} [TopologicalSpace α]
    (flow : Flow ℝ α) (L : ℝ) (seed : α → ℝ) (x : α) : ℝ :=
  L⁻¹ * ∫ s in (0 : ℝ)..L, seed (flow s x)

/-- Moving the base point along the flow translates the integration window. -/
theorem orbitAverage_along_flow_eq_shifted_interval
    {α : Type*} [TopologicalSpace α]
    (flow : Flow ℝ α) (L τ : ℝ) (seed : α → ℝ) (x : α) :
    orbitAverage flow L seed (flow τ x) =
      L⁻¹ * ∫ s in τ..L + τ, seed (flow s x) := by
  rw [orbitAverage]
  have htranslate :
      (∫ s in (0 : ℝ)..L, seed (flow s (flow τ x))) =
        ∫ s in (0 : ℝ)..L, seed (flow (s + τ) x) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    change seed (flow s (flow τ x)) = seed (flow (s + τ) x)
    rw [flow.map_add]
  rw [htranslate]
  congr 1
  simpa only [zero_add] using
    (intervalIntegral.integral_comp_add_right
      (fun s : ℝ => seed (flow s x)) τ (a := 0) (b := L))

/-- The flow derivative of a finite orbit average is its endpoint difference
divided by the averaging length. -/
theorem orbitAverage_hasDerivAt_along_flow
    {α : Type*} [TopologicalSpace α]
    (flow : Flow ℝ α) (L τ : ℝ) (seed : α → ℝ) (x : α)
    (hseed : Continuous seed) :
    HasDerivAt (fun σ => orbitAverage flow L seed (flow σ x))
      (L⁻¹ * (seed (flow (L + τ) x) - seed (flow τ x))) τ := by
  let observable : ℝ → ℝ := fun s => seed (flow s x)
  have hobservable : Continuous observable := by
    exact hseed.comp (flow.continuous continuous_id continuous_const)
  let primitive : ℝ → ℝ := fun b => ∫ s in (0 : ℝ)..b, observable s
  have hprimitive : ∀ b : ℝ, HasDerivAt primitive (observable b) b := by
    intro b
    exact (hobservable.integral_hasStrictDerivAt 0 b).hasDerivAt
  have hupper : HasDerivAt (fun σ => primitive (L + σ))
      (observable (L + τ)) τ :=
    (hprimitive (L + τ)).comp_const_add L τ
  have hlower : HasDerivAt primitive (observable τ) τ := hprimitive τ
  have hfunction :
      (fun σ => orbitAverage flow L seed (flow σ x)) =
        fun σ => L⁻¹ * (primitive (L + σ) - primitive σ) := by
    funext σ
    rw [orbitAverage_along_flow_eq_shifted_interval]
    dsimp [primitive]
    rw [intervalIntegral.integral_interval_sub_left
      (hobservable.intervalIntegrable 0 (L + σ))
      (hobservable.intervalIntegrable 0 σ)]
  rw [hfunction]
  simpa [observable] using (hupper.sub hlower).const_mul L⁻¹

/-- A bounded seed gives an explicit `O(L⁻¹)` pointwise leakage bound for its
orbit average. -/
theorem orbitAverage_endpointLeakage_le
    {α : Type*} [TopologicalSpace α]
    (flow : Flow ℝ α) (L K τ : ℝ) (seed : α → ℝ) (x : α)
    (hL : 0 < L) (hseedBound : ∀ y, |seed y| ≤ K) :
    |L⁻¹ * (seed (flow (L + τ) x) - seed (flow τ x))| ≤
      2 * K / L := by
  rw [abs_mul, abs_inv, abs_of_pos hL]
  rw [inv_mul_eq_div]
  apply (div_le_div_iff_of_pos_right hL).2
  calc
    |seed (flow (L + τ) x) - seed (flow τ x)| ≤
        |seed (flow (L + τ) x)| + |seed (flow τ x)| := abs_sub _ _
    _ ≤ K + K := add_le_add (hseedBound _) (hseedBound _)
    _ = 2 * K := by ring

/-- If a continuous flow is differentiable at the base point with velocity
`velocity`, and the constructed orbit average is Fréchet differentiable there,
then its directional derivative in that velocity is exactly the endpoint
leakage.  For a smooth vorticity flow this is the bridge to
`(ω · ∇) φ_L`. -/
theorem orbitAverage_fderiv_apply_flowVelocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (flow : Flow ℝ E) (L : ℝ) (seed : E → ℝ) (x velocity : E)
    (D : E →L[ℝ] ℝ) (hseed : Continuous seed)
    (haverage : HasFDerivAt (orbitAverage flow L seed) D x)
    (hcurve : HasDerivAt (fun τ => flow τ x) velocity 0) :
    D velocity = L⁻¹ * (seed (flow L x) - seed x) := by
  have hzero : x = flow 0 x := (congrFun flow.map_zero x).symm
  have hchain := haverage.comp_hasDerivAt_of_eq 0 hcurve hzero
  change HasDerivAt (fun τ => orbitAverage flow L seed (flow τ x))
    (D velocity) 0 at hchain
  have hboundary := orbitAverage_hasDerivAt_along_flow
    flow L 0 seed x hseed
  simpa using hchain.unique hboundary

/-- For a nonnegative retained orbit-average amplitude `r`, a quadratic
helicity signal beats a linear endpoint penalty exactly when the retained
amplitude beats the normalized leakage scale. -/
theorem orbitAverage_quadraticSignal_sub_linearLeakage_pos
    {r leakageScale : ℝ} (hr : 0 < r)
    (hleakage : leakageScale < r) :
    0 < r ^ 2 - r * leakageScale := by
  nlinarith

/-- The identity flow is an elementary exact-first-integral instance of the
construction: every orbit average recovers its seed when `L ≠ 0`. -/
theorem orbitAverage_identityFlow
    {α : Type*} [TopologicalSpace α]
    (L : ℝ) (seed : α → ℝ) (x : α) (hL : L ≠ 0) :
    orbitAverage (Flow.id ℝ α) L seed x = seed x := by
  rw [orbitAverage]
  simp [hL]

/-! ## Discrete spectral diagnostic -/

/-- Discrete orbit averages of a contracting transport converge in squared
norm to the squared norm of the fixed-point projection.  For vortex-line
transport this projection is the exactly invariant part of the seed. -/
theorem birkhoffAverage_norm_sq_tendsto_fixedProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (transport : E →L[ℝ] E) (hcontract : ‖transport‖ ≤ 1) (seed : E) :
    Filter.Tendsto
      (fun n => ‖birkhoffAverage ℝ transport id n seed‖ ^ 2)
      Filter.atTop
      (𝓝 (‖(transport.eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto
        seed‖ ^ 2)) := by
  exact (transport.tendsto_birkhoffAverage_orthogonalProjection
    hcontract seed).norm.pow 2

/-- Before taking the mean-ergodic limit, an `n`-step average is already
approximately invariant: its one-step transport defect is at most
`2 ‖seed‖ / n`. -/
theorem birkhoffAverage_transportLeakage_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (transport : E →L[ℝ] E) (hcontract : ‖transport‖ ≤ 1)
    (n : ℕ) (hn : 0 < n) (seed : E) :
    ‖birkhoffAverage ℝ transport id n (transport seed) -
        birkhoffAverage ℝ transport id n seed‖ ≤
      2 * ‖seed‖ / (n : ℝ) := by
  rw [birkhoffAverage_apply_sub_birkhoffAverage]
  have hiterateAll : ∀ m : ℕ, ‖transport^[m] seed‖ ≤ ‖seed‖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        have hstep : ‖transport (transport^[m] seed)‖ ≤
            ‖transport^[m] seed‖ := by
          simpa using transport.le_of_opNorm_le hcontract
            (transport^[m] seed)
        exact hstep.trans ih
  have hiterate := hiterateAll n
  have hdifference : ‖transport^[n] seed - seed‖ ≤ 2 * ‖seed‖ := by
    calc
      ‖transport^[n] seed - seed‖ ≤
          ‖transport^[n] seed‖ + ‖seed‖ := norm_sub_le _ _
      _ ≤ ‖seed‖ + ‖seed‖ := add_le_add hiterate le_rfl
      _ = 2 * ‖seed‖ := by ring
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnreal]
  calc
    (n : ℝ)⁻¹ * ‖transport^[n] seed - seed‖ ≤
        (n : ℝ)⁻¹ * (2 * ‖seed‖) :=
      mul_le_mul_of_nonneg_left hdifference (inv_nonneg.mpr hnreal.le)
    _ = 2 * ‖seed‖ / (n : ℝ) := by
      rw [div_eq_mul_inv]
      ring

/-- Orbit averaging does not automatically preserve a signal: the nonzero
seed `1` is annihilated by the two-step average of the isometric sign-flip
transport. -/
theorem birkhoffAverage_signFlip_two_annihilates :
    birkhoffAverage ℝ (fun x : ℝ => -x) id 2 1 = 0 := by
  norm_num [birkhoffAverage, birkhoffSum, Finset.sum_range_succ,
    Function.iterate_succ_apply]

/-! ## Positive adjoint-averaged weights -/

/-- Apply the adjoint average to the forward-averaged seed.  In a spatial
`L²` realization this is the Fejér-type weight `A_L* A_L h`. -/
def adjointAveragedWeight
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (average : E →L[ℝ] E) (seed : E) : E :=
  average.adjoint (average seed)

/-- The adjoint-averaged weight has an automatically nonnegative signal,
exactly the squared norm retained by the forward average. -/
theorem adjointAveragedWeight_inner_seed_eq_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (average : E →L[ℝ] E) (seed : E) :
    inner ℝ (adjointAveragedWeight average seed) seed =
      ‖average seed‖ ^ 2 := by
  rw [adjointAveragedWeight, average.adjoint_inner_left,
    real_inner_self_eq_norm_sq]

/-- If the averaging operator is a contraction, the squared mass of its
adjoint-averaged weight is no larger than the retained forward-average mass. -/
theorem adjointAveragedWeight_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (average : E →L[ℝ] E) (seed : E)
    (haverage : ‖average‖ ≤ 1) :
    ‖adjointAveragedWeight average seed‖ ≤ ‖average seed‖ := by
  have hadjoint : ‖average.adjoint‖ ≤ 1 := by
    simpa using haverage
  exact average.adjoint.le_of_opNorm_le hadjoint (average seed) |>.trans_eq
    (one_mul _)

/-- A forward average which retains any nonzero component therefore produces
a strictly positive adjoint-averaged signal. -/
theorem adjointAveragedWeight_inner_seed_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (average : E →L[ℝ] E) (seed : E)
    (hretained : average seed ≠ 0) :
    0 < inner ℝ (adjointAveragedWeight average seed) seed := by
  rw [adjointAveragedWeight_inner_seed_eq_norm_sq]
  positivity

/-! ## Strongly continuous operator averages -/

/-- The normalized Bochner average of a family of bounded operators. -/
def operatorIntervalAverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (operators : ℝ → E →L[ℝ] E) (L : ℝ) : E →L[ℝ] E :=
  L⁻¹ • ∫ s in (0 : ℝ)..L, operators s

/-- A strongly continuous operator average acts by averaging the orbit of
each vector. -/
theorem operatorIntervalAverage_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (operators : ℝ → E →L[ℝ] E) (L : ℝ) (seed : E)
    (hoperators : Continuous operators) :
    operatorIntervalAverage operators L seed =
      L⁻¹ • ∫ s in (0 : ℝ)..L, operators s seed := by
  rw [operatorIntervalAverage]
  change L⁻¹ • ((∫ s in (0 : ℝ)..L, operators s) seed) = _
  rw [ContinuousLinearMap.intervalIntegral_apply
    (hoperators.intervalIntegrable 0 L) seed]

/-- The average of contraction operators over a positive interval is again a
contraction. -/
theorem operatorIntervalAverage_norm_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (operators : ℝ → E →L[ℝ] E) (L : ℝ) (hL : 0 < L)
    (hcontract : ∀ s, ‖operators s‖ ≤ 1) :
    ‖operatorIntervalAverage operators L‖ ≤ 1 := by
  rw [operatorIntervalAverage, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hL]
  have hintegral : ‖∫ s in (0 : ℝ)..L, operators s‖ ≤ L := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := L) (C := (1 : ℝ))
      (f := operators) (fun s _hs => hcontract s)
    simpa [abs_of_pos hL] using hbound
  calc
    L⁻¹ * ‖∫ s in (0 : ℝ)..L, operators s‖ ≤ L⁻¹ * L :=
      mul_le_mul_of_nonneg_left hintegral (inv_nonneg.mpr hL.le)
    _ = 1 := inv_mul_cancel₀ hL.ne'

/-- Composition by a measure-preserving map as a concrete isometric Koopman
operator on scalar `L²`. -/
def measurePreservingKoopman
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (map : α → α) (hmap : MeasurePreserving map μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ map hmap).toContinuousLinearMap

/-- Every measure-preserving Koopman operator has norm at most one. -/
theorem measurePreservingKoopman_norm_le_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (map : α → α) (hmap : MeasurePreserving map μ μ) :
    ‖measurePreservingKoopman μ map hmap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro seed
  change ‖Lp.compMeasurePreserving map hmap seed‖ ≤ 1 * ‖seed‖
  simp
