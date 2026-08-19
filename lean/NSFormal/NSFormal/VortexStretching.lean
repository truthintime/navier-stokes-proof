import NSFormal.DirectorTensor

/-!
# Periodic vortex-stretching cancellation

This file records the global integration-by-parts identity which makes constant-direction
vorticity effectively two-dimensional.  The normalized direction formula is stated with
explicit smoothness, integrability, and divergence hypotheses; no vorticity direction is
postulated at a zero.
-/

open Filter Function MeasureTheory Set

noncomputable section

/-- The expansion vector is parallel to the direction, while line curvature is tangent to
the sphere.  Their squared norms therefore add with no triangle-inequality loss. -/
theorem norm_directionExpansion_sub_curvature_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (divergence : ℝ) (direction curvature : E)
    (hunit : ‖direction‖ = 1) (horth : inner ℝ direction curvature = 0) :
    ‖divergence • direction - curvature‖ ^ 2 =
      divergence ^ 2 + ‖curvature‖ ^ 2 := by
  have horth' : inner ℝ curvature direction = 0 := by
    rw [real_inner_comm]
    exact horth
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [horth, horth', norm_smul, Real.norm_eq_abs, hunit]
  simp only [mul_one, sq_abs]
  ring

/-- With the elementary bounds `|div ξ|² ≤ 3 |∇ξ|²` and
`|(ξ·∇)ξ|² ≤ |∇ξ|²`, the exact orthogonal split has constant `4`. -/
theorem norm_directionExpansion_sub_curvature_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (divergence gradientSq : ℝ) (direction curvature : E)
    (hunit : ‖direction‖ = 1) (horth : inner ℝ direction curvature = 0)
    (hdiv : divergence ^ 2 ≤ 3 * gradientSq)
    (hcurvature : ‖curvature‖ ^ 2 ≤ gradientSq) :
    ‖divergence • direction - curvature‖ ^ 2 ≤ 4 * gradientSq := by
  rw [norm_directionExpansion_sub_curvature_sq divergence direction curvature hunit horth]
  linarith

/-- Orthogonal projection of a vorticity derivative away from the radial direction. -/
def vorticityDirectionProjection (w h : Vec3) : Vec3 :=
  h - (((∑ q : Fin 3, w q * h q) / (∑ q : Fin 3, w q ^ 2)) • w)

theorem vorticityDirectionProjection_add (w h k : Vec3) :
    vorticityDirectionProjection w (h + k) =
      vorticityDirectionProjection w h + vorticityDirectionProjection w k := by
  have hsum : (∑ q : Fin 3, w q * (h q + k q)) =
      (∑ q : Fin 3, w q * h q) + ∑ q : Fin 3, w q * k q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  ext i
  simp only [vorticityDirectionProjection, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply]
  rw [hsum]
  ring

theorem vorticityDirectionProjection_smul
    (w h : Vec3) (c : ℝ) :
    vorticityDirectionProjection w (c • h) =
      c • vorticityDirectionProjection w h := by
  have hsum : (∑ q : Fin 3, w q * (c * h q)) =
      c * ∑ q : Fin 3, w q * h q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  ext i
  simp only [vorticityDirectionProjection, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  rw [hsum]
  ring

@[simp]
theorem vorticityDirectionProjection_zero (w : Vec3) :
    vorticityDirectionProjection w 0 = 0 := by
  simp [vorticityDirectionProjection]

/-- The component along vorticity of the cleared rigidity equation is the
scalar amplitude-transport balance. -/
theorem cleared_vorticity_rigidity_parallel_balance
    (w velocity selfTransport : Vec3) (c : ℝ)
    (h : ‖w‖ ^ 2 • velocity + c • selfTransport = 0) :
    ‖w‖ ^ 2 * inner ℝ w velocity +
      c * inner ℝ w selfTransport = 0 := by
  have hi := congrArg (fun z : Vec3 => inner ℝ w z) h
  simpa only [inner_add_right, real_inner_smul_right, inner_zero_right] using hi

/-- The component perpendicular to vorticity of the cleared rigidity equation
is the vortex-line direction/bending balance. -/
theorem cleared_vorticity_rigidity_projected_balance
    (w velocity selfTransport : Vec3) (c : ℝ)
    (h : ‖w‖ ^ 2 • velocity + c • selfTransport = 0) :
    ‖w‖ ^ 2 • vorticityDirectionProjection w velocity +
      c • vorticityDirectionProjection w selfTransport = 0 := by
  have hp := congrArg (vorticityDirectionProjection w) h
  simpa only [vorticityDirectionProjection_add,
    vorticityDirectionProjection_smul,
    vorticityDirectionProjection_zero] using hp

/-- Projected spatial self-transport jet. -/
def projectedVorticitySelfTransportJet
    (w : Vec3) (H : Fin 3 → Vec3) : Vec3 :=
  WithLp.toLp 2 fun i =>
    ∑ j : Fin 3, w j * vorticityDirectionProjection w (H j) i

/-- Unprojected self-transport jet `(w·∇)w`. -/
def vorticitySelfTransportJet (w : Vec3) (H : Fin 3 → Vec3) : Vec3 :=
  WithLp.toLp 2 fun i => ∑ j : Fin 3, w j * H j i

/-- Trace of the direction-projected derivative matrix. -/
def vorticityDirectionProjectionTrace
    (w : Vec3) (H : Fin 3 → Vec3) : ℝ :=
  ∑ j : Fin 3, vorticityDirectionProjection w (H j) j

/-- Direction-only part of a full vorticity derivative jet. -/
def vorticityDirectionDissipationJet
    (w : Vec3) (H : Fin 3 → Vec3) : ℝ :=
  ∑ j : Fin 3, regularizedDirectorDirectionDerivativeSq w (H j)

/-- The sharp direction charge after retaining the projected self-transport correction. -/
def effectiveVorticityDirectionDissipationJet
    (w : Vec3) (H : Fin 3 → Vec3) : ℝ :=
  2 * vorticityDirectionDissipationJet w H -
    ‖projectedVorticitySelfTransportJet w H‖ ^ 2 /
      (∑ q : Fin 3, w q ^ 2)

/-- Exact zero-safe self-transport charge `|(w·∇)w|² / |w|²`. -/
def vorticitySelfTransportQuotientJet
    (w : Vec3) (H : Fin 3 → Vec3) : ℝ :=
  ‖vorticitySelfTransportJet w H‖ ^ 2 / (∑ q : Fin 3, w q ^ 2)

theorem vorticitySelfTransportQuotientJet_nonneg
    (w : Vec3) (H : Fin 3 → Vec3) :
    0 ≤ vorticitySelfTransportQuotientJet w H := by
  exact div_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem vorticitySelfTransportJet_norm_sq_eq_weight_mul_quotient
    (w : Vec3) (H : Fin 3 → Vec3) :
    ‖vorticitySelfTransportJet w H‖ ^ 2 =
      (∑ q : Fin 3, w q ^ 2) * vorticitySelfTransportQuotientJet w H := by
  by_cases hr : (∑ q : Fin 3, w q ^ 2) = 0
  · have hw := vec3_eq_zero_of_sq_sum_eq_zero w hr
    subst w
    have hz : vorticitySelfTransportJet (0 : Vec3) H = 0 := by
      ext i
      simp [vorticitySelfTransportJet]
    rw [hz]
    simp [vorticitySelfTransportQuotientJet]
  · unfold vorticitySelfTransportQuotientJet
    field_simp [hr]

theorem inner_vorticity_directionProjection_eq_zero
    (w h : Vec3) (hr : (∑ q : Fin 3, w q ^ 2) ≠ 0) :
    inner ℝ w (vorticityDirectionProjection w h) = 0 := by
  unfold vorticityDirectionProjection
  rw [inner_sub_right, real_inner_smul_right]
  have hdot : inner ℝ w h = ∑ q : Fin 3, w q * h q := by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  have hnorm : ‖w‖ ^ 2 = ∑ q : Fin 3, w q ^ 2 :=
    EuclideanSpace.real_norm_sq_eq w
  rw [hdot, real_inner_self_eq_norm_sq, hnorm]
  field_simp [hr]
  ring

/-- The quotient definition of direction dissipation is exactly the squared norm of the
orthogonal derivative projection. -/
theorem vorticityDirectionProjection_norm_sq
    (w h : Vec3) (hr : (∑ q : Fin 3, w q ^ 2) ≠ 0) :
    ‖vorticityDirectionProjection w h‖ ^ 2 =
      regularizedDirectorDirectionDerivativeSq w h := by
  let r : ℝ := ∑ q : Fin 3, w q ^ 2
  let d : ℝ := ∑ q : Fin 3, w q * h q
  let a : ℝ := d / r
  have hwh : inner ℝ w h = d := by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
    rfl
  have hhw : inner ℝ h w = d := by
    rw [real_inner_comm]
    exact hwh
  have hww : inner ℝ w w = r := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  have hhh : inner ℝ h h = ∑ q : Fin 3, h q ^ 2 := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  rw [← real_inner_self_eq_norm_sq]
  unfold vorticityDirectionProjection
  change inner ℝ (h - a • w) (h - a • w) = _
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [hwh, hhw, hww, hhh]
  unfold regularizedDirectorDirectionDerivativeSq
  dsimp [a, d, r]
  field_simp [hr]
  ring

/-- Coordinate matrix of the orthogonal projector onto the plane normal to `w`. -/
def vorticityTangentProjectorCoefficient
    (w : Vec3) (j i : Fin 3) : ℝ :=
  (if j = i then 1 else 0) -
    w j * w i / (∑ q : Fin 3, w q ^ 2)

theorem vorticityTangentProjectorCoefficient_sq_sum
    (w : Vec3) (hr : (∑ q : Fin 3, w q ^ 2) ≠ 0) :
    (∑ j : Fin 3, ∑ i : Fin 3,
      vorticityTangentProjectorCoefficient w j i ^ 2) = 2 := by
  unfold vorticityTangentProjectorCoefficient
  simp only [Fin.sum_univ_three]
  simp
  have hr' : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 ≠ 0 := by
    simpa only [Fin.sum_univ_three] using hr
  field_simp [hr']
  ring

/-- A matrix whose rows are all normal to `w` has trace bounded by its two-dimensional
tangential Frobenius norm. -/
theorem trace_sq_le_two_frobenius_of_rows_orthogonal
    (w : Vec3) (B : Fin 3 → Vec3)
    (hr : (∑ q : Fin 3, w q ^ 2) ≠ 0)
    (horth : ∀ j : Fin 3, inner ℝ w (B j) = 0) :
    (∑ j : Fin 3, B j j) ^ 2 ≤
      2 * ∑ j : Fin 3, ‖B j‖ ^ 2 := by
  let r : ℝ := ∑ q : Fin 3, w q ^ 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun ji => vorticityTangentProjectorCoefficient w ji.1 ji.2)
    (fun ji => B ji.1 ji.2)
  have hcoeff :
      (∑ ji : Fin 3 × Fin 3,
        vorticityTangentProjectorCoefficient w ji.1 ji.2 ^ 2) = 2 := by
    rw [Fintype.sum_prod_type]
    exact vorticityTangentProjectorCoefficient_sq_sum w hr
  have hdata : (∑ ji : Fin 3 × Fin 3, B ji.1 ji.2 ^ 2) =
      ∑ j : Fin 3, ‖B j‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [EuclideanSpace.real_norm_sq_eq]
  have hdot :
      (∑ ji : Fin 3 × Fin 3,
        vorticityTangentProjectorCoefficient w ji.1 ji.2 * B ji.1 ji.2) =
        ∑ j : Fin 3, B j j := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _hj
    have hrow : (∑ i : Fin 3, w i * B j i) = 0 := by
      have hj := horth j
      rw [PiLp.inner_apply] at hj
      simpa only [Real.inner_apply] using hj
    unfold vorticityTangentProjectorCoefficient
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    have hdiag : (∑ i : Fin 3, (if j = i then 1 else 0) * B j i) = B j j := by
      simp
    rw [hdiag]
    rw [show (∑ i : Fin 3, w j * w i / r * B j i) =
        (w j / r) * ∑ i : Fin 3, w i * B j i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring]
    rw [hrow]
    ring
  rw [hdot, hcoeff, hdata] at hcs
  exact hcs

theorem inner_projectedVorticitySelfTransportJet_vorticity_eq_zero
    (w : Vec3) (H : Fin 3 → Vec3) (hr : (∑ q : Fin 3, w q ^ 2) ≠ 0) :
    inner ℝ (projectedVorticitySelfTransportJet w H) w = 0 := by
  rw [real_inner_comm, PiLp.inner_apply]
  unfold projectedVorticitySelfTransportJet
  simp only [Real.inner_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin 3, ∑ i : Fin 3,
        w i * (w j * vorticityDirectionProjection w (H j) i)) =
        ∑ j : Fin 3, w j *
          inner ℝ w (vorticityDirectionProjection w (H j)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [PiLp.inner_apply, Finset.mul_sum]
      simp only [Real.inner_apply]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = 0 := by
      simp [inner_vorticity_directionProjection_eq_zero w _ hr]

theorem projectedVorticitySelfTransportJet_norm_sq_le
    (w : Vec3) (H : Fin 3 → Vec3) (hr : (∑ q : Fin 3, w q ^ 2) ≠ 0) :
    ‖projectedVorticitySelfTransportJet w H‖ ^ 2 ≤
      (∑ q : Fin 3, w q ^ 2) * vorticityDirectionDissipationJet w H := by
  let r : ℝ := ∑ q : Fin 3, w q ^ 2
  have hcomponent : ∀ i : Fin 3,
      (∑ j : Fin 3, w j * vorticityDirectionProjection w (H j) i) ^ 2 ≤
        r * ∑ j : Fin 3, vorticityDirectionProjection w (H j) i ^ 2 := by
    intro i
    have hcs := vec3_dot_sq_le_sq_sum_mul_sq_sum w
      (WithLp.toLp 2 fun j => vorticityDirectionProjection w (H j) i)
    simpa [r] using hcs
  calc
    ‖projectedVorticitySelfTransportJet w H‖ ^ 2 =
        ∑ i : Fin 3,
          (∑ j : Fin 3, w j * vorticityDirectionProjection w (H j) i) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    _ ≤ ∑ i : Fin 3,
        r * ∑ j : Fin 3, vorticityDirectionProjection w (H j) i ^ 2 :=
      Finset.sum_le_sum fun i _hi => hcomponent i
    _ = r * ∑ j : Fin 3, ‖vorticityDirectionProjection w (H j)‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      rw [EuclideanSpace.real_norm_sq_eq]
    _ = (∑ q : Fin 3, w q ^ 2) * vorticityDirectionDissipationJet w H := by
      dsimp [r, vorticityDirectionDissipationJet]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      exact vorticityDirectionProjection_norm_sq w (H j) hr

/-- Directional differentiation by `w` is bounded by the full derivative Frobenius norm. -/
theorem vorticitySelfTransportJet_norm_sq_le_fullDissipation
    (w : Vec3) (H : Fin 3 → Vec3) :
    ‖vorticitySelfTransportJet w H‖ ^ 2 ≤
      (∑ q : Fin 3, w q ^ 2) * ∑ j : Fin 3, ‖H j‖ ^ 2 := by
  have hcomponent : ∀ i : Fin 3,
      (∑ j : Fin 3, w j * H j i) ^ 2 ≤
        (∑ q : Fin 3, w q ^ 2) * ∑ j : Fin 3, H j i ^ 2 := by
    intro i
    exact vec3_dot_sq_le_sq_sum_mul_sq_sum w
      (WithLp.toLp 2 fun j => H j i)
  calc
    ‖vorticitySelfTransportJet w H‖ ^ 2 =
        ∑ i : Fin 3, (∑ j : Fin 3, w j * H j i) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    _ ≤ ∑ i : Fin 3,
        (∑ q : Fin 3, w q ^ 2) * ∑ j : Fin 3, H j i ^ 2 :=
      Finset.sum_le_sum fun i _hi => hcomponent i
    _ = (∑ q : Fin 3, w q ^ 2) * ∑ j : Fin 3, ‖H j‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      rw [EuclideanSpace.real_norm_sq_eq]

theorem vorticitySelfTransportQuotientJet_le_fullDissipation
    (w : Vec3) (H : Fin 3 → Vec3) :
    vorticitySelfTransportQuotientJet w H ≤ ∑ j : Fin 3, ‖H j‖ ^ 2 := by
  by_cases hr : (∑ q : Fin 3, w q ^ 2) = 0
  · have hw := vec3_eq_zero_of_sq_sum_eq_zero w hr
    subst w
    have hzero : vorticitySelfTransportQuotientJet (0 : Vec3) H = 0 := by
      simp [vorticitySelfTransportQuotientJet, vorticitySelfTransportJet]
    rw [hzero]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · have hr0 : 0 < ∑ q : Fin 3, w q ^ 2 := lt_of_le_of_ne
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hr)
    have hbound := vorticitySelfTransportJet_norm_sq_le_fullDissipation w H
    rw [vorticitySelfTransportJet_norm_sq_eq_weight_mul_quotient] at hbound
    exact le_of_mul_le_mul_left hbound hr0

theorem vorticityDirectionProjectionTrace_sq_le
    (w : Vec3) (H : Fin 3 → Vec3) (hr : (∑ q : Fin 3, w q ^ 2) ≠ 0) :
    vorticityDirectionProjectionTrace w H ^ 2 ≤
      2 * vorticityDirectionDissipationJet w H := by
  have htrace := trace_sq_le_two_frobenius_of_rows_orthogonal w
    (fun j => vorticityDirectionProjection w (H j)) hr
    (fun j => inner_vorticity_directionProjection_eq_zero w (H j) hr)
  have hproj : (∑ j : Fin 3, ‖vorticityDirectionProjection w (H j)‖ ^ 2) =
      vorticityDirectionDissipationJet w H := by
    unfold vorticityDirectionDissipationJet
    apply Finset.sum_congr rfl
    intro j _hj
    exact vorticityDirectionProjection_norm_sq w (H j) hr
  simpa [vorticityDirectionProjectionTrace, hproj] using htrace

theorem vorticitySelfTransportJet_eq_projected_sub_trace
    (w : Vec3) (H : Fin 3 → Vec3)
    (hdiv : (∑ j : Fin 3, H j j) = 0) :
    vorticitySelfTransportJet w H =
      projectedVorticitySelfTransportJet w H -
        vorticityDirectionProjectionTrace w H • w := by
  let r : ℝ := ∑ q : Fin 3, w q ^ 2
  let b : Fin 3 → ℝ := fun j => (∑ q : Fin 3, w q * H j q) / r
  have hcomponent : ∀ (j i : Fin 3),
      H j i = vorticityDirectionProjection w (H j) i + b j * w i := by
    intro j i
    dsimp [vorticityDirectionProjection, b, r]
    ring
  have htrace : (∑ j : Fin 3, w j * b j) =
      -vorticityDirectionProjectionTrace w H := by
    have hdiv' := hdiv
    simp_rw [hcomponent] at hdiv'
    unfold vorticityDirectionProjectionTrace
    rw [Finset.sum_add_distrib] at hdiv'
    have hbcomm : (∑ j : Fin 3, b j * w j) = ∑ j : Fin 3, w j * b j := by
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    rw [hbcomm] at hdiv'
    linarith
  ext i
  unfold vorticitySelfTransportJet projectedVorticitySelfTransportJet
  simp only [PiLp.sub_apply, PiLp.smul_apply]
  simp_rw [hcomponent]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [show (∑ x : Fin 3, w x * (b x * w i)) =
      (∑ x : Fin 3, w x * b x) * w i by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [htrace]
  ring

/-- Strong zero-safe geometric depletion.  Besides the sharp factor `2`, it retains the
nonnegative projected self-transport correction which is lost in the usual bound. -/
theorem vorticitySelfTransportJet_norm_sq_add_projected_le_directionDissipation
    (w : Vec3) (H : Fin 3 → Vec3)
    (hdiv : (∑ j : Fin 3, H j j) = 0) :
    ‖vorticitySelfTransportJet w H‖ ^ 2 +
        ‖projectedVorticitySelfTransportJet w H‖ ^ 2 ≤
      2 * (∑ q : Fin 3, w q ^ 2) * vorticityDirectionDissipationJet w H := by
  by_cases hr : (∑ q : Fin 3, w q ^ 2) = 0
  · have hw := vec3_eq_zero_of_sq_sum_eq_zero w hr
    subst w
    have hz : vorticitySelfTransportJet (0 : Vec3) H = 0 := by
      ext i
      simp [vorticitySelfTransportJet]
    have hpz : projectedVorticitySelfTransportJet (0 : Vec3) H = 0 := by
      ext i
      simp [projectedVorticitySelfTransportJet]
    rw [hz, hpz]
    simp
  · let p : Vec3 := projectedVorticitySelfTransportJet w H
    let t : ℝ := vorticityDirectionProjectionTrace w H
    let r : ℝ := ∑ q : Fin 3, w q ^ 2
    let D : ℝ := vorticityDirectionDissipationJet w H
    let B : Fin 3 → Vec3 := fun j => vorticityDirectionProjection w (H j)
    let C : Fin 3 → Vec3 := fun j => B j - (w j / r) • p
    have hr0 : 0 ≤ r := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hD0 : 0 ≤ D := by
      dsimp [D, vorticityDirectionDissipationJet]
      exact Finset.sum_nonneg fun _ _ =>
        regularizedDirectorDirectionDerivativeSq_nonneg _ _
    have hdecomp : vorticitySelfTransportJet w H = p - t • w := by
      simpa [p, t] using vorticitySelfTransportJet_eq_projected_sub_trace w H hdiv
    have horth : inner ℝ p w = 0 := by
      exact inner_projectedVorticitySelfTransportJet_vorticity_eq_zero w H hr
    have horth' : inner ℝ w p = 0 := by
      rw [real_inner_comm]
      exact horth
    have hww : inner ℝ w w = r := by
      rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
    have hexact : ‖p - t • w‖ ^ 2 = ‖p‖ ^ 2 + t ^ 2 * r := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right]
      rw [horth, horth', hww, real_inner_self_eq_norm_sq]
      ring
    have hBorth : ∀ j : Fin 3, inner ℝ w (B j) = 0 := fun j => by
      exact inner_vorticity_directionProjection_eq_zero w (H j) hr
    have hpSum : p = ∑ j : Fin 3, w j • B j := by
      ext i
      simp [p, B, projectedVorticitySelfTransportJet]
    have hBnorm : (∑ j : Fin 3, ‖B j‖ ^ 2) = D := by
      dsimp [B, D, vorticityDirectionDissipationJet]
      apply Finset.sum_congr rfl
      intro j _hj
      exact vorticityDirectionProjection_norm_sq w (H j) hr
    have hweightedInner :
        (∑ j : Fin 3, w j * inner ℝ (B j) p) = ‖p‖ ^ 2 := by
      calc
        (∑ j : Fin 3, w j * inner ℝ (B j) p) =
            inner ℝ (∑ j : Fin 3, w j • B j) p := by
              symm
              calc
                inner ℝ (∑ j : Fin 3, w j • B j) p =
                    ∑ j : Fin 3, inner ℝ (w j • B j) p := by
                      simpa using
                        (sum_inner (𝕜 := ℝ) Finset.univ
                          (fun j : Fin 3 => w j • B j) p)
                _ = ∑ j : Fin 3, w j * inner ℝ (B j) p := by
                      apply Finset.sum_congr rfl
                      intro j _hj
                      rw [real_inner_smul_left]
        _ = inner ℝ p p := by rw [← hpSum]
        _ = ‖p‖ ^ 2 := real_inner_self_eq_norm_sq p
    have hcoeffSq : (∑ j : Fin 3, (w j / r) ^ 2) = 1 / r := by
      have hr' : r ≠ 0 := by simpa [r] using hr
      calc
        (∑ j : Fin 3, (w j / r) ^ 2) =
            (∑ j : Fin 3, w j ^ 2) / r ^ 2 := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j _hj
              rw [div_pow]
        _ = 1 / r := by
              dsimp [r]
              field_simp [hr]
    have hCnorm : r * (∑ j : Fin 3, ‖C j‖ ^ 2) =
        r * D - ‖p‖ ^ 2 := by
      have hCeach : ∀ j : Fin 3,
          ‖C j‖ ^ 2 = ‖B j‖ ^ 2 -
              2 * (w j / r) * inner ℝ (B j) p +
              (w j / r) ^ 2 * ‖p‖ ^ 2 := by
        intro j
        rw [← real_inner_self_eq_norm_sq]
        dsimp [C]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
          real_inner_smul_right, real_inner_self_eq_norm_sq]
        rw [real_inner_comm p (B j)]
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      simp_rw [hCeach]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul]
      rw [show (∑ j : Fin 3, 2 * (w j / r) * inner ℝ (B j) p) =
          (2 / r) * ∑ j : Fin 3, w j * inner ℝ (B j) p by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring]
      rw [hBnorm, hweightedInner, hcoeffSq]
      have hr' : r ≠ 0 := by simpa [r] using hr
      field_simp [hr']
      ring
    have hCorth : ∀ j : Fin 3, inner ℝ w (C j) = 0 := by
      intro j
      dsimp [C]
      rw [inner_sub_right, real_inner_smul_right, hBorth j, horth']
      ring
    have hCtrace : (∑ j : Fin 3, C j j) = t := by
      dsimp [C, t, vorticityDirectionProjectionTrace, B]
      rw [Finset.sum_sub_distrib]
      have hwp : (∑ j : Fin 3, w j * p j) = 0 := by
        have hpw := horth'
        rw [PiLp.inner_apply] at hpw
        simpa only [Real.inner_apply] using hpw
      rw [show (∑ j : Fin 3, (w j / r) * p j) =
          (1 / r) * ∑ j : Fin 3, w j * p j by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring]
      rw [hwp]
      ring
    have htC := trace_sq_le_two_frobenius_of_rows_orthogonal w C hr hCorth
    rw [hCtrace] at htC
    have htr : r * t ^ 2 ≤ 2 * (r * D - ‖p‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left htC hr0
      nlinarith [hCnorm]
    rw [hdecomp, hexact]
    dsimp [r, D] at ⊢
    nlinarith

theorem effectiveVorticityDirectionDissipationJet_nonneg
    (w : Vec3) (H : Fin 3 → Vec3)
    (hdiv : (∑ j : Fin 3, H j j) = 0) :
    0 ≤ effectiveVorticityDirectionDissipationJet w H := by
  let r : ℝ := ∑ q : Fin 3, w q ^ 2
  let p : Vec3 := projectedVorticitySelfTransportJet w H
  let D : ℝ := vorticityDirectionDissipationJet w H
  by_cases hr : r = 0
  · have hw := vec3_eq_zero_of_sq_sum_eq_zero w (by simpa [r] using hr)
    subst w
    simp [effectiveVorticityDirectionDissipationJet,
      vorticityDirectionDissipationJet, projectedVorticitySelfTransportJet,
      regularizedDirectorDirectionDerivativeSq]
  · have hr0 : 0 < r := lt_of_le_of_ne
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hr)
    have hstrong :=
      vorticitySelfTransportJet_norm_sq_add_projected_le_directionDissipation w H hdiv
    have hp : ‖p‖ ^ 2 ≤ 2 * r * D := by
      dsimp [p, r, D]
      nlinarith [hstrong, sq_nonneg ‖vorticitySelfTransportJet w H‖]
    have hdivp : ‖p‖ ^ 2 / r ≤ 2 * D := by
      apply (div_le_iff₀ hr0).2
      nlinarith
    change 0 ≤ 2 * D - ‖p‖ ^ 2 / r
    linarith

theorem vorticitySelfTransportJet_norm_sq_le_effectiveDirectionDissipation
    (w : Vec3) (H : Fin 3 → Vec3)
    (hdiv : (∑ j : Fin 3, H j j) = 0) :
    ‖vorticitySelfTransportJet w H‖ ^ 2 ≤
      (∑ q : Fin 3, w q ^ 2) *
        effectiveVorticityDirectionDissipationJet w H := by
  let r : ℝ := ∑ q : Fin 3, w q ^ 2
  let p : Vec3 := projectedVorticitySelfTransportJet w H
  let D : ℝ := vorticityDirectionDissipationJet w H
  by_cases hr : r = 0
  · have hw := vec3_eq_zero_of_sq_sum_eq_zero w (by simpa [r] using hr)
    subst w
    have hz : vorticitySelfTransportJet (0 : Vec3) H = 0 := by
      ext i
      simp [vorticitySelfTransportJet]
    rw [hz]
    simp
  · have hstrong :=
      vorticitySelfTransportJet_norm_sq_add_projected_le_directionDissipation w H hdiv
    have hr' : (∑ q : Fin 3, w q ^ 2) ≠ 0 := by simpa [r] using hr
    calc
      ‖vorticitySelfTransportJet w H‖ ^ 2 ≤ 2 * r * D - ‖p‖ ^ 2 := by
        dsimp [r, p, D]
        linarith [hstrong]
      _ = r * effectiveVorticityDirectionDissipationJet w H := by
        unfold effectiveVorticityDirectionDissipationJet
        dsimp [r, p, D]
        field_simp [hr']

theorem vorticitySelfTransportQuotientJet_le_effectiveDirectionDissipation
    (w : Vec3) (H : Fin 3 → Vec3)
    (hdiv : (∑ j : Fin 3, H j j) = 0) :
    vorticitySelfTransportQuotientJet w H ≤
      effectiveVorticityDirectionDissipationJet w H := by
  let r : ℝ := ∑ q : Fin 3, w q ^ 2
  by_cases hr : r = 0
  · have hw := vec3_eq_zero_of_sq_sum_eq_zero w (by simpa [r] using hr)
    subst w
    simp [vorticitySelfTransportQuotientJet,
      effectiveVorticityDirectionDissipationJet,
      vorticityDirectionDissipationJet, projectedVorticitySelfTransportJet,
      regularizedDirectorDirectionDerivativeSq]
  · have hr0 : 0 < r := lt_of_le_of_ne
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hr)
    have hbound :=
      vorticitySelfTransportJet_norm_sq_le_effectiveDirectionDissipation w H hdiv
    rw [vorticitySelfTransportJet_norm_sq_eq_weight_mul_quotient] at hbound
    apply (le_of_mul_le_mul_left hbound hr0)

/-- Zero-safe, direction-free form of the sharp geometric depletion estimate.  It controls
`|(w·∇)w|²` by the vorticity amplitude times only the derivative components orthogonal to
`w`; no normalized direction is chosen at `w = 0`. -/
theorem vorticitySelfTransportJet_norm_sq_le_directionDissipation
    (w : Vec3) (H : Fin 3 → Vec3)
    (hdiv : (∑ j : Fin 3, H j j) = 0) :
    ‖vorticitySelfTransportJet w H‖ ^ 2 ≤
      2 * (∑ q : Fin 3, w q ^ 2) * vorticityDirectionDissipationJet w H := by
  have hstrong :=
    vorticitySelfTransportJet_norm_sq_add_projected_le_directionDissipation w H hdiv
  nlinarith [sq_nonneg ‖projectedVorticitySelfTransportJet w H‖]

/-- Equality model showing that the coefficient `2` in the zero-safe jet estimate is sharp. -/
theorem vorticitySelfTransportJet_directionDissipation_constant_sharp :
    let w : Vec3 := EuclideanSpace.single 2 (1 : ℝ)
    let H : Fin 3 → Vec3 := fun j =>
      if j = 0 then EuclideanSpace.single 0 (1 : ℝ)
      else if j = 1 then EuclideanSpace.single 1 (1 : ℝ)
      else EuclideanSpace.single 2 (-2 : ℝ)
    (∑ j : Fin 3, H j j) = 0 ∧
      ‖vorticitySelfTransportJet w H‖ ^ 2 =
        2 * (∑ q : Fin 3, w q ^ 2) * vorticityDirectionDissipationJet w H := by
  dsimp
  constructor
  · simp [Fin.sum_univ_three]
    norm_num
  · simp [vorticitySelfTransportJet, vorticityDirectionDissipationJet,
      regularizedDirectorDirectionDerivativeSq, Fin.sum_univ_three,
      EuclideanSpace.real_norm_sq_eq]
    norm_num

/-- Vorticity-energy weight in the direction-only stretching ledger. -/
def periodicVorticityEnergyWeight (ω : Torus3 → Vec3) (x : Torus3) : ℝ :=
  ∑ q : Fin 3, ω x q ^ 2

/-- Velocity variance sampled by vorticity energy.  It is written as a finite sum of scalar
integrals so that the exact Haar centering theorem applies without hidden Fubini hypotheses. -/
def periodicVorticityWeightedVelocityVariance
    (u ω : Torus3 → Vec3) (a : Vec3) : ℝ :=
  ∑ j : Fin 3, ∫ x : Torus3,
    periodicVorticityEnergyWeight ω x * (u x j - a j) ^ 2

theorem periodicVorticityWeightedVelocityVariance_eq_integral_norm_sq
    (u ω : Torus3 → Vec3) (a : Vec3)
    (hcomponents : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight ω x * (u x j - a j) ^ 2)) :
    periodicVorticityWeightedVelocityVariance u ω a =
      ∫ x : Torus3, periodicVorticityEnergyWeight ω x *
        ‖centeredVelocity u a x‖ ^ 2 := by
  unfold periodicVorticityWeightedVelocityVariance
  rw [← MeasureTheory.integral_finsetSum Finset.univ
    (fun j _hj => hcomponents j)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ j : Fin 3,
      periodicVorticityEnergyWeight ω x * (u x j - a j) ^ 2) =
        periodicVorticityEnergyWeight ω x * ‖centeredVelocity u a x‖ ^ 2
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rfl

/-- The explicit vorticity-energy-weighted Galilean frame. -/
def periodicVorticityWeightedOptimalFrame
    (u ω : Torus3 → Vec3) : Vec3 :=
  periodicWeightedOptimalFrame (periodicVorticityEnergyWeight ω) u

@[simp]
theorem periodicVorticityWeightedOptimalFrame_apply
    (u ω : Torus3 → Vec3) (j : Fin 3) :
    periodicVorticityWeightedOptimalFrame u ω j =
      (∫ x : Torus3, periodicVorticityEnergyWeight ω x * u x j) /
        (∫ x : Torus3, periodicVorticityEnergyWeight ω x) := by
  rfl

/-- Exact vector Haar identity for the direction-only stretching weight. -/
theorem periodicVorticityWeightedOptimalFrame_centering
    (u ω : Torus3 → Vec3) (a : Vec3)
    (hweight : Integrable (periodicVorticityEnergyWeight ω))
    (hmoment : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight ω x * u x j))
    (hraw : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight ω x * u x j ^ 2))
    (hmass : (0 : ℝ) < ∫ x : Torus3, periodicVorticityEnergyWeight ω x) :
    periodicVorticityWeightedVelocityVariance u ω a =
      periodicVorticityWeightedVelocityVariance u ω
        (periodicVorticityWeightedOptimalFrame u ω) +
      (∫ x : Torus3, periodicVorticityEnergyWeight ω x) *
        ‖a - periodicVorticityWeightedOptimalFrame u ω‖ ^ 2 := by
  exact periodicWeightedOptimalFrame_centering
    (periodicVorticityEnergyWeight ω) u a hweight hmoment hraw hmass

/-- The vorticity-weighted frame globally minimizes the remaining critical velocity
variance among all spatially constant Galilean frames. -/
theorem periodicVorticityWeightedOptimalFrame_minimum
    (u ω : Torus3 → Vec3) (a : Vec3)
    (hweight : Integrable (periodicVorticityEnergyWeight ω))
    (hmoment : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight ω x * u x j))
    (hraw : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight ω x * u x j ^ 2))
    (hmass : (0 : ℝ) < ∫ x : Torus3, periodicVorticityEnergyWeight ω x) :
    periodicVorticityWeightedVelocityVariance u ω
        (periodicVorticityWeightedOptimalFrame u ω) ≤
      periodicVorticityWeightedVelocityVariance u ω a := by
  rw [periodicVorticityWeightedOptimalFrame_centering
    u ω a hweight hmoment hraw hmass]
  exact le_add_of_nonneg_right (mul_nonneg hmass.le (sq_nonneg _))

/-- Curvature vector `(ξ·∇)ξ` of a periodic direction field. -/
def periodicDirectionCurvature (ξ : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  WithLp.toLp 2 fun i => torusScalarTransport ξ (fun y => ξ y i) x

/-- Expansion-minus-curvature vector appearing in the exact stretching identity. -/
def periodicDirectionProductionVector (ξ : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  torusCoordinateDivergence ξ x • ξ x - periodicDirectionCurvature ξ x

/-- Coordinate divergence is bounded by three times the full Frobenius gradient square. -/
theorem periodicDirectionDivergence_sq_le
    (ξ : Torus3 → Vec3) (x : Torus3) :
    torusCoordinateDivergence ξ x ^ 2 ≤
      3 * periodicGradientFrobeniusSq ξ x := by
  let d : Fin 3 → Fin 3 → ℝ := fun i j => periodicFirstDerivative ξ i j x
  have hdiag : (d 0 0 + d 1 1 + d 2 2) ^ 2 ≤
      3 * (d 0 0 ^ 2 + d 1 1 ^ 2 + d 2 2 ^ 2) := by
    nlinarith [sq_nonneg (d 0 0 - d 1 1), sq_nonneg (d 0 0 - d 2 2),
      sq_nonneg (d 1 1 - d 2 2)]
  have hfull : d 0 0 ^ 2 + d 1 1 ^ 2 + d 2 2 ^ 2 ≤
      (d 0 0 ^ 2 + d 0 1 ^ 2 + d 0 2 ^ 2) +
      (d 1 0 ^ 2 + d 1 1 ^ 2 + d 1 2 ^ 2) +
      (d 2 0 ^ 2 + d 2 1 ^ 2 + d 2 2 ^ 2) := by
    nlinarith [sq_nonneg (d 0 1), sq_nonneg (d 0 2), sq_nonneg (d 1 0),
      sq_nonneg (d 1 2), sq_nonneg (d 2 0), sq_nonneg (d 2 1)]
  simp only [torusCoordinateDivergence, periodicGradientFrobeniusSq,
    periodicFirstDerivative, Fin.sum_univ_three]
  change (d 0 0 + d 1 1 + d 2 2) ^ 2 ≤
    3 * ((d 0 0 ^ 2 + d 0 1 ^ 2 + d 0 2 ^ 2) +
      (d 1 0 ^ 2 + d 1 1 ^ 2 + d 1 2 ^ 2) +
      (d 2 0 ^ 2 + d 2 1 ^ 2 + d 2 2 ^ 2))
  nlinarith

/-- Unit length turns directional self-transport into a contraction of the full gradient. -/
theorem periodicDirectionCurvature_norm_sq_le
    (ξ : Torus3 → Vec3) (x : Torus3) (hunit : ‖ξ x‖ = 1) :
    ‖periodicDirectionCurvature ξ x‖ ^ 2 ≤
      periodicGradientFrobeniusSq ξ x := by
  have hnorm : (∑ j : Fin 3, ξ x j ^ 2) = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq (ξ x)
    rw [hunit] at h
    norm_num at h ⊢
    exact h.symm
  have hcomponent : ∀ i : Fin 3,
      torusScalarTransport ξ (fun y => ξ y i) x ^ 2 ≤
        ∑ j : Fin 3, periodicFirstDerivative ξ j i x ^ 2 := by
    intro i
    have hcs := vec3_dot_sq_le_sq_sum_mul_sq_sum
      (ξ x) (WithLp.toLp 2 fun j => periodicFirstDerivative ξ j i x)
    rw [hnorm, one_mul] at hcs
    simpa [torusScalarTransport, periodicFirstDerivative] using hcs
  calc
    ‖periodicDirectionCurvature ξ x‖ ^ 2 =
        ∑ i : Fin 3, torusScalarTransport ξ (fun y => ξ y i) x ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        periodicFirstDerivative ξ j i x ^ 2 :=
      Finset.sum_le_sum fun i _hi => hcomponent i
    _ = periodicGradientFrobeniusSq ξ x := by
      unfold periodicGradientFrobeniusSq
      exact Finset.sum_comm

/-- If every coordinate derivative is tangent to the unit sphere, line curvature is
orthogonal to the direction. -/
theorem inner_direction_periodicDirectionCurvature_eq_zero
    (ξ : Torus3 → Vec3) (x : Torus3)
    (htangent : ∀ j : Fin 3,
      (∑ i : Fin 3, ξ x i * periodicFirstDerivative ξ j i x) = 0) :
    inner ℝ (ξ x) (periodicDirectionCurvature ξ x) = 0 := by
  rw [PiLp.inner_apply]
  unfold periodicDirectionCurvature torusScalarTransport
  simp only [Real.inner_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ x_1 : Fin 3, ∑ x_2 : Fin 3,
        ξ x x_2 * (ξ x x_1 *
          torusCoordinateDerivative (fun y => ξ y x_2) x_1 x)) =
        ∑ j : Fin 3, ξ x j *
          (∑ i : Fin 3, ξ x i * periodicFirstDerivative ξ j i x) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [periodicFirstDerivative]
      ring
    _ = 0 := by simp [htangent]

/-- Fully concrete constant-`4` bound for the direction-only production vector. -/
theorem periodicDirectionProductionVector_norm_sq_le
    (ξ : Torus3 → Vec3) (x : Torus3)
    (hunit : ‖ξ x‖ = 1)
    (htangent : ∀ j : Fin 3,
      (∑ i : Fin 3, ξ x i * periodicFirstDerivative ξ j i x) = 0) :
    ‖periodicDirectionProductionVector ξ x‖ ^ 2 ≤
      4 * periodicGradientFrobeniusSq ξ x := by
  unfold periodicDirectionProductionVector
  exact norm_directionExpansion_sub_curvature_sq_le
    (torusCoordinateDivergence ξ x) (periodicGradientFrobeniusSq ξ x)
    (ξ x) (periodicDirectionCurvature ξ x) hunit
    (inner_direction_periodicDirectionCurvature_eq_zero ξ x htangent)
    (periodicDirectionDivergence_sq_le ξ x)
    (periodicDirectionCurvature_norm_sq_le ξ x hunit)

/-- Direction-only production density.  Its two vector terms are the expansion and curvature
of the vorticity-line field. -/
def periodicDirectionProductionDensity
    (u : Torus3 → Vec3) (ρ : Torus3 → ℝ) (ξ : Torus3 → Vec3)
    (x : Torus3) : ℝ :=
  ρ x ^ 2 * ∑ i : Fin 3, u x i *
    (ξ x i * torusCoordinateDivergence ξ x -
      torusScalarTransport ξ (fun y => ξ y i) x)

theorem periodicDirectionProductionDensity_eq_inner
    (u : Torus3 → Vec3) (ρ : Torus3 → ℝ) (ξ : Torus3 → Vec3)
    (x : Torus3) :
    periodicDirectionProductionDensity u ρ ξ x =
      ρ x ^ 2 * inner ℝ (u x) (periodicDirectionProductionVector ξ x) := by
  unfold periodicDirectionProductionDensity periodicDirectionProductionVector
    periodicDirectionCurvature
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, PiLp.sub_apply, PiLp.smul_apply]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Pointwise direction-only stretching bound with the sharp elementary constant `2`. -/
theorem abs_periodicDirectionProductionDensity_le
    (u : Torus3 → Vec3) (ρ : Torus3 → ℝ) (ξ : Torus3 → Vec3)
    (x : Torus3) (hunit : ‖ξ x‖ = 1)
    (htangent : ∀ j : Fin 3,
      (∑ i : Fin 3, ξ x i * periodicFirstDerivative ξ j i x) = 0) :
    |periodicDirectionProductionDensity u ρ ξ x| ≤
      2 * ρ x ^ 2 * ‖u x‖ *
        Real.sqrt (periodicGradientFrobeniusSq ξ x) := by
  have hG := periodicGradientFrobeniusSq_nonneg ξ x
  have hvector := periodicDirectionProductionVector_norm_sq_le ξ x hunit htangent
  have hvectorNorm : ‖periodicDirectionProductionVector ξ x‖ ≤
      2 * Real.sqrt (periodicGradientFrobeniusSq ξ x) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    calc
      ‖periodicDirectionProductionVector ξ x‖ ^ 2 ≤
          4 * periodicGradientFrobeniusSq ξ x := hvector
      _ = (2 * Real.sqrt (periodicGradientFrobeniusSq ξ x)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hG]
        ring
  rw [periodicDirectionProductionDensity_eq_inner]
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    ρ x ^ 2 * |inner ℝ (u x) (periodicDirectionProductionVector ξ x)| ≤
        ρ x ^ 2 * (‖u x‖ * ‖periodicDirectionProductionVector ξ x‖) :=
      mul_le_mul_of_nonneg_left
        (abs_real_inner_le_norm (u x) (periodicDirectionProductionVector ξ x))
        (sq_nonneg _)
    _ ≤ ρ x ^ 2 *
        (‖u x‖ * (2 * Real.sqrt (periodicGradientFrobeniusSq ξ x))) := by
      gcongr
    _ = 2 * ρ x ^ 2 * ‖u x‖ *
        Real.sqrt (periodicGradientFrobeniusSq ξ x) := by ring

/-- Integrated direction-only Cauchy ledger.  Its second charge is the vorticity-energy-
weighted velocity variance, and its first charge is precisely direction dissipation. -/
theorem sq_abs_integral_periodicDirectionProductionDensity_le
    (u : Torus3 → Vec3) (ρ : Torus3 → ℝ) (ξ : Torus3 → Vec3)
    (hρ : ∀ x : Torus3, 0 ≤ ρ x)
    (hunit : ∀ x : Torus3, ‖ξ x‖ = 1)
    (htangent : ∀ (x : Torus3) (j : Fin 3),
      (∑ i : Fin 3, ξ x i * periodicFirstDerivative ξ j i x) = 0)
    (hdirection : MemLp (fun x : Torus3 =>
      ρ x * Real.sqrt (periodicGradientFrobeniusSq ξ x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 => ρ x * ‖u x‖) 2 volume) :
    |∫ x : Torus3, periodicDirectionProductionDensity u ρ ξ x| ^ 2 ≤
      4 * (∫ x : Torus3,
        ρ x ^ 2 * periodicGradientFrobeniusSq ξ x) *
        (∫ x : Torus3, ρ x ^ 2 * ‖u x‖ ^ 2) := by
  let f : Torus3 → ℝ := fun x =>
    ρ x * Real.sqrt (periodicGradientFrobeniusSq ξ x)
  let g : Torus3 → ℝ := fun x => ρ x * ‖u x‖
  have hf0 : ∀ x : Torus3, 0 ≤ f x := fun x =>
    mul_nonneg (hρ x) (Real.sqrt_nonneg _)
  have hg0 : ∀ x : Torus3, 0 ≤ g x := fun x =>
    mul_nonneg (hρ x) (norm_nonneg _)
  have hmajor : Integrable (fun x : Torus3 => 2 * (f x * g x)) :=
    (hdirection.integrable_mul hvariance).const_mul 2
  have habsIntegral :
      |∫ x : Torus3, periodicDirectionProductionDensity u ρ ξ x| ≤
        ∫ x : Torus3, 2 * (f x * g x) := by
    have hnorm := norm_integral_le_of_norm_le
      (f := periodicDirectionProductionDensity u ρ ξ)
      (g := fun x : Torus3 => 2 * (f x * g x)) hmajor
      (Eventually.of_forall fun x => by
        have hpoint := abs_periodicDirectionProductionDensity_le u ρ ξ x
          (hunit x) (htangent x)
        simp only [Real.norm_eq_abs]
        dsimp [f, g]
        exact hpoint.trans_eq (by ring))
    simpa only [Real.norm_eq_abs] using hnorm
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    hdirection hvariance
  have hmajor0 : 0 ≤ ∫ x : Torus3, 2 * (f x * g x) := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun x => mul_nonneg (by norm_num) (mul_nonneg (hf0 x) (hg0 x))
  have habs0 : 0 ≤ |∫ x : Torus3,
      periodicDirectionProductionDensity u ρ ξ x| := abs_nonneg _
  have hsquare := (sq_le_sq₀ habs0 hmajor0).2 habsIntegral
  rw [MeasureTheory.integral_const_mul] at hsquare
  have hfSq : (∫ x : Torus3, f x ^ 2) =
      ∫ x : Torus3, ρ x ^ 2 * periodicGradientFrobeniusSq ξ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [f]
      rw [mul_pow, Real.sq_sqrt (periodicGradientFrobeniusSq_nonneg ξ x)]
  have hgSq : (∫ x : Torus3, g x ^ 2) =
      ∫ x : Torus3, ρ x ^ 2 * ‖u x‖ ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [g]
      rw [mul_pow]
  rw [hfSq, hgSq] at hcs
  nlinarith

/-- The concrete periodic coordinate curl is divergence free once mixed second derivatives
commute.  This discharges the divergence hypothesis in the stretching identity for an actual
smooth curl field. -/
theorem torusCoordinateDivergence_periodicCoordinateCurl_eq_zero
    (u : Torus3 → Vec3) (x : Torus3)
    (hfirst : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun z => periodicFirstDerivative u k j z) i y))
    (hmixed : ∀ (i k j : Fin 3) (z : Torus3),
      periodicSecondDerivative u i k j z = periodicSecondDerivative u k i j z) :
    torusCoordinateDivergence (fun z => periodicCoordinateCurl u z) x = 0 := by
  unfold torusCoordinateDivergence
  simp only [Fin.sum_univ_three]
  change
    torusCoordinateDerivative (fun z =>
        periodicFirstDerivative u 1 2 z - periodicFirstDerivative u 2 1 z) 0 x +
      torusCoordinateDerivative (fun z =>
        periodicFirstDerivative u 2 0 z - periodicFirstDerivative u 0 2 z) 1 x +
      torusCoordinateDerivative (fun z =>
        periodicFirstDerivative u 0 1 z - periodicFirstDerivative u 1 0 z) 2 x = 0
  rw [torusCoordinateDerivative_sub
    (fun z => periodicFirstDerivative u 1 2 z)
    (fun z => periodicFirstDerivative u 2 1 z) 0 x
    (hfirst 0 1 2 _) (hfirst 0 2 1 _)]
  rw [torusCoordinateDerivative_sub
    (fun z => periodicFirstDerivative u 2 0 z)
    (fun z => periodicFirstDerivative u 0 2 z) 1 x
    (hfirst 1 2 0 _) (hfirst 1 0 2 _)]
  rw [torusCoordinateDerivative_sub
    (fun z => periodicFirstDerivative u 0 1 z)
    (fun z => periodicFirstDerivative u 1 0 z) 2 x
    (hfirst 2 0 1 _) (hfirst 2 1 0 _)]
  change periodicSecondDerivative u 0 1 2 x - periodicSecondDerivative u 0 2 1 x +
      (periodicSecondDerivative u 1 2 0 x - periodicSecondDerivative u 1 0 2 x) +
      (periodicSecondDerivative u 2 0 1 x - periodicSecondDerivative u 2 1 0 x) = 0
  rw [hmixed 1 0 2 x, hmixed 2 0 1 x, hmixed 2 1 0 x]
  ring

/-- Enstrophy-production density in vorticity variables. -/
def periodicVortexStretchingDensity
    (u ω : Torus3 → Vec3) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, ω x i * torusScalarTransport ω (fun y => u y i) x

@[simp]
theorem periodicVortexStretchingDensity_centeredVelocity
    (u ω : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    periodicVortexStretchingDensity (centeredVelocity u a) ω x =
      periodicVortexStretchingDensity u ω x := by
  unfold periodicVortexStretchingDensity torusScalarTransport
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  change ω x j * periodicFirstDerivative (centeredVelocity u a) j i x =
    ω x j * periodicFirstDerivative u j i x
  rw [periodicFirstDerivative_centeredVelocity]

/-- The self-transport pairing obtained after periodic integration by parts. -/
def periodicVorticitySelfTransportDensity
    (u ω : Torus3 → Vec3) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, torusScalarTransport ω (fun y => ω y i) x * u x i

/-- Vector self-transport `(\omega·\nabla)\omega` on the periodic coordinate model. -/
def periodicVorticitySelfTransportVector
    (ω : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  WithLp.toLp 2 fun i => torusScalarTransport ω (fun y => ω y i) x

/-- Direction-projected part of periodic vorticity self-transport. -/
def periodicProjectedVorticitySelfTransportVector
    (ω : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  projectedVorticitySelfTransportJet (ω x)
    (fun j => WithLp.toLp 2 fun i => periodicFirstDerivative ω j i x)

/-- Sharp effective periodic direction charge, including the projected-transport credit. -/
def periodicEffectiveVorticityDirectionDissipationSq
    (ω : Torus3 → Vec3) (x : Torus3) : ℝ :=
  effectiveVorticityDirectionDissipationJet (ω x)
    (fun j => WithLp.toLp 2 fun i => periodicFirstDerivative ω j i x)

/-- Exact periodic self-transport quotient, defined as zero on the vorticity zero set. -/
def periodicVorticitySelfTransportQuotientSq
    (ω : Torus3 → Vec3) (x : Torus3) : ℝ :=
  vorticitySelfTransportQuotientJet (ω x)
    (fun j => WithLp.toLp 2 fun i => periodicFirstDerivative ω j i x)

/-- Vorticity self-transport divided by `|ω|`, with the ambient real-field inverse
providing the zero value on the vorticity zero set. -/
def periodicNormalizedVorticitySelfTransportVector
    (ω : Torus3 → Vec3) (x : Torus3) : Vec3 :=
  ‖ω x‖⁻¹ • periodicVorticitySelfTransportVector ω x

/-- Velocity relative to a constant frame, multiplied by the vorticity magnitude. -/
def periodicVorticityWeightedCenteredVelocityVector
    (u ω : Torus3 → Vec3) (a : Vec3) (x : Torus3) : Vec3 :=
  ‖ω x‖ • centeredVelocity u a x

/-- Multiplying the zero-safe normalized self-transport by `|ω|` recovers
the original self-transport vector, including on the vorticity zero set. -/
theorem norm_smul_periodicNormalizedVorticitySelfTransportVector
    (ω : Torus3 → Vec3) (x : Torus3) :
    ‖ω x‖ • periodicNormalizedVorticitySelfTransportVector ω x =
      periodicVorticitySelfTransportVector ω x := by
  by_cases hω : ‖ω x‖ = 0
  · have hwx : ω x = 0 := norm_eq_zero.mp hω
    have hself : periodicVorticitySelfTransportVector ω x = 0 := by
      ext i
      simp [periodicVorticitySelfTransportVector, torusScalarTransport, hwx]
    simp [periodicNormalizedVorticitySelfTransportVector, hω, hself]
  · unfold periodicNormalizedVorticitySelfTransportVector
    rw [smul_smul, mul_inv_cancel₀ hω, one_smul]

/-- Multiplication by the vorticity magnitude clears the weight from the
weighted centered velocity. -/
theorem norm_smul_periodicVorticityWeightedCenteredVelocityVector
    (u ω : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    ‖ω x‖ • periodicVorticityWeightedCenteredVelocityVector u ω a x =
      ‖ω x‖ ^ 2 • centeredVelocity u a x := by
  unfold periodicVorticityWeightedCenteredVelocityVector
  rw [smul_smul, pow_two]

theorem periodicVorticitySelfTransportDensity_eq_inner
    (u ω : Torus3 → Vec3) (x : Torus3) :
    periodicVorticitySelfTransportDensity u ω x =
      inner ℝ (u x) (periodicVorticitySelfTransportVector ω x) := by
  unfold periodicVorticitySelfTransportDensity periodicVorticitySelfTransportVector
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Strong periodic pointwise depletion with its nonnegative projected-transport correction. -/
theorem periodicVorticitySelfTransportVector_norm_sq_add_projected_le_directionDissipation
    (ω : Torus3 → Vec3) (x : Torus3)
    (hdiv : torusCoordinateDivergence ω x = 0) :
    ‖periodicVorticitySelfTransportVector ω x‖ ^ 2 +
        ‖periodicProjectedVorticitySelfTransportVector ω x‖ ^ 2 ≤
      2 * (∑ q : Fin 3, ω x q ^ 2) *
        periodicVorticityDirectionDissipationSq ω x := by
  let H : Fin 3 → Vec3 := fun j =>
    WithLp.toLp 2 fun i => torusCoordinateDerivative (fun y => ω y i) j x
  have hjetDiv : (∑ j : Fin 3, H j j) = 0 := by
    simpa [H, torusCoordinateDivergence] using hdiv
  have hjet :=
    vorticitySelfTransportJet_norm_sq_add_projected_le_directionDissipation
      (ω x) H hjetDiv
  simpa [periodicVorticitySelfTransportVector,
    periodicProjectedVorticitySelfTransportVector, vorticitySelfTransportJet,
    projectedVorticitySelfTransportJet, vorticityDirectionDissipationJet,
    periodicVorticityDirectionDissipationSq, torusScalarTransport,
    periodicFirstDerivative, H] using hjet

theorem periodicEffectiveVorticityDirectionDissipationSq_nonneg
    (ω : Torus3 → Vec3) (x : Torus3)
    (hdiv : torusCoordinateDivergence ω x = 0) :
    0 ≤ periodicEffectiveVorticityDirectionDissipationSq ω x := by
  let H : Fin 3 → Vec3 := fun j =>
    WithLp.toLp 2 fun i => torusCoordinateDerivative (fun y => ω y i) j x
  have hjetDiv : (∑ j : Fin 3, H j j) = 0 := by
    simpa [H, torusCoordinateDivergence] using hdiv
  have hnonneg := effectiveVorticityDirectionDissipationJet_nonneg (ω x) H hjetDiv
  simpa [periodicEffectiveVorticityDirectionDissipationSq,
    periodicFirstDerivative, H] using hnonneg

theorem periodicVorticitySelfTransportQuotientSq_nonneg
    (ω : Torus3 → Vec3) (x : Torus3) :
    0 ≤ periodicVorticitySelfTransportQuotientSq ω x := by
  exact vorticitySelfTransportQuotientJet_nonneg _ _

theorem periodicVorticitySelfTransportVector_norm_sq_eq_weight_mul_quotient
    (ω : Torus3 → Vec3) (x : Torus3) :
    ‖periodicVorticitySelfTransportVector ω x‖ ^ 2 =
      (∑ q : Fin 3, ω x q ^ 2) *
        periodicVorticitySelfTransportQuotientSq ω x := by
  let H : Fin 3 → Vec3 := fun j =>
    WithLp.toLp 2 fun i => torusCoordinateDerivative (fun y => ω y i) j x
  have hid := vorticitySelfTransportJet_norm_sq_eq_weight_mul_quotient (ω x) H
  simpa [periodicVorticitySelfTransportVector,
    periodicVorticitySelfTransportQuotientSq, vorticitySelfTransportJet,
    torusScalarTransport, periodicFirstDerivative, H] using hid

/-- The normalized self-transport vector realizes the zero-safe quotient density
as its exact squared norm. -/
theorem periodicNormalizedVorticitySelfTransportVector_norm_sq
    (ω : Torus3 → Vec3) (x : Torus3) :
    ‖periodicNormalizedVorticitySelfTransportVector ω x‖ ^ 2 =
      periodicVorticitySelfTransportQuotientSq ω x := by
  by_cases hω : ‖ω x‖ = 0
  · have hwx : ω x = 0 := norm_eq_zero.mp hω
    have hself : periodicVorticitySelfTransportVector ω x = 0 := by
      ext i
      simp [periodicVorticitySelfTransportVector, torusScalarTransport, hwx]
    simp [periodicNormalizedVorticitySelfTransportVector, hself,
      periodicVorticitySelfTransportQuotientSq,
      vorticitySelfTransportQuotientJet, vorticitySelfTransportJet, hwx]
  · have hωpos : 0 < ‖ω x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hω)
    rw [periodicNormalizedVorticitySelfTransportVector, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hωpos), mul_pow]
    rw [periodicVorticitySelfTransportVector_norm_sq_eq_weight_mul_quotient]
    rw [← EuclideanSpace.real_norm_sq_eq (ω x)]
    field_simp [hω]

/-- The vorticity-weighted centered velocity realizes the variance density as
its exact squared norm. -/
theorem periodicVorticityWeightedCenteredVelocityVector_norm_sq
    (u ω : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    ‖periodicVorticityWeightedCenteredVelocityVector u ω a x‖ ^ 2 =
      periodicVorticityEnergyWeight ω x * ‖centeredVelocity u a x‖ ^ 2 := by
  rw [periodicVorticityWeightedCenteredVelocityVector, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_pow]
  unfold periodicVorticityEnergyWeight
  rw [← EuclideanSpace.real_norm_sq_eq (ω x)]

/-- The pointwise pairing of the two normalized fields is exactly the
self-transport density in the chosen Galilean frame. -/
theorem inner_periodicNormalizedSelfTransport_weightedCenteredVelocity
    (u ω : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    inner ℝ (periodicNormalizedVorticitySelfTransportVector ω x)
        (periodicVorticityWeightedCenteredVelocityVector u ω a x) =
      periodicVorticitySelfTransportDensity (centeredVelocity u a) ω x := by
  rw [periodicVorticitySelfTransportDensity_eq_inner]
  by_cases hω : ‖ω x‖ = 0
  · have hwx : ω x = 0 := norm_eq_zero.mp hω
    have hself : periodicVorticitySelfTransportVector ω x = 0 := by
      ext i
      simp [periodicVorticitySelfTransportVector, torusScalarTransport, hwx]
    simp [periodicNormalizedVorticitySelfTransportVector,
      periodicVorticityWeightedCenteredVelocityVector, hω, hself]
  · unfold periodicNormalizedVorticitySelfTransportVector
      periodicVorticityWeightedCenteredVelocityVector
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, inv_mul_cancel₀ hω, one_mul]
    exact real_inner_comm _ _

theorem periodicVorticitySelfTransportQuotientSq_le_effectiveDirectionDissipation
    (ω : Torus3 → Vec3) (x : Torus3)
    (hdiv : torusCoordinateDivergence ω x = 0) :
    periodicVorticitySelfTransportQuotientSq ω x ≤
      periodicEffectiveVorticityDirectionDissipationSq ω x := by
  let H : Fin 3 → Vec3 := fun j =>
    WithLp.toLp 2 fun i => torusCoordinateDerivative (fun y => ω y i) j x
  have hjetDiv : (∑ j : Fin 3, H j j) = 0 := by
    simpa [H, torusCoordinateDivergence] using hdiv
  have hbound :=
    vorticitySelfTransportQuotientJet_le_effectiveDirectionDissipation
      (ω x) H hjetDiv
  simpa [periodicVorticitySelfTransportQuotientSq,
    periodicEffectiveVorticityDirectionDissipationSq,
    periodicFirstDerivative, H] using hbound

theorem periodicVorticitySelfTransportQuotientSq_le_gradientFrobeniusSq
    (ω : Torus3 → Vec3) (x : Torus3) :
    periodicVorticitySelfTransportQuotientSq ω x ≤
      periodicGradientFrobeniusSq ω x := by
  let H : Fin 3 → Vec3 := fun j =>
    WithLp.toLp 2 fun i => periodicFirstDerivative ω j i x
  have hbound := vorticitySelfTransportQuotientJet_le_fullDissipation (ω x) H
  simpa [periodicVorticitySelfTransportQuotientSq,
    periodicGradientFrobeniusSq, EuclideanSpace.real_norm_sq_eq, H] using hbound

theorem periodicVorticitySelfTransportVector_norm_sq_le_effectiveDirectionDissipation
    (ω : Torus3 → Vec3) (x : Torus3)
    (hdiv : torusCoordinateDivergence ω x = 0) :
    ‖periodicVorticitySelfTransportVector ω x‖ ^ 2 ≤
      (∑ q : Fin 3, ω x q ^ 2) *
        periodicEffectiveVorticityDirectionDissipationSq ω x := by
  let H : Fin 3 → Vec3 := fun j =>
    WithLp.toLp 2 fun i => torusCoordinateDerivative (fun y => ω y i) j x
  have hjetDiv : (∑ j : Fin 3, H j j) = 0 := by
    simpa [H, torusCoordinateDivergence] using hdiv
  have hjet := vorticitySelfTransportJet_norm_sq_le_effectiveDirectionDissipation
    (ω x) H hjetDiv
  simpa [periodicVorticitySelfTransportVector,
    periodicEffectiveVorticityDirectionDissipationSq,
    vorticitySelfTransportJet, torusScalarTransport,
    periodicFirstDerivative, H] using hjet

/-- Exact pointwise production bound through the self-transport quotient. -/
theorem abs_periodicVorticitySelfTransportDensity_le_selfTransportQuotient
    (u ω : Torus3 → Vec3) (x : Torus3) :
    |periodicVorticitySelfTransportDensity u ω x| ≤
      Real.sqrt (periodicVorticitySelfTransportQuotientSq ω x) *
        ‖ω x‖ * ‖u x‖ := by
  let Q : ℝ := periodicVorticitySelfTransportQuotientSq ω x
  let r : ℝ := ∑ q : Fin 3, ω x q ^ 2
  let A : Vec3 := periodicVorticitySelfTransportVector ω x
  have hQ : 0 ≤ Q := periodicVorticitySelfTransportQuotientSq_nonneg ω x
  have hr : 0 ≤ r := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA : ‖A‖ ^ 2 = r * Q := by
    simpa [A, r, Q] using
      periodicVorticitySelfTransportVector_norm_sq_eq_weight_mul_quotient ω x
  have hnorm : ‖A‖ ≤ Real.sqrt Q * Real.sqrt r := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    have heq : ‖A‖ ^ 2 = (Real.sqrt Q * Real.sqrt r) ^ 2 := by
      rw [hA, mul_pow, Real.sq_sqrt hQ, Real.sq_sqrt hr]
      ring
    exact heq.le
  rw [periodicVorticitySelfTransportDensity_eq_inner]
  have hinner := abs_real_inner_le_norm (u x) A
  have hsqrtR : Real.sqrt r = ‖ω x‖ := by
    simpa [r, EuclideanSpace.real_norm_sq_eq] using
      (Real.sqrt_sq (norm_nonneg (ω x)))
  calc
    |inner ℝ (u x) A| ≤ ‖u x‖ * ‖A‖ := hinner
    _ ≤ ‖u x‖ * (Real.sqrt Q * Real.sqrt r) := by gcongr
    _ = Real.sqrt Q * ‖ω x‖ * ‖u x‖ := by
      rw [hsqrtR]
      ring

/-- Exact integrated quotient ledger.  This is the narrowest kinematic factorization of
vortex stretching before using any upper bound on vorticity-line geometry. -/
theorem sq_abs_integral_periodicVorticitySelfTransportDensity_le_selfTransportQuotient
    (u ω : Torus3 → Vec3)
    (hquotient : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 => ‖ω x‖ * ‖u x‖) 2 volume) :
    |∫ x : Torus3, periodicVorticitySelfTransportDensity u ω x| ^ 2 ≤
      (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq ω x) *
        (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) * ‖u x‖ ^ 2) := by
  let f : Torus3 → ℝ := fun x =>
    Real.sqrt (periodicVorticitySelfTransportQuotientSq ω x)
  let g : Torus3 → ℝ := fun x => ‖ω x‖ * ‖u x‖
  have hf0 : ∀ x : Torus3, 0 ≤ f x := fun x => Real.sqrt_nonneg _
  have hg0 : ∀ x : Torus3, 0 ≤ g x := fun x =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hmajor : Integrable (fun x : Torus3 => f x * g x) :=
    hquotient.integrable_mul hvariance
  have habsIntegral :
      |∫ x : Torus3, periodicVorticitySelfTransportDensity u ω x| ≤
        ∫ x : Torus3, f x * g x := by
    have hnorm := norm_integral_le_of_norm_le
      (f := periodicVorticitySelfTransportDensity u ω)
      (g := fun x : Torus3 => f x * g x) hmajor
      (Eventually.of_forall fun x => by
        have hpoint :=
          abs_periodicVorticitySelfTransportDensity_le_selfTransportQuotient u ω x
        simp only [Real.norm_eq_abs]
        dsimp [f, g]
        exact hpoint.trans_eq (by ring))
    simpa only [Real.norm_eq_abs] using hnorm
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    hquotient hvariance
  have hmajor0 : 0 ≤ ∫ x : Torus3, f x * g x := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun x => mul_nonneg (hf0 x) (hg0 x)
  have hsquare := (sq_le_sq₀ (abs_nonneg _) hmajor0).2 habsIntegral
  have hfSq : (∫ x : Torus3, f x ^ 2) =
      ∫ x : Torus3, periodicVorticitySelfTransportQuotientSq ω x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [f]
      rw [Real.sq_sqrt (periodicVorticitySelfTransportQuotientSq_nonneg ω x)]
  have hgSq : (∫ x : Torus3, g x ^ 2) =
      ∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) * ‖u x‖ ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [g]
      rw [mul_pow, EuclideanSpace.real_norm_sq_eq]
  rw [hfSq, hgSq] at hcs
  exact hsquare.trans hcs

/-- Pointwise production bound retaining the projected self-transport credit. -/
theorem abs_periodicVorticitySelfTransportDensity_le_effectiveDirectionDissipation
    (u ω : Torus3 → Vec3) (x : Torus3)
    (hdiv : torusCoordinateDivergence ω x = 0) :
    |periodicVorticitySelfTransportDensity u ω x| ≤
      Real.sqrt (periodicEffectiveVorticityDirectionDissipationSq ω x) *
        ‖ω x‖ * ‖u x‖ := by
  let E : ℝ := periodicEffectiveVorticityDirectionDissipationSq ω x
  let r : ℝ := ∑ q : Fin 3, ω x q ^ 2
  let A : Vec3 := periodicVorticitySelfTransportVector ω x
  have hE : 0 ≤ E := periodicEffectiveVorticityDirectionDissipationSq_nonneg ω x hdiv
  have hr : 0 ≤ r := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA : ‖A‖ ^ 2 ≤ r * E := by
    simpa [A, r, E] using
      periodicVorticitySelfTransportVector_norm_sq_le_effectiveDirectionDissipation
        ω x hdiv
  have hnorm : ‖A‖ ≤ Real.sqrt E * Real.sqrt r := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    calc
      ‖A‖ ^ 2 ≤ r * E := hA
      _ = (Real.sqrt E * Real.sqrt r) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hr]
        ring
  rw [periodicVorticitySelfTransportDensity_eq_inner]
  have hinner := abs_real_inner_le_norm (u x) A
  have hsqrtR : Real.sqrt r = ‖ω x‖ := by
    simpa [r, EuclideanSpace.real_norm_sq_eq] using
      (Real.sqrt_sq (norm_nonneg (ω x)))
  calc
    |inner ℝ (u x) A| ≤ ‖u x‖ * ‖A‖ := hinner
    _ ≤ ‖u x‖ * (Real.sqrt E * Real.sqrt r) := by gcongr
    _ = Real.sqrt E * ‖ω x‖ * ‖u x‖ := by
      rw [hsqrtR]
      ring

/-- Strongest integrated zero-safe ledger currently available: the direction factor is the
sharp effective charge `2 Dξ` minus the projected self-transport credit. -/
theorem sq_abs_integral_periodicVorticitySelfTransportDensity_le_effectiveDirection
    (u ω : Torus3 → Vec3)
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0)
    (heffective : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicEffectiveVorticityDirectionDissipationSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 => ‖ω x‖ * ‖u x‖) 2 volume) :
    |∫ x : Torus3, periodicVorticitySelfTransportDensity u ω x| ^ 2 ≤
      (∫ x : Torus3, periodicEffectiveVorticityDirectionDissipationSq ω x) *
        (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) * ‖u x‖ ^ 2) := by
  let f : Torus3 → ℝ := fun x =>
    Real.sqrt (periodicEffectiveVorticityDirectionDissipationSq ω x)
  let g : Torus3 → ℝ := fun x => ‖ω x‖ * ‖u x‖
  have hf0 : ∀ x : Torus3, 0 ≤ f x := fun x => Real.sqrt_nonneg _
  have hg0 : ∀ x : Torus3, 0 ≤ g x := fun x =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hmajor : Integrable (fun x : Torus3 => f x * g x) :=
    heffective.integrable_mul hvariance
  have habsIntegral :
      |∫ x : Torus3, periodicVorticitySelfTransportDensity u ω x| ≤
        ∫ x : Torus3, f x * g x := by
    have hnorm := norm_integral_le_of_norm_le
      (f := periodicVorticitySelfTransportDensity u ω)
      (g := fun x : Torus3 => f x * g x) hmajor
      (Eventually.of_forall fun x => by
        have hpoint :=
          abs_periodicVorticitySelfTransportDensity_le_effectiveDirectionDissipation
            u ω x (hdiv x)
        simp only [Real.norm_eq_abs]
        dsimp [f, g]
        exact hpoint.trans_eq (by ring))
    simpa only [Real.norm_eq_abs] using hnorm
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    heffective hvariance
  have hmajor0 : 0 ≤ ∫ x : Torus3, f x * g x := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun x => mul_nonneg (hf0 x) (hg0 x)
  have hsquare := (sq_le_sq₀ (abs_nonneg _) hmajor0).2 habsIntegral
  have hfSq : (∫ x : Torus3, f x ^ 2) =
      ∫ x : Torus3, periodicEffectiveVorticityDirectionDissipationSq ω x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [f]
      rw [Real.sq_sqrt
        (periodicEffectiveVorticityDirectionDissipationSq_nonneg ω x (hdiv x))]
  have hgSq : (∫ x : Torus3, g x ^ 2) =
      ∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) * ‖u x‖ ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [g]
      rw [mul_pow, EuclideanSpace.real_norm_sq_eq]
  rw [hfSq, hgSq] at hcs
  exact hsquare.trans hcs

/-- Zero-safe pointwise geometric depletion, expressed entirely through `ω` and `∇ω`. -/
theorem periodicVorticitySelfTransportVector_norm_sq_le_directionDissipation
    (ω : Torus3 → Vec3) (x : Torus3)
    (hdiv : torusCoordinateDivergence ω x = 0) :
    ‖periodicVorticitySelfTransportVector ω x‖ ^ 2 ≤
      2 * (∑ q : Fin 3, ω x q ^ 2) *
        periodicVorticityDirectionDissipationSq ω x := by
  let H : Fin 3 → Vec3 := fun j =>
    WithLp.toLp 2 fun i => torusCoordinateDerivative (fun y => ω y i) j x
  have hjetDiv : (∑ j : Fin 3, H j j) = 0 := by
    simpa [H, torusCoordinateDivergence] using hdiv
  have hjet := vorticitySelfTransportJet_norm_sq_le_directionDissipation
    (ω x) H hjetDiv
  simpa [periodicVorticitySelfTransportVector, vorticitySelfTransportJet,
    vorticityDirectionDissipationJet, periodicVorticityDirectionDissipationSq,
    torusScalarTransport, periodicFirstDerivative, H] using hjet

/-- Pointwise signed production bound without a normalized direction or zero-set convention. -/
theorem abs_periodicVorticitySelfTransportDensity_le
    (u ω : Torus3 → Vec3) (x : Torus3)
    (hdiv : torusCoordinateDivergence ω x = 0) :
    |periodicVorticitySelfTransportDensity u ω x| ≤
      Real.sqrt 2 * Real.sqrt (periodicVorticityDirectionDissipationSq ω x) *
        ‖ω x‖ * ‖u x‖ := by
  let D : ℝ := periodicVorticityDirectionDissipationSq ω x
  let r : ℝ := ∑ q : Fin 3, ω x q ^ 2
  let A : Vec3 := periodicVorticitySelfTransportVector ω x
  have hD : 0 ≤ D := periodicVorticityDirectionDissipationSq_nonneg ω x
  have hr : 0 ≤ r := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA : ‖A‖ ^ 2 ≤ 2 * r * D := by
    simpa [A, r, D] using
      periodicVorticitySelfTransportVector_norm_sq_le_directionDissipation ω x hdiv
  have hnorm : ‖A‖ ≤ Real.sqrt 2 * Real.sqrt D * Real.sqrt r := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))).mp
    calc
      ‖A‖ ^ 2 ≤ 2 * r * D := hA
      _ = (Real.sqrt 2 * Real.sqrt D * Real.sqrt r) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sq_sqrt hD, Real.sq_sqrt hr]
        ring
  rw [periodicVorticitySelfTransportDensity_eq_inner]
  have hinner := abs_real_inner_le_norm (u x) A
  have hsqrtR : Real.sqrt r = ‖ω x‖ := by
    simpa [r, EuclideanSpace.real_norm_sq_eq] using
      (Real.sqrt_sq (norm_nonneg (ω x)))
  calc
    |inner ℝ (u x) A| ≤ ‖u x‖ * ‖A‖ := hinner
    _ ≤ ‖u x‖ * (Real.sqrt 2 * Real.sqrt D * Real.sqrt r) := by gcongr
    _ = Real.sqrt 2 * Real.sqrt D * ‖ω x‖ * ‖u x‖ := by
      rw [hsqrtR]
      ring

/-- Integrated zero-safe direction-only ledger.  This is the normalized-direction estimate
with every zero-set and orientation choice removed. -/
theorem sq_abs_integral_periodicVorticitySelfTransportDensity_le
    (u ω : Torus3 → Vec3)
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0)
    (hdirection : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticityDirectionDissipationSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 => ‖ω x‖ * ‖u x‖) 2 volume) :
    |∫ x : Torus3, periodicVorticitySelfTransportDensity u ω x| ^ 2 ≤
      2 * (∫ x : Torus3, periodicVorticityDirectionDissipationSq ω x) *
        (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) * ‖u x‖ ^ 2) := by
  let f : Torus3 → ℝ := fun x =>
    Real.sqrt (periodicVorticityDirectionDissipationSq ω x)
  let g : Torus3 → ℝ := fun x => ‖ω x‖ * ‖u x‖
  have hf0 : ∀ x : Torus3, 0 ≤ f x := fun x => Real.sqrt_nonneg _
  have hg0 : ∀ x : Torus3, 0 ≤ g x := fun x =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hmajor : Integrable (fun x : Torus3 => Real.sqrt 2 * (f x * g x)) :=
    (hdirection.integrable_mul hvariance).const_mul (Real.sqrt 2)
  have habsIntegral :
      |∫ x : Torus3, periodicVorticitySelfTransportDensity u ω x| ≤
        ∫ x : Torus3, Real.sqrt 2 * (f x * g x) := by
    have hnorm := norm_integral_le_of_norm_le
      (f := periodicVorticitySelfTransportDensity u ω)
      (g := fun x : Torus3 => Real.sqrt 2 * (f x * g x)) hmajor
      (Eventually.of_forall fun x => by
        have hpoint := abs_periodicVorticitySelfTransportDensity_le u ω x (hdiv x)
        simp only [Real.norm_eq_abs]
        dsimp [f, g]
        exact hpoint.trans_eq (by ring))
    simpa only [Real.norm_eq_abs] using hnorm
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    hdirection hvariance
  have hmajor0 : 0 ≤ ∫ x : Torus3, Real.sqrt 2 * (f x * g x) := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun x =>
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hf0 x) (hg0 x))
  have hsquare := (sq_le_sq₀ (abs_nonneg _) hmajor0).2 habsIntegral
  rw [MeasureTheory.integral_const_mul] at hsquare
  have hfSq : (∫ x : Torus3, f x ^ 2) =
      ∫ x : Torus3, periodicVorticityDirectionDissipationSq ω x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [f]
      rw [Real.sq_sqrt (periodicVorticityDirectionDissipationSq_nonneg ω x)]
  have hgSq : (∫ x : Torus3, g x ^ 2) =
      ∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) * ‖u x‖ ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [g]
      rw [mul_pow, EuclideanSpace.real_norm_sq_eq]
  rw [hfSq, hgSq] at hcs
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Periodic vortex stretching is the negative pairing of velocity with vorticity
self-transport.  The divergence-free condition on `ω` is displayed explicitly. -/
theorem integral_periodicVortexStretching_eq_neg_selfTransport
    (u ω : Torus3 → Vec3)
    (hωtransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x j) j y))
    (hω : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x i) j y))
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((ω x i) * ω x j) * periodicFirstDerivative u j i x))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => ω z i * ω z j) j x * u x i))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0) :
    (∫ x : Torus3, periodicVortexStretchingDensity u ω x) =
      -∫ x : Torus3, periodicVorticitySelfTransportDensity u ω x := by
  have hcomponent : ∀ i : Fin 3,
      (∫ x : Torus3, ω x i * torusScalarTransport ω (fun y => u y i) x) =
        -∫ x : Torus3,
          torusScalarTransport ω (fun y => ω y i) x * u x i := by
    intro i
    exact torus3_divergenceFree_transport_skew
      ω (fun x => ω x i) (fun x => u x i)
      hωtransport (hω i) (hu i)
      (fun j => by simpa [periodicFirstDerivative] using hleft i j)
      (fun j => hright i j) hdiv
  have hleftComponent : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      ω x i * torusScalarTransport ω (fun y => u y i) x) := by
    intro i
    unfold torusScalarTransport
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum Finset.univ fun j _hj => by
      simpa only [periodicFirstDerivative, mul_assoc] using hleft i j
  have hrightComponent : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      torusScalarTransport ω (fun y => ω y i) x * u x i) := by
    intro i
    have htransport := integrable_finsetSum Finset.univ fun j _hj => hright i j
    have heq : (fun x : Torus3 =>
        torusScalarTransport ω (fun y => ω y i) x * u x i) =
        fun x : Torus3 =>
          ∑ j : Fin 3,
            torusCoordinateDerivative (fun z => ω z i * ω z j) j x * u x i := by
      funext x
      simp only [torusScalarTransport]
      rw [Finset.sum_mul]
      have hproduct : ∀ j : Fin 3,
          torusCoordinateDerivative (fun z => ω z i * ω z j) j x =
            periodicFirstDerivative ω j i x * ω x j +
              ω x i * periodicFirstDerivative ω j j x := by
        intro j
        simpa [periodicFirstDerivative] using
          torusCoordinateDerivative_mul (fun z => ω z i) (fun z => ω z j) j x
            (hω i j _) (hω j j _)
      simp_rw [hproduct, add_mul]
      rw [Finset.sum_add_distrib]
      rw [show (∑ j : Fin 3,
          ω x i * periodicFirstDerivative ω j j x * u x i) = 0 by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        change ω x i * torusCoordinateDivergence ω x * u x i = 0
        rw [hdiv]
        ring]
      simp only [add_zero, periodicFirstDerivative]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    rw [heq]
    exact htransport
  unfold periodicVortexStretchingDensity periodicVorticitySelfTransportDensity
  rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun i _hi => hleftComponent i),
    MeasureTheory.integral_finsetSum Finset.univ
      (fun i _hi => hrightComponent i)]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _hi => hcomponent i

/-- The zero-safe direction-depletion estimate for the actual periodic vortex-stretching
integral.  No normalized vorticity direction is chosen, including on the zero set of `ω`. -/
theorem sq_integral_periodicVortexStretching_le_directionDissipation_weightedVelocity
    (u ω : Torus3 → Vec3)
    (hωtransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x j) j y))
    (hω : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x i) j y))
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((ω x i) * ω x j) * periodicFirstDerivative u j i x))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => ω z i * ω z j) j x * u x i))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0)
    (hdirection : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticityDirectionDissipationSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 => ‖ω x‖ * ‖u x‖) 2 volume) :
    (∫ x : Torus3, periodicVortexStretchingDensity u ω x) ^ 2 ≤
      2 * (∫ x : Torus3, periodicVorticityDirectionDissipationSq ω x) *
        (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) * ‖u x‖ ^ 2) := by
  have hparts := integral_periodicVortexStretching_eq_neg_selfTransport
    u ω hωtransport hω hu hleft hright hdiv
  have hself := sq_abs_integral_periodicVorticitySelfTransportDensity_le
    u ω hdiv hdirection hvariance
  rw [hparts]
  simpa only [neg_sq, sq_abs] using hself

/-- Actual vortex-stretching estimate with the projected self-transport credit retained. -/
theorem sq_integral_periodicVortexStretching_le_effectiveDirection_weightedVelocity
    (u ω : Torus3 → Vec3)
    (hωtransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x j) j y))
    (hω : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x i) j y))
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((ω x i) * ω x j) * periodicFirstDerivative u j i x))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => ω z i * ω z j) j x * u x i))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0)
    (heffective : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicEffectiveVorticityDirectionDissipationSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 => ‖ω x‖ * ‖u x‖) 2 volume) :
    (∫ x : Torus3, periodicVortexStretchingDensity u ω x) ^ 2 ≤
      (∫ x : Torus3, periodicEffectiveVorticityDirectionDissipationSq ω x) *
        (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) * ‖u x‖ ^ 2) := by
  have hparts := integral_periodicVortexStretching_eq_neg_selfTransport
    u ω hωtransport hω hu hleft hright hdiv
  have hself :=
    sq_abs_integral_periodicVorticitySelfTransportDensity_le_effectiveDirection
      u ω hdiv heffective hvariance
  rw [hparts]
  simpa only [neg_sq, sq_abs] using hself

/-- Narrowest exact kinematic factorization of the actual vortex-stretching integral. -/
theorem sq_integral_periodicVortexStretching_le_selfTransportQuotient_weightedVelocity
    (u ω : Torus3 → Vec3)
    (hωtransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x j) j y))
    (hω : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x i) j y))
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((ω x i) * ω x j) * periodicFirstDerivative u j i x))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => ω z i * ω z j) j x * u x i))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0)
    (hquotient : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 => ‖ω x‖ * ‖u x‖) 2 volume) :
    (∫ x : Torus3, periodicVortexStretchingDensity u ω x) ^ 2 ≤
      (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq ω x) *
        (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) * ‖u x‖ ^ 2) := by
  have hparts := integral_periodicVortexStretching_eq_neg_selfTransport
    u ω hωtransport hω hu hleft hright hdiv
  have hself :=
    sq_abs_integral_periodicVorticitySelfTransportDensity_le_selfTransportQuotient
      u ω hquotient hvariance
  rw [hparts]
  simpa only [neg_sq, sq_abs] using hself

/-- Galilean-centered form of the zero-safe vortex-stretching ledger.  The last factor is
the vorticity-energy-weighted velocity variance about the chosen constant frame `a`. -/
theorem sq_integral_periodicVortexStretching_le_directionDissipation_centeredVelocity
    (u ω : Torus3 → Vec3) (a : Vec3)
    (hωtransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x j) j y))
    (hω : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x i) j y))
    (hucentered : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => centeredVelocity u a x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((ω x i) * ω x j) * periodicFirstDerivative u j i x))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => ω z i * ω z j) j x *
        centeredVelocity u a x i))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0)
    (hdirection : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticityDirectionDissipationSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 =>
      ‖ω x‖ * ‖centeredVelocity u a x‖) 2 volume) :
    (∫ x : Torus3, periodicVortexStretchingDensity u ω x) ^ 2 ≤
      2 * (∫ x : Torus3, periodicVorticityDirectionDissipationSq ω x) *
        (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) *
          ‖centeredVelocity u a x‖ ^ 2) := by
  have hbound :=
    sq_integral_periodicVortexStretching_le_directionDissipation_weightedVelocity
      (centeredVelocity u a) ω hωtransport hω hucentered
      (fun i j => by simpa using hleft i j) hright hdiv hdirection hvariance
  simpa using hbound

/-- The centered estimate in the exact scalar variance used by the critical-product
criterion. -/
theorem sq_integral_periodicVortexStretching_le_directionDissipation_weightedVariance
    (u ω : Torus3 → Vec3) (a : Vec3)
    (hωtransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x j) j y))
    (hω : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x i) j y))
    (hucentered : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => centeredVelocity u a x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((ω x i) * ω x j) * periodicFirstDerivative u j i x))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => ω z i * ω z j) j x *
        centeredVelocity u a x i))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0)
    (hdirection : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticityDirectionDissipationSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 =>
      ‖ω x‖ * ‖centeredVelocity u a x‖) 2 volume)
    (hcomponents : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight ω x * (u x j - a j) ^ 2)) :
    (∫ x : Torus3, periodicVortexStretchingDensity u ω x) ^ 2 ≤
      2 * (∫ x : Torus3, periodicVorticityDirectionDissipationSq ω x) *
        periodicVorticityWeightedVelocityVariance u ω a := by
  have hbound :=
    sq_integral_periodicVortexStretching_le_directionDissipation_centeredVelocity
      u ω a hωtransport hω hucentered hleft hright hdiv hdirection hvariance
  have hvarianceEq :
      (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) *
        ‖centeredVelocity u a x‖ ^ 2) =
        periodicVorticityWeightedVelocityVariance u ω a := by
    symm
    simpa [periodicVorticityEnergyWeight] using
      periodicVorticityWeightedVelocityVariance_eq_integral_norm_sq
        u ω a hcomponents
  rw [hvarianceEq] at hbound
  exact hbound

/-- Optimal-frame form of the strongest current production ledger.  Its first factor is
`2 Dξ` minus the explicit projected self-transport credit. -/
theorem sq_integral_periodicVortexStretching_le_effectiveDirection_weightedVariance
    (u ω : Torus3 → Vec3) (a : Vec3)
    (hωtransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x j) j y))
    (hω : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x i) j y))
    (hucentered : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => centeredVelocity u a x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((ω x i) * ω x j) * periodicFirstDerivative u j i x))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => ω z i * ω z j) j x *
        centeredVelocity u a x i))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0)
    (heffective : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicEffectiveVorticityDirectionDissipationSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 =>
      ‖ω x‖ * ‖centeredVelocity u a x‖) 2 volume)
    (hcomponents : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight ω x * (u x j - a j) ^ 2)) :
    (∫ x : Torus3, periodicVortexStretchingDensity u ω x) ^ 2 ≤
      (∫ x : Torus3, periodicEffectiveVorticityDirectionDissipationSq ω x) *
        periodicVorticityWeightedVelocityVariance u ω a := by
  have hbound :=
    sq_integral_periodicVortexStretching_le_effectiveDirection_weightedVelocity
      (centeredVelocity u a) ω hωtransport hω hucentered
      (fun i j => by simpa using hleft i j) hright hdiv heffective hvariance
  have hvarianceEq :
      (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) *
        ‖centeredVelocity u a x‖ ^ 2) =
        periodicVorticityWeightedVelocityVariance u ω a := by
    symm
    simpa [periodicVorticityEnergyWeight] using
      periodicVorticityWeightedVelocityVariance_eq_integral_norm_sq
        u ω a hcomponents
  rw [hvarianceEq] at hbound
  simpa using hbound

/-- Optimal-frame version of the exact self-transport quotient factorization. -/
theorem sq_integral_periodicVortexStretching_le_selfTransportQuotient_weightedVariance
    (u ω : Torus3 → Vec3) (a : Vec3)
    (hωtransport : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x j) j y))
    (hω : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ω x i) j y))
    (hucentered : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => centeredVelocity u a x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      ((ω x i) * ω x j) * periodicFirstDerivative u j i x))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative (fun z => ω z i * ω z j) j x *
        centeredVelocity u a x i))
    (hdiv : ∀ x : Torus3, torusCoordinateDivergence ω x = 0)
    (hquotient : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticitySelfTransportQuotientSq ω x)) 2 volume)
    (hvariance : MemLp (fun x : Torus3 =>
      ‖ω x‖ * ‖centeredVelocity u a x‖) 2 volume)
    (hcomponents : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicVorticityEnergyWeight ω x * (u x j - a j) ^ 2)) :
    (∫ x : Torus3, periodicVortexStretchingDensity u ω x) ^ 2 ≤
      (∫ x : Torus3, periodicVorticitySelfTransportQuotientSq ω x) *
        periodicVorticityWeightedVelocityVariance u ω a := by
  have hbound :=
    sq_integral_periodicVortexStretching_le_selfTransportQuotient_weightedVelocity
      (centeredVelocity u a) ω hωtransport hω hucentered
      (fun i j => by simpa using hleft i j) hright hdiv hquotient hvariance
  have hvarianceEq :
      (∫ x : Torus3, (∑ q : Fin 3, ω x q ^ 2) *
        ‖centeredVelocity u a x‖ ^ 2) =
        periodicVorticityWeightedVelocityVariance u ω a := by
    symm
    simpa [periodicVorticityEnergyWeight] using
      periodicVorticityWeightedVelocityVariance_eq_integral_norm_sq
        u ω a hcomponents
  rw [hvarianceEq] at hbound
  simpa using hbound

/-- Vortex stretching written in scalar-amplitude and unit-direction variables. -/
def periodicDirectionalStretchingDensity
    (u : Torus3 → Vec3) (ρ : Torus3 → ℝ) (ξ : Torus3 → Vec3)
    (x : Torus3) : ℝ :=
  ∑ i : Fin 3, ρ x ^ 2 * ξ x i *
    torusScalarTransport ξ (fun y => u y i) x

/-- Exact periodic amplitude/direction formula for total vortex stretching.  The scalar
amplitude derivative cancels by `div (ρ ξ) = 0`; only direction deformation remains. -/
theorem integral_periodicDirectionalStretching_eq_directionProduction
    (u : Torus3 → Vec3) (ρ : Torus3 → ℝ) (ξ : Torus3 → Vec3)
    (hρ : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift ρ j y))
    (hξ : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => ξ x i) j y))
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x i) j y))
    (hleft : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      (((ρ x ^ 2 * ξ x i) * ξ x j) * periodicFirstDerivative u j i x)))
    (hright : ∀ i j : Fin 3, Integrable (fun x : Torus3 =>
      torusCoordinateDerivative
        (fun z => (ρ z ^ 2 * ξ z i) * ξ z j) j x * u x i))
    (hproduction : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      ρ x ^ 2 * u x i *
        (ξ x i * torusCoordinateDivergence ξ x -
          torusScalarTransport ξ (fun y => ξ y i) x)))
    (hdiv : ∀ x : Torus3,
      torusScalarTransport ξ ρ x +
        ρ x * torusCoordinateDivergence ξ x = 0) :
    (∫ x : Torus3, periodicDirectionalStretchingDensity u ρ ξ x) =
      ∫ x : Torus3, periodicDirectionProductionDensity u ρ ξ x := by
  have hcomponent : ∀ i : Fin 3,
      (∫ x : Torus3, ρ x ^ 2 * ξ x i *
        torusScalarTransport ξ (fun y => u y i) x) =
      ∫ x : Torus3, ρ x ^ 2 * u x i *
        (ξ x i * torusCoordinateDivergence ξ x -
          torusScalarTransport ξ (fun y => ξ y i) x) := by
    intro i
    let f : Torus3 → ℝ := fun x => ρ x ^ 2 * ξ x i
    have hf : ∀ (j : Fin 3) (y : TorusCoordinateComplement),
        ContDiff ℝ 1 (torusCoordinateSliceLift f j y) := by
      intro j y
      change ContDiff ℝ 1 (fun r =>
        torusCoordinateSliceLift ρ j y r ^ 2 *
          torusCoordinateSliceLift (fun x => ξ x i) j y r)
      exact ((hρ j y).pow 2).mul (hξ i j y)
    have hparts := torus3_transport_integration_by_parts
      ξ f (fun x => u x i)
      (fun j y => hξ j j y) hf (hu i)
      (fun j => by simpa [f, periodicFirstDerivative] using hleft i j)
      (fun j => by simpa [f] using hright i j)
    calc
      (∫ x : Torus3, ρ x ^ 2 * ξ x i *
          torusScalarTransport ξ (fun y => u y i) x) =
          ∫ x : Torus3, f x * torusScalarTransport ξ (fun y => u y i) x := by
            rfl
      _ = -∫ x : Torus3,
          (torusScalarTransport ξ f x +
            f x * torusCoordinateDivergence ξ x) * u x i := hparts
      _ = ∫ x : Torus3, ρ x ^ 2 * u x i *
          (ξ x i * torusCoordinateDivergence ξ x -
            torusScalarTransport ξ (fun y => ξ y i) x) := by
        rw [← MeasureTheory.integral_neg]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          have htransport : torusScalarTransport ξ f x =
              2 * ρ x * torusScalarTransport ξ ρ x * ξ x i +
                ρ x ^ 2 * torusScalarTransport ξ (fun y => ξ y i) x := by
            unfold torusScalarTransport
            have hderiv : ∀ j : Fin 3,
                torusCoordinateDerivative f j x =
                  2 * ρ x * torusCoordinateDerivative ρ j x * ξ x i +
                    ρ x ^ 2 * torusCoordinateDerivative (fun y => ξ y i) j x := by
              intro j
              dsimp [f]
              have hρsq : ContDiff ℝ 1
                  (torusCoordinateSliceLift (fun z => ρ z ^ 2) j (Fin.removeNth j x)) := by
                change ContDiff ℝ 1 (fun r =>
                  torusCoordinateSliceLift ρ j (Fin.removeNth j x) r ^ 2)
                exact (hρ j _).pow 2
              rw [torusCoordinateDerivative_mul
                (fun z => ρ z ^ 2) (fun z => ξ z i) j x]
              · rw [show torusCoordinateDerivative (fun z => ρ z ^ 2) j x =
                    2 * ρ x * torusCoordinateDerivative ρ j x by
                  have hpow : (fun z => ρ z ^ 2) = (fun z => ρ z * ρ z) := by
                    funext z
                    ring
                  rw [hpow]
                  rw [torusCoordinateDerivative_mul ρ ρ j x
                    (hρ j _) (hρ j _)]
                  ring]
              · exact hρsq
              · exact hξ i j _
            simp_rw [hderiv]
            simp only [Fin.sum_univ_three]
            ring
          change -((torusScalarTransport ξ f x +
            f x * torusCoordinateDivergence ξ x) * u x i) = _
          rw [htransport]
          dsimp [f]
          have hdivx := hdiv x
          rw [show torusScalarTransport ξ ρ x =
              -ρ x * torusCoordinateDivergence ξ x by linarith]
          ring
  have hleftComponent : ∀ i : Fin 3, Integrable (fun x : Torus3 =>
      ρ x ^ 2 * ξ x i * torusScalarTransport ξ (fun y => u y i) x) := by
    intro i
    unfold torusScalarTransport
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum Finset.univ fun j _hj => by
      simpa only [periodicFirstDerivative, mul_assoc] using hleft i j
  unfold periodicDirectionalStretchingDensity periodicDirectionProductionDensity
  rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun i _hi => hleftComponent i)]
  have hprodSum : Integrable (fun x : Torus3 =>
      ∑ i : Fin 3, ρ x ^ 2 * u x i *
        (ξ x i * torusCoordinateDivergence ξ x -
          torusScalarTransport ξ (fun y => ξ y i) x)) :=
    integrable_finsetSum Finset.univ fun i _hi => hproduction i
  rw [show (∫ x : Torus3, ρ x ^ 2 * ∑ i : Fin 3, u x i *
      (ξ x i * torusCoordinateDivergence ξ x -
        torusScalarTransport ξ (fun y => ξ y i) x)) =
      ∫ x : Torus3, ∑ i : Fin 3, ρ x ^ 2 * u x i *
      (ξ x i * torusCoordinateDivergence ξ x -
        torusScalarTransport ξ (fun y => ξ y i) x) by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change ρ x ^ 2 * (∑ i : Fin 3, u x i *
        (ξ x i * torusCoordinateDivergence ξ x -
          torusScalarTransport ξ (fun y => ξ y i) x)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun i _hi => hproduction i)]
  exact Finset.sum_congr rfl fun i _hi => hcomponent i
