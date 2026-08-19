import NSFormal.AnisotropicCriterion
import NSFormal.Budget

/-!
# Unoriented director-tensor anisotropic ledger

The rank-one tensor `P = e ⊗ e` contains exactly the information in a direction up to sign.
Writing the periodic anisotropic integration identity directly in terms of `P` removes
artificial sign interfaces: its error contains one derivative of `P`, rather than two expanded
derivatives of a chosen orientation `e`.  No tensor field or Navier--Stokes solution is inferred.
-/

open Filter Function MeasureTheory Set

noncomputable section

/-- A spatial field of real `3 × 3` director tensors. -/
abbrev DirectorTensorField := Torus3 → Matrix (Fin 3) (Fin 3) ℝ

/-- A positive trace-one mixture of squared strain eigenvalues dominates their minimum.  In a
strain eigenframe this is the finite-dimensional reason a positive director tensor retains the
middle-eigenvalue regularity criterion. -/
theorem convex_director_strain_dominates_minimum
    (weight eigenvalueSq : Fin 3 → ℝ) (minimum : ℝ)
    (hweight : ∀ i : Fin 3, 0 ≤ weight i)
    (htrace : (∑ i : Fin 3, weight i) = 1)
    (hminimum : ∀ i : Fin 3, minimum ≤ eigenvalueSq i) :
    minimum ≤ ∑ i : Fin 3, weight i * eigenvalueSq i := by
  calc
    minimum = ∑ i : Fin 3, weight i * minimum := by
      rw [← Finset.sum_mul, htrace, one_mul]
    _ ≤ ∑ i : Fin 3, weight i * eigenvalueSq i := by
      exact Finset.sum_le_sum fun i _hi =>
        mul_le_mul_of_nonneg_left (hminimum i) (hweight i)

/-- For three ordered trace-zero strain eigenvalues, the middle eigenvalue has the smallest
absolute value.  This is the scalar spectral fact behind the director criterion. -/
theorem middle_eigenvalue_sq_is_minimum
    (e₁ e₂ e₃ : ℝ) (h₁₂ : e₁ ≤ e₂) (h₂₃ : e₂ ≤ e₃)
    (htrace : e₁ + e₂ + e₃ = 0) :
    e₂ ^ 2 ≤ e₁ ^ 2 ∧ e₂ ^ 2 ≤ e₃ ^ 2 := by
  by_cases he₂ : 0 ≤ e₂
  · have he₃ : 0 ≤ e₃ := he₂.trans h₂₃
    have hleft : 0 ≤ (e₁ - e₂) * (e₁ + e₂) := by
      apply mul_nonneg_of_nonpos_of_nonpos
      · linarith
      · linarith
    have hright : 0 ≤ (e₃ - e₂) * (e₃ + e₂) := by
      exact mul_nonneg (sub_nonneg.2 h₂₃) (add_nonneg he₃ he₂)
    constructor <;> nlinarith
  · have he₂' : e₂ < 0 := lt_of_not_ge he₂
    have he₁ : e₁ < 0 := h₁₂.trans_lt he₂'
    have hleft : 0 ≤ (e₁ - e₂) * (e₁ + e₂) := by
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h₁₂)
        (add_nonpos he₁.le he₂'.le)
    have hright : 0 ≤ (e₃ - e₂) * (e₃ + e₂) := by
      apply mul_nonneg
      · exact sub_nonneg.2 h₂₃
      · linarith
    constructor <;> nlinarith

/-- Positive trace-one weights in a strain eigenframe control the squared middle eigenvalue. -/
theorem director_eigenframe_dominates_middle_sq
    (weight : Fin 3 → ℝ) (e₁ e₂ e₃ : ℝ)
    (hweight : ∀ i : Fin 3, 0 ≤ weight i)
    (hweightsum : (∑ i : Fin 3, weight i) = 1)
    (h₁₂ : e₁ ≤ e₂) (h₂₃ : e₂ ≤ e₃)
    (htrace : e₁ + e₂ + e₃ = 0) :
    e₂ ^ 2 ≤
      weight 0 * e₁ ^ 2 + weight 1 * e₂ ^ 2 + weight 2 * e₃ ^ 2 := by
  have hmiddle := middle_eigenvalue_sq_is_minimum
    e₁ e₂ e₃ h₁₂ h₂₃ htrace
  let eigenvalueSq : Fin 3 → ℝ := ![e₁ ^ 2, e₂ ^ 2, e₃ ^ 2]
  have hminimum : ∀ i : Fin 3, e₂ ^ 2 ≤ eigenvalueSq i := by
    intro i
    fin_cases i
    · exact hmiddle.1
    · exact le_rfl
    · exact hmiddle.2
  have hconvex := convex_director_strain_dominates_minimum
    weight eigenvalueSq (e₂ ^ 2) hweight hweightsum hminimum
  simpa [eigenvalueSq, Fin.sum_univ_three] using hconvex

/-- The isotropic trace-one director used to interpolate across low-vorticity regions. -/
def isotropicDirector : DirectorTensorField :=
  fun _ j k => if j = k then (3 : ℝ)⁻¹ else 0

/-- Globally nonsingular vorticity director.  It interpolates between the aligned rank-one
director at high amplitude and `I/3` at a vorticity zero. -/
def regularizedDirector (ω : Torus3 → Vec3) (c : ℝ) : DirectorTensorField :=
  fun x j k =>
    (ω x j * ω x k + if j = k then c ^ 2 / 3 else 0) /
      ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2)

/-- Algebraic differential of the regularized director at vorticity `w` in the increment
`h`.  This definition isolates the finite-dimensional estimate from the torus chain rule. -/
def regularizedDirectorDifferential
    (w h : Vec3) (c : ℝ) (j k : Fin 3) : ℝ :=
  let den := (∑ q : Fin 3, w q ^ 2) + c ^ 2
  ((h j * w k + w j * h k) * den -
      (w j * w k + if j = k then c ^ 2 / 3 else 0) *
        (2 * ∑ q : Fin 3, w q * h q)) / den ^ 2

/-- Cancellation-preserving form of the regularized-director differential.  It differentiates
`I / 3 + (w ⊗ w - |w|² I / 3) / (|w|² + c²)`, so every term visibly contains one
factor of `w`. -/
def regularizedDirectorTraceFreeDifferential
    (w h : Vec3) (c : ℝ) (j k : Fin 3) : ℝ :=
  let radiusSq := ∑ q : Fin 3, w q ^ 2
  let den := radiusSq + c ^ 2
  (((h j * w k + w j * h k) -
        if j = k then (2 / 3 : ℝ) * ∑ q : Fin 3, w q * h q else 0) * den -
      (w j * w k - if j = k then radiusSq / 3 else 0) *
        (2 * ∑ q : Fin 3, w q * h q)) / den ^ 2

/-- The quotient-rule differential equals its trace-free form exactly. -/
theorem regularizedDirectorDifferential_eq_traceFree
    (w h : Vec3) (c : ℝ) (j k : Fin 3) :
    regularizedDirectorDifferential w h c j k =
      regularizedDirectorTraceFreeDifferential w h c j k := by
  by_cases hjk : j = k
  · subst k
    simp [regularizedDirectorDifferential,
      regularizedDirectorTraceFreeDifferential]
    ring
  · simp [regularizedDirectorDifferential,
      regularizedDirectorTraceFreeDifferential, hjk]

/-- Three-dimensional coordinate `ℓ¹` is controlled by Euclidean square norm. -/
theorem vec3_l1_sq_le_three_sq_sum (w : Vec3) :
    (∑ q : Fin 3, |w q|) ^ 2 ≤ 3 * ∑ q : Fin 3, w q ^ 2 := by
  simp only [Fin.sum_univ_three]
  have h0 : |w 0| ^ 2 = w 0 ^ 2 := sq_abs (w 0)
  have h1 : |w 1| ^ 2 = w 1 ^ 2 := sq_abs (w 1)
  have h2 : |w 2| ^ 2 = w 2 ^ 2 := sq_abs (w 2)
  nlinarith [sq_nonneg (|w 0| - |w 1|),
    sq_nonneg (|w 0| - |w 2|), sq_nonneg (|w 1| - |w 2|)]

/-- The Euclidean coordinate square sum is bounded by coordinate `ℓ¹` squared. -/
theorem vec3_sq_sum_le_l1_sq (w : Vec3) :
    (∑ q : Fin 3, w q ^ 2) ≤ (∑ q : Fin 3, |w q|) ^ 2 := by
  simp only [Fin.sum_univ_three]
  have h0 : |w 0| ^ 2 = w 0 ^ 2 := sq_abs (w 0)
  have h1 : |w 1| ^ 2 = w 1 ^ 2 := sq_abs (w 1)
  have h2 : |w 2| ^ 2 = w 2 ^ 2 := sq_abs (w 2)
  nlinarith [mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 1)),
    mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 2)),
    mul_nonneg (abs_nonneg (w 1)) (abs_nonneg (w 2))]

/-- Scalar cancellation estimate used after rewriting the director differential in trace-free
form.  The constant is deliberately explicit; the important gain is the factor `R`, which
forces the differential to vanish at `w = 0`. -/
theorem abs_traceFree_quotient_differential_le
    (A T d D R H : ℝ) (hD : 0 < D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hA : |A| ≤ 3 * R * H) (hT : |T| ≤ 2 * R ^ 2)
    (hd : |d| ≤ R * H) (hR2D : R ^ 2 ≤ 3 * D) :
    |(A * D - T * (2 * d)) / D ^ 2| ≤ 15 * R * H / D := by
  have hRH : 0 ≤ R * H := mul_nonneg hR hH
  have hsecond : (2 * R ^ 2) * (2 * (R * H)) ≤ 12 * D * (R * H) := by
    have hprod := mul_le_mul_of_nonneg_right hR2D hRH
    nlinarith
  rw [abs_div, abs_pow, abs_of_pos hD]
  rw [div_le_iff₀ (sq_pos_of_pos hD)]
  calc
    |A * D - T * (2 * d)| ≤ |A * D| + |T * (2 * d)| := abs_sub _ _
    _ = |A| * D + |T| * (2 * |d|) := by
      rw [abs_mul, abs_mul]
      simp [abs_of_pos hD]
    _ ≤ (3 * R * H) * D + (2 * R ^ 2) * (2 * (R * H)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hA hD.le)
        (mul_le_mul hT (mul_le_mul_of_nonneg_left hd (by norm_num))
          (mul_nonneg (by norm_num) (abs_nonneg d))
          (mul_nonneg (by norm_num) (sq_nonneg R)))
    _ ≤ (3 * R * H) * D + 12 * D * (R * H) :=
      add_le_add le_rfl hsecond
    _ = (15 * R * H / D) * D ^ 2 := by
      field_simp [hD.ne']
      ring

/-- Cancellation-preserving componentwise director estimate.  Unlike the coarser square-root
bound, this estimate is exactly zero at a vorticity zero and behaves like
`|w| |∂w| / (|w|² + c²)`. -/
theorem abs_regularizedDirectorDifferential_le_sharp
    (w h : Vec3) (c : ℝ) (hc : c ≠ 0) (j k : Fin 3) :
    |regularizedDirectorDifferential w h c j k| ≤
      15 * (∑ q : Fin 3, |w q|) * (∑ q : Fin 3, |h q|) /
        ((∑ q : Fin 3, w q ^ 2) + c ^ 2) := by
  let radiusSq : ℝ := ∑ q : Fin 3, w q ^ 2
  let D : ℝ := radiusSq + c ^ 2
  let R : ℝ := ∑ q : Fin 3, |w q|
  let H : ℝ := ∑ q : Fin 3, |h q|
  let d : ℝ := ∑ q : Fin 3, w q * h q
  let A : ℝ := h j * w k + w j * h k -
    if j = k then (2 / 3 : ℝ) * d else 0
  let T : ℝ := w j * w k - if j = k then radiusSq / 3 else 0
  have hradiusSq : 0 ≤ radiusSq := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 < D := by
    exact add_pos_of_nonneg_of_pos hradiusSq (sq_pos_of_ne_zero hc)
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hw : ∀ q : Fin 3, |w q| ≤ R := by
    intro q
    exact Finset.single_le_sum (f := fun r : Fin 3 => |w r|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
  have hh : ∀ q : Fin 3, |h q| ≤ H := by
    intro q
    exact Finset.single_le_sum (f := fun r : Fin 3 => |h r|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
  have hd : |d| ≤ R * H := by
    calc
      |d| ≤ ∑ q : Fin 3, |w q * h q| := by
        dsimp [d]
        simpa using Finset.abs_sum_le_sum_abs
          (f := fun q : Fin 3 => w q * h q) Finset.univ
      _ = ∑ q : Fin 3, |w q| * |h q| := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact abs_mul _ _
      _ ≤ ∑ q : Fin 3, R * |h q| := by
        exact Finset.sum_le_sum fun q _hq =>
          mul_le_mul_of_nonneg_right (hw q) (abs_nonneg _)
      _ = R * H := by simp [H, Finset.mul_sum]
  have hbilinear : |h j * w k + w j * h k| ≤ 2 * R * H := by
    calc
      |h j * w k + w j * h k| ≤
          |h j * w k| + |w j * h k| := abs_add_le _ _
      _ = |h j| * |w k| + |w j| * |h k| := by rw [abs_mul, abs_mul]
      _ ≤ H * R + R * H := by
        exact add_le_add
          (mul_le_mul (hh j) (hw k) (abs_nonneg _) hH)
          (mul_le_mul (hw j) (hh k) (abs_nonneg _) hR)
      _ = 2 * R * H := by ring
  have hA : |A| ≤ 3 * R * H := by
    by_cases hjk : j = k
    · have htrace : |(2 / 3 : ℝ) * d| ≤ (2 / 3 : ℝ) * (R * H) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
        exact mul_le_mul_of_nonneg_left hd (by norm_num)
      dsimp [A]
      rw [if_pos hjk]
      calc
        |h j * w k + w j * h k - 2 / 3 * d| ≤
            |h j * w k + w j * h k| + |2 / 3 * d| := abs_sub _ _
        _ ≤ 2 * R * H + (2 / 3 : ℝ) * (R * H) :=
          add_le_add hbilinear htrace
        _ ≤ 3 * R * H := by nlinarith [mul_nonneg hR hH]
    · dsimp [A]
      rw [if_neg hjk, sub_zero]
      exact hbilinear.trans (by nlinarith [mul_nonneg hR hH])
  have hradiusR : radiusSq ≤ R ^ 2 := by
    simpa [radiusSq, R] using vec3_sq_sum_le_l1_sq w
  have hT : |T| ≤ 2 * R ^ 2 := by
    by_cases hjk : j = k
    · have hjradius : w j ^ 2 ≤ radiusSq := by
        dsimp [radiusSq]
        exact Finset.single_le_sum (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
      dsimp [T]
      rw [if_pos hjk]
      calc
        |w j * w k - radiusSq / 3| ≤
            |w j * w k| + |radiusSq / 3| := abs_sub _ _
        _ = w j ^ 2 + radiusSq / 3 := by
          rw [hjk, ← pow_two, abs_sq, abs_div,
            abs_of_nonneg hradiusSq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
        _ ≤ R ^ 2 + R ^ 2 / 3 := by
          exact add_le_add (hjradius.trans hradiusR)
            (div_le_div_of_nonneg_right hradiusR (by norm_num))
        _ ≤ 2 * R ^ 2 := by nlinarith [sq_nonneg R]
    · dsimp [T]
      rw [if_neg hjk, sub_zero, abs_mul]
      have hproduct : |w j| * |w k| ≤ R * R :=
        mul_le_mul (hw j) (hw k) (abs_nonneg _) hR
      simpa [pow_two] using hproduct.trans (by nlinarith [sq_nonneg R])
  have hR2D : R ^ 2 ≤ 3 * D := by
    have hthree := vec3_l1_sq_le_three_sq_sum w
    dsimp [R, radiusSq] at hthree ⊢
    dsimp [D]
    nlinarith [sq_nonneg c]
  rw [regularizedDirectorDifferential_eq_traceFree]
  simpa [regularizedDirectorTraceFreeDifferential, radiusSq, D, R, H, d, A, T]
    using abs_traceFree_quotient_differential_le
      A T d D R H hD hR hH hA hT hd hR2D

/-! The following fixed-dimensional identity has a deliberately generous elaboration depth:
expanding its nine rational terms is computationally routine but syntactically large. -/
set_option maxRecDepth 100000 in
/-- Exact rotationally invariant Frobenius square of the regularized-director differential.
The first summand is the angular derivative (the Gram determinant of `w,h`); the second is
the radial amplitude derivative. -/
theorem regularizedDirectorDifferential_frobenius_sq
    (w h : Vec3) (c : ℝ) (hc : c ≠ 0) :
    (∑ j : Fin 3, ∑ k : Fin 3,
      regularizedDirectorDifferential w h c j k ^ 2) =
      2 * (((∑ q : Fin 3, w q ^ 2) * (∑ q : Fin 3, h q ^ 2) -
          (∑ q : Fin 3, w q * h q) ^ 2) /
        ((∑ q : Fin 3, w q ^ 2) + c ^ 2) ^ 2) +
      (8 / 3 : ℝ) * c ^ 4 * (∑ q : Fin 3, w q * h q) ^ 2 /
        ((∑ q : Fin 3, w q ^ 2) + c ^ 2) ^ 4 := by
  have hD0 : (∑ q : Fin 3, w q ^ 2) + c ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_pos_of_ne_zero hc)).ne'
  simp [regularizedDirectorDifferential, Fin.sum_univ_three]
  field_simp [hD0]
  ring

/-- Finite-dimensional Cauchy--Schwarz for the Euclidean coordinate dot product. -/
theorem vec3_dot_sq_le_sq_sum_mul_sq_sum (w h : Vec3) :
    (∑ q : Fin 3, w q * h q) ^ 2 ≤
      (∑ q : Fin 3, w q ^ 2) * (∑ q : Fin 3, h q ^ 2) := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin 3)) (fun q => w q) (fun q => h q)

theorem vec3_eq_zero_of_sq_sum_eq_zero
    (w : Vec3) (hsum : (∑ q : Fin 3, w q ^ 2) = 0) : w = 0 := by
  ext q
  have hq : w q ^ 2 ≤ ∑ r : Fin 3, w r ^ 2 :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ q)
  rw [hsum] at hq
  simp only [PiLp.zero_apply]
  nlinarith [sq_nonneg (w q)]

/-- Directional part of an increment, weighted as `|w|² |∂ξ|²` away from `w = 0` and
defined to be zero at the origin. -/
def regularizedDirectorDirectionDerivativeSq (w h : Vec3) : ℝ :=
  ((∑ q : Fin 3, w q ^ 2) * (∑ q : Fin 3, h q ^ 2) -
    (∑ q : Fin 3, w q * h q) ^ 2) / (∑ q : Fin 3, w q ^ 2)

/-- Radial-amplitude part of an increment, equal to `|∂|w||²` away from `w = 0` and
defined to be zero at the origin. -/
def regularizedDirectorAmplitudeDerivativeSq (w h : Vec3) : ℝ :=
  (∑ q : Fin 3, w q * h q) ^ 2 / (∑ q : Fin 3, w q ^ 2)

theorem regularizedDirectorDirectionDerivativeSq_nonneg (w h : Vec3) :
    0 ≤ regularizedDirectorDirectionDerivativeSq w h := by
  unfold regularizedDirectorDirectionDerivativeSq
  exact div_nonneg
    (sub_nonneg.2 (vec3_dot_sq_le_sq_sum_mul_sq_sum w h))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem regularizedDirectorAmplitudeDerivativeSq_nonneg (w h : Vec3) :
    0 ≤ regularizedDirectorAmplitudeDerivativeSq w h := by
  unfold regularizedDirectorAmplitudeDerivativeSq
  exact div_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Recomposition of the angular Gram determinant, including the zero-vorticity case. -/
theorem regularizedDirectorDirectionDerivativeSq_mul_radiusSq
    (w h : Vec3) :
    regularizedDirectorDirectionDerivativeSq w h * (∑ q : Fin 3, w q ^ 2) =
      (∑ q : Fin 3, w q ^ 2) * (∑ q : Fin 3, h q ^ 2) -
        (∑ q : Fin 3, w q * h q) ^ 2 := by
  by_cases hr : (∑ q : Fin 3, w q ^ 2) = 0
  · have hw := vec3_eq_zero_of_sq_sum_eq_zero w hr
    subst w
    simp [regularizedDirectorDirectionDerivativeSq]
  · unfold regularizedDirectorDirectionDerivativeSq
    field_simp

/-- Recomposition of the radial square, including the zero-vorticity case. -/
theorem regularizedDirectorAmplitudeDerivativeSq_mul_radiusSq
    (w h : Vec3) :
    regularizedDirectorAmplitudeDerivativeSq w h * (∑ q : Fin 3, w q ^ 2) =
      (∑ q : Fin 3, w q * h q) ^ 2 := by
  by_cases hr : (∑ q : Fin 3, w q ^ 2) = 0
  · have hw := vec3_eq_zero_of_sq_sum_eq_zero w hr
    subst w
    simp [regularizedDirectorAmplitudeDerivativeSq]
  · unfold regularizedDirectorAmplitudeDerivativeSq
    field_simp

/-- Sharp-scaling Frobenius estimate obtained from the exact radial/angular identity.  Its
constant `14/3` replaces the coordinatewise square of `135`. -/
theorem regularizedDirectorDifferential_frobenius_sq_le
    (w h : Vec3) (c : ℝ) (hc : c ≠ 0) :
    (∑ j : Fin 3, ∑ k : Fin 3,
      regularizedDirectorDifferential w h c j k ^ 2) ≤
      (14 / 3 : ℝ) * (∑ q : Fin 3, w q ^ 2) *
        (∑ q : Fin 3, h q ^ 2) /
        ((∑ q : Fin 3, w q ^ 2) + c ^ 2) ^ 2 := by
  let r2 : ℝ := ∑ q : Fin 3, w q ^ 2
  let h2 : ℝ := ∑ q : Fin 3, h q ^ 2
  let d2 : ℝ := (∑ q : Fin 3, w q * h q) ^ 2
  let D : ℝ := r2 + c ^ 2
  have hr2 : 0 ≤ r2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hh2 : 0 ≤ h2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd2 : 0 ≤ d2 := sq_nonneg _
  have hdot : d2 ≤ r2 * h2 := by
    simpa [r2, h2, d2] using vec3_dot_sq_le_sq_sum_mul_sq_sum w h
  have hD : 0 < D := by
    exact add_pos_of_nonneg_of_pos hr2 (sq_pos_of_ne_zero hc)
  have hc2D : c ^ 2 ≤ D := by
    dsimp [D]
    linarith
  have hc4D2 : c ^ 4 ≤ D ^ 2 := by
    have hsquares := (sq_le_sq₀ (sq_nonneg c) hD.le).2 hc2D
    simpa [show c ^ 4 = (c ^ 2) ^ 2 by ring] using hsquares
  have hprod : c ^ 4 * d2 ≤ D ^ 2 * (r2 * h2) :=
    (mul_le_mul_of_nonneg_right hc4D2 hd2).trans
      (mul_le_mul_of_nonneg_left hdot (sq_nonneg D))
  have hangular : 0 ≤ r2 * h2 - d2 := sub_nonneg.2 hdot
  have hfirst :
      2 * ((r2 * h2 - d2) / D ^ 2) ≤
        2 * (r2 * h2 / D ^ 2) := by
    gcongr
    linarith
  have hsecond :
      (8 / 3 : ℝ) * c ^ 4 * d2 / D ^ 4 ≤
        (8 / 3 : ℝ) * (r2 * h2) / D ^ 2 := by
    have hD4 : 0 < D ^ 4 := pow_pos hD 4
    rw [div_le_iff₀ hD4]
    have heq : ((8 / 3 : ℝ) * (r2 * h2) / D ^ 2) * D ^ 4 =
        (8 / 3 : ℝ) * (D ^ 2 * (r2 * h2)) := by
      field_simp [hD.ne']
    rw [heq]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 8 / 3)
  rw [regularizedDirectorDifferential_frobenius_sq w h c hc]
  dsimp [r2, h2, d2, D] at hfirst hsecond ⊢
  calc
    2 * (((∑ q : Fin 3, w q ^ 2) * (∑ q : Fin 3, h q ^ 2) -
          (∑ q : Fin 3, w q * h q) ^ 2) /
        ((∑ q : Fin 3, w q ^ 2) + c ^ 2) ^ 2) +
        (8 / 3 : ℝ) * c ^ 4 * (∑ q : Fin 3, w q * h q) ^ 2 /
          ((∑ q : Fin 3, w q ^ 2) + c ^ 2) ^ 4 ≤
        2 * (((∑ q : Fin 3, w q ^ 2) * (∑ q : Fin 3, h q ^ 2)) /
          ((∑ q : Fin 3, w q ^ 2) + c ^ 2) ^ 2) +
        (8 / 3 : ℝ) *
          ((∑ q : Fin 3, w q ^ 2) * (∑ q : Fin 3, h q ^ 2)) /
          ((∑ q : Fin 3, w q ^ 2) + c ^ 2) ^ 2 :=
      add_le_add hfirst hsecond
    _ = (14 / 3 : ℝ) * (∑ q : Fin 3, w q ^ 2) *
        (∑ q : Fin 3, h q ^ 2) /
        ((∑ q : Fin 3, w q ^ 2) + c ^ 2) ^ 2 := by ring

/-- Scalar estimate underlying the regularized-director derivative bound. -/
theorem abs_regularized_quotient_differential_le
    (a n d D H s : ℝ) (hD : 0 < D) (hs : 0 < s)
    (hsq : s ^ 2 = D) (ha : |a| ≤ 2 * H * s)
    (hn : |n| ≤ D) (hd : |d| ≤ s * H) :
    |(a * D - n * (2 * d)) / D ^ 2| ≤ 4 * H / s := by
  rw [abs_div, abs_pow, abs_of_pos hD]
  rw [div_le_iff₀ (sq_pos_of_pos hD)]
  calc
    |a * D - n * (2 * d)| ≤ |a * D| + |n * (2 * d)| := abs_sub _ _
    _ = |a| * D + |n| * (2 * |d|) := by
      rw [abs_mul, abs_mul]
      simp [abs_of_pos hD]
    _ ≤ (2 * H * s) * D + D * (2 * (s * H)) := by
      have hd2 : 2 * |d| ≤ 2 * (s * H) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      exact add_le_add
        (mul_le_mul_of_nonneg_right ha hD.le)
        (mul_le_mul hn hd2 (mul_nonneg (by norm_num) (abs_nonneg d)) hD.le)
    _ = (4 * H / s) * D ^ 2 := by
      rw [← hsq]
      field_simp [hs.ne']
      ring

/-- Every numerator entry in the regularized director is bounded by its positive
denominator. -/
theorem abs_regularizedDirector_numerator_le
    (w : Vec3) (c : ℝ) (j k : Fin 3) :
    |w j * w k + if j = k then c ^ 2 / 3 else 0| ≤
      (∑ q : Fin 3, w q ^ 2) + c ^ 2 := by
  by_cases hjk : j = k
  · subst k
    have hj : w j ^ 2 ≤ ∑ q : Fin 3, w q ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    rw [if_pos rfl, abs_of_nonneg]
    · nlinarith [sq_nonneg c]
    · nlinarith [sq_nonneg (w j), sq_nonneg c]
  · have hpair : w j ^ 2 + w k ^ 2 ≤ ∑ q : Fin 3, w q ^ 2 := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun q : Fin 3 => w q ^ 2)
        (s := {j, k}) (t := Finset.univ) (by simp)
        (fun _ _ _ => sq_nonneg _)
      rwa [Finset.sum_pair hjk] at h
    rw [if_neg hjk, add_zero, abs_le]
    constructor <;>
      nlinarith [sq_nonneg (w j - w k), sq_nonneg (w j + w k), sq_nonneg c]

/-- Sharp componentwise scaling of the regularized-director differential.  The coordinate
`ℓ¹` norm of the increment is used so this theorem can feed the concrete periodic ledger. -/
theorem abs_regularizedDirectorDifferential_le
    (w h : Vec3) (c : ℝ) (hc : c ≠ 0) (j k : Fin 3) :
    |regularizedDirectorDifferential w h c j k| ≤
      4 * (∑ q : Fin 3, |h q|) /
        Real.sqrt ((∑ q : Fin 3, w q ^ 2) + c ^ 2) := by
  let D : ℝ := (∑ q : Fin 3, w q ^ 2) + c ^ 2
  let H : ℝ := ∑ q : Fin 3, |h q|
  let s : ℝ := Real.sqrt D
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_pos_of_ne_zero hc)
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hs : 0 < s := Real.sqrt_pos.2 hD
  have hsq : s ^ 2 = D := Real.sq_sqrt hD.le
  have hw : ∀ q : Fin 3, |w q| ≤ s := by
    intro q
    have hqsum : w q ^ 2 ≤ ∑ r : Fin 3, w r ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ q)
    have hqD : w q ^ 2 ≤ D := by
      dsimp [D]
      nlinarith [sq_nonneg c]
    have hsq' : w q ^ 2 ≤ s ^ 2 := by rwa [hsq]
    have habs := (sq_le_sq).1 hsq'
    simpa [abs_of_pos hs] using habs
  have hh : ∀ q : Fin 3, |h q| ≤ H := by
    intro q
    exact Finset.single_le_sum (f := fun r : Fin 3 => |h r|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
  have hdot : |∑ q : Fin 3, w q * h q| ≤ s * H := by
    calc
      |∑ q : Fin 3, w q * h q| ≤ ∑ q : Fin 3, |w q * h q| := by
        simpa using Finset.abs_sum_le_sum_abs
          (f := fun q : Fin 3 => w q * h q) Finset.univ
      _ = ∑ q : Fin 3, |w q| * |h q| := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact abs_mul _ _
      _ ≤ ∑ q : Fin 3, s * |h q| := by
        exact Finset.sum_le_sum fun q _hq =>
          mul_le_mul_of_nonneg_right (hw q) (abs_nonneg _)
      _ = s * H := by simp [H, Finset.mul_sum]
  have ha : |h j * w k + w j * h k| ≤ 2 * H * s := by
    calc
      |h j * w k + w j * h k| ≤
          |h j * w k| + |w j * h k| := abs_add_le _ _
      _ = |h j| * |w k| + |w j| * |h k| := by rw [abs_mul, abs_mul]
      _ ≤ H * s + s * H := by
        exact add_le_add
          (mul_le_mul (hh j) (hw k) (abs_nonneg _) hH)
          (mul_le_mul (hw j) (hh k) (abs_nonneg _) hs.le)
      _ = 2 * H * s := by ring
  have hn : |w j * w k + if j = k then c ^ 2 / 3 else 0| ≤ D := by
    exact abs_regularizedDirector_numerator_le w c j k
  simpa [regularizedDirectorDifferential, D, H, s] using
    abs_regularized_quotient_differential_le
      (h j * w k + w j * h k)
      (w j * w k + if j = k then c ^ 2 / 3 else 0)
      (∑ q : Fin 3, w q * h q) D H s hD hs hsq ha hn hdot

/-- Derivative of the squared coordinate norm plus a constant. -/
theorem torusCoordinateDerivative_vorticityNormSq_add_const
    (ω : Torus3 → Vec3) (c : ℝ) (i : Fin 3) (x : Torus3)
    (hω : ∀ q : Fin 3,
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun z => ω z q) i (Fin.removeNth i x))) :
    torusCoordinateDerivative
        (fun z => (∑ q : Fin 3, ω z q ^ 2) + c ^ 2) i x =
      2 * ∑ q : Fin 3, ω x q * periodicFirstDerivative ω i q x := by
  simp only [Fin.sum_univ_three, pow_two]
  rw [torusCoordinateDerivative_add]
  · rw [torusCoordinateDerivative_add]
    · rw [torusCoordinateDerivative_add]
      · rw [torusCoordinateDerivative_mul _ _ i x (hω 0) (hω 0)]
        rw [torusCoordinateDerivative_mul _ _ i x (hω 1) (hω 1)]
        rw [torusCoordinateDerivative_mul _ _ i x (hω 2) (hω 2)]
        simp only [periodicFirstDerivative, torusCoordinateDerivative_const]
        ring
      · exact (hω 0).mul (hω 0)
      · exact (hω 1).mul (hω 1)
    · exact (hω 0).mul (hω 0) |>.add ((hω 1).mul (hω 1))
    · exact (hω 2).mul (hω 2)
  · exact ((hω 0).mul (hω 0) |>.add ((hω 1).mul (hω 1))).add
      ((hω 2).mul (hω 2))
  · exact contDiff_const

theorem isotropicDirector_symmetric (x : Torus3) (j k : Fin 3) :
    isotropicDirector x j k = isotropicDirector x k j := by
  by_cases hjk : j = k
  · simp [isotropicDirector, hjk]
  · have hkj : k ≠ j := fun h => hjk h.symm
    simp [isotropicDirector, hjk, hkj]

theorem isotropicDirector_trace_eq_one (x : Torus3) :
    (∑ j : Fin 3, isotropicDirector x j j) = 1 := by
  norm_num [isotropicDirector, Fin.sum_univ_three]

theorem regularizedDirector_symmetric
    (ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) (j k : Fin 3) :
    regularizedDirector ω c x j k = regularizedDirector ω c x k j := by
  by_cases hjk : j = k
  · simp [regularizedDirector, hjk]
  · have hkj : k ≠ j := fun h => hjk h.symm
    simp [regularizedDirector, hjk, hkj, mul_comm]

theorem regularizedDirector_trace_eq_one
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    (∑ j : Fin 3, regularizedDirector ω c x j j) = 1 := by
  have hsum0 : 0 ≤ ∑ q : Fin 3, ω x q ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hden : (∑ q : Fin 3, ω x q ^ 2) + c ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos hsum0 hc2).ne'
  simp [regularizedDirector, Fin.sum_univ_three]
  field_simp
  ring

/-- Exact quadratic form of the regularized director. -/
theorem regularizedDirector_quadratic_eq
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) (v : Vec3) :
    (∑ j : Fin 3, ∑ k : Fin 3,
      regularizedDirector ω c x j k * v j * v k) =
      ((∑ j : Fin 3, ω x j * v j) ^ 2 +
        c ^ 2 / 3 * ∑ j : Fin 3, v j ^ 2) /
        ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) := by
  have hden : (∑ q : Fin 3, ω x q ^ 2) + c ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_pos_of_ne_zero hc)).ne'
  simp [regularizedDirector, Fin.sum_univ_three]
  field_simp [hden]
  ring

/-- The regularized director is positive semidefinite, expressed directly through its
quadratic form rather than an abstract matrix typeclass. -/
theorem regularizedDirector_quadratic_nonneg
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) (v : Vec3) :
    0 ≤ ∑ j : Fin 3, ∑ k : Fin 3,
      regularizedDirector ω c x j k * v j * v k := by
  rw [regularizedDirector_quadratic_eq ω c hc x v]
  apply div_nonneg
  · exact add_nonneg (sq_nonneg _)
      (mul_nonneg (div_nonneg (sq_nonneg c) (by norm_num))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  · exact add_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg c)

/-- Coordinate derivative `∂ᵢ Pⱼₖ` of a director tensor. -/
def periodicDirectorDerivative
    (P : DirectorTensorField) (i j k : Fin 3) (x : Torus3) : ℝ :=
  torusCoordinateDerivative (fun y => P y j k) i x

/-- Frobenius square of the periodic velocity gradient. -/
def periodicGradientFrobeniusSq (u : Torus3 → Vec3) (x : Torus3) : ℝ :=
  ∑ k : Fin 3, ∑ i : Fin 3, periodicFirstDerivative u k i x ^ 2

/-- Frobenius square of the full director-tensor gradient. -/
def periodicDirectorGradientFrobeniusSq
    (P : DirectorTensorField) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    periodicDirectorDerivative P i j k x ^ 2

/-- Coordinate-free magnitude of the tensor error density. -/
def periodicDirectorFrobeniusDebitDensity
    (u : Torus3 → Vec3) (P : DirectorTensorField) (x : Torus3) : ℝ :=
  ‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) *
    Real.sqrt (periodicDirectorGradientFrobeniusSq P x)

theorem periodicGradientFrobeniusSq_nonneg
    (u : Torus3 → Vec3) (x : Torus3) :
    0 ≤ periodicGradientFrobeniusSq u x := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem periodicGradientFrobeniusSq_centeredVelocity
    (u : Torus3 → Vec3) (a : Vec3) (x : Torus3) :
    periodicGradientFrobeniusSq (centeredVelocity u a) x =
      periodicGradientFrobeniusSq u x := by
  unfold periodicGradientFrobeniusSq
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [periodicFirstDerivative_centeredVelocity]

theorem periodicDirectorGradientFrobeniusSq_nonneg
    (P : DirectorTensorField) (x : Torus3) :
    0 ≤ periodicDirectorGradientFrobeniusSq P x := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem periodicDirectorFrobeniusDebitDensity_nonneg
    (u : Torus3 → Vec3) (P : DirectorTensorField) (x : Torus3) :
    0 ≤ periodicDirectorFrobeniusDebitDensity u P x := by
  unfold periodicDirectorFrobeniusDebitDensity
  positivity

/-- Exact torus-coordinate chain rule for the nonsingular director. -/
theorem periodicDirectorDerivative_regularizedDirector
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (i j k : Fin 3) (x : Torus3)
    (hω : ∀ q : Fin 3,
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun z => ω z q) i (Fin.removeNth i x))) :
    periodicDirectorDerivative (regularizedDirector ω c) i j k x =
      regularizedDirectorDifferential (ω x)
        (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x) c j k := by
  let numerator : Torus3 → ℝ := fun z =>
    ω z j * ω z k + if j = k then c ^ 2 / 3 else 0
  let denominator : Torus3 → ℝ := fun z =>
    (∑ q : Fin 3, ω z q ^ 2) + c ^ 2
  have hdenPos : 0 < denominator x := by
    dsimp [denominator]
    exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_pos_of_ne_zero hc)
  have hnum : ContDiff ℝ 1
      (torusCoordinateSliceLift numerator i (Fin.removeNth i x)) := by
    exact (hω j).mul (hω k) |>.add contDiff_const
  have hden : ContDiff ℝ 1
      (torusCoordinateSliceLift denominator i (Fin.removeNth i x)) := by
    simp only [denominator, Fin.sum_univ_three, pow_two]
    exact (((hω 0).mul (hω 0) |>.add ((hω 1).mul (hω 1))).add
      ((hω 2).mul (hω 2))).add contDiff_const
  have hnumDerivative : torusCoordinateDerivative numerator i x =
      periodicFirstDerivative ω i j x * ω x k +
        ω x j * periodicFirstDerivative ω i k x := by
    dsimp [numerator]
    have hprod : ContDiff ℝ 1
        (torusCoordinateSliceLift (fun z => ω z j * ω z k)
          i (Fin.removeNth i x)) := (hω j).mul (hω k)
    rw [torusCoordinateDerivative_add
      (fun z => ω z j * ω z k)
      (fun _ : Torus3 => if j = k then c ^ 2 / 3 else 0)
      i x hprod contDiff_const]
    rw [torusCoordinateDerivative_mul _ _ i x (hω j) (hω k)]
    simp [periodicFirstDerivative]
  have hdenDerivative : torusCoordinateDerivative denominator i x =
      2 * ∑ q : Fin 3, ω x q * periodicFirstDerivative ω i q x := by
    exact torusCoordinateDerivative_vorticityNormSq_add_const ω c i x hω
  change torusCoordinateDerivative (fun z => numerator z / denominator z) i x = _
  rw [torusCoordinateDerivative_div numerator denominator i x hnum hden hdenPos.ne']
  rw [hnumDerivative, hdenDerivative]
  dsimp [regularizedDirectorDifferential, numerator, denominator]

/-- Squared angular part of one vorticity derivative.  Algebraically this is the Gram
determinant `|ω|² |∂ᵢω|² - (ω·∂ᵢω)²`. -/
def periodicVorticityAngularDerivativeSq
    (ω : Torus3 → Vec3) (i : Fin 3) (x : Torus3) : ℝ :=
  (∑ q : Fin 3, ω x q ^ 2) *
      (∑ q : Fin 3, periodicFirstDerivative ω i q x ^ 2) -
    (∑ q : Fin 3, ω x q * periodicFirstDerivative ω i q x) ^ 2

/-- Squared radial-amplitude part of one vorticity derivative. -/
def periodicVorticityRadialDerivativeSq
    (ω : Torus3 → Vec3) (i : Fin 3) (x : Torus3) : ℝ :=
  (∑ q : Fin 3, ω x q * periodicFirstDerivative ω i q x) ^ 2

/-- Direction-palinstrophy density, defined without choosing a direction at a zero. -/
def periodicVorticityDirectionDissipationSq
    (ω : Torus3 → Vec3) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, regularizedDirectorDirectionDerivativeSq (ω x)
    (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x)

/-- Scalar-amplitude palinstrophy density, also defined harmlessly at a zero. -/
def periodicVorticityAmplitudeDissipationSq
    (ω : Torus3 → Vec3) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, regularizedDirectorAmplitudeDerivativeSq (ω x)
    (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x)

theorem periodicVorticityDirectionDissipationSq_nonneg
    (ω : Torus3 → Vec3) (x : Torus3) :
    0 ≤ periodicVorticityDirectionDissipationSq ω x := by
  exact Finset.sum_nonneg fun _ _ =>
    regularizedDirectorDirectionDerivativeSq_nonneg _ _

theorem periodicVorticityAmplitudeDissipationSq_nonneg
    (ω : Torus3 → Vec3) (x : Torus3) :
    0 ≤ periodicVorticityAmplitudeDissipationSq ω x := by
  exact Finset.sum_nonneg fun _ _ =>
    regularizedDirectorAmplitudeDerivativeSq_nonneg _ _

/-- Exact periodic Frobenius decomposition of the regularized-director gradient into angular
and radial-amplitude pieces.  At large vorticity only the angular piece has inverse-vorticity
scaling; the radial piece decays three additional powers. -/
theorem periodicDirectorGradientFrobeniusSq_regularizedDirector
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y)) :
    periodicDirectorGradientFrobeniusSq (regularizedDirector ω c) x =
      2 * (∑ i : Fin 3, periodicVorticityAngularDerivativeSq ω i x) /
          ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 +
        (8 / 3 : ℝ) * c ^ 4 *
          (∑ i : Fin 3, periodicVorticityRadialDerivativeSq ω i x) /
          ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4 := by
  have hcomponent : ∀ i : Fin 3,
      (∑ j : Fin 3, ∑ k : Fin 3,
        periodicDirectorDerivative (regularizedDirector ω c) i j k x ^ 2) =
        2 * periodicVorticityAngularDerivativeSq ω i x /
            ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 +
          (8 / 3 : ℝ) * c ^ 4 *
            periodicVorticityRadialDerivativeSq ω i x /
            ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4 := by
    intro i
    calc
      (∑ j : Fin 3, ∑ k : Fin 3,
          periodicDirectorDerivative (regularizedDirector ω c) i j k x ^ 2) =
          ∑ j : Fin 3, ∑ k : Fin 3,
            regularizedDirectorDifferential (ω x)
              (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x) c j k ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro k _hk
        rw [periodicDirectorDerivative_regularizedDirector ω c hc i j k x
          (fun q => hω i q (Fin.removeNth i x))]
      _ = 2 * periodicVorticityAngularDerivativeSq ω i x /
            ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 +
          (8 / 3 : ℝ) * c ^ 4 *
            periodicVorticityRadialDerivativeSq ω i x /
            ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4 := by
        have hid := regularizedDirectorDifferential_frobenius_sq
          (ω x) (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x) c hc
        simp only [periodicVorticityAngularDerivativeSq,
          periodicVorticityRadialDerivativeSq] at ⊢
        convert hid using 1 <;> ring
  unfold periodicDirectorGradientFrobeniusSq
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        periodicDirectorDerivative (regularizedDirector ω c) i j k x ^ 2) =
        ∑ i : Fin 3,
          (2 * periodicVorticityAngularDerivativeSq ω i x /
              ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 +
            (8 / 3 : ℝ) * c ^ 4 *
              periodicVorticityRadialDerivativeSq ω i x /
              ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4) :=
      Finset.sum_congr rfl fun i _hi => hcomponent i
    _ = 2 * (∑ i : Fin 3, periodicVorticityAngularDerivativeSq ω i x) /
          ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 +
        (8 / 3 : ℝ) * c ^ 4 *
          (∑ i : Fin 3, periodicVorticityRadialDerivativeSq ω i x) /
          ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4 := by
      simp only [Fin.sum_univ_three]
      ring

/-- Exact periodic decomposition in normalized direction- and amplitude-dissipation variables.
It remains valid on the vorticity zero set without selecting `ξ`. -/
theorem periodicDirectorGradientFrobeniusSq_regularizedDirector_direction_amplitude
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y)) :
    periodicDirectorGradientFrobeniusSq (regularizedDirector ω c) x =
      2 * periodicVorticityDirectionDissipationSq ω x *
          (∑ q : Fin 3, ω x q ^ 2) /
          ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 +
        (8 / 3 : ℝ) * periodicVorticityAmplitudeDissipationSq ω x *
          (∑ q : Fin 3, ω x q ^ 2) * c ^ 4 /
          ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4 := by
  have hexact := periodicDirectorGradientFrobeniusSq_regularizedDirector
    ω c hc x hω
  have hdirection :
      periodicVorticityDirectionDissipationSq ω x *
          (∑ q : Fin 3, ω x q ^ 2) =
        ∑ i : Fin 3, periodicVorticityAngularDerivativeSq ω i x := by
    unfold periodicVorticityDirectionDissipationSq
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    simpa [periodicVorticityAngularDerivativeSq] using
      regularizedDirectorDirectionDerivativeSq_mul_radiusSq (ω x)
        (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x)
  have hamplitude :
      periodicVorticityAmplitudeDissipationSq ω x *
          (∑ q : Fin 3, ω x q ^ 2) =
        ∑ i : Fin 3, periodicVorticityRadialDerivativeSq ω i x := by
    unfold periodicVorticityAmplitudeDissipationSq
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    simpa [periodicVorticityRadialDerivativeSq] using
      regularizedDirectorAmplitudeDerivativeSq_mul_radiusSq (ω x)
        (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x)
  rw [← hdirection, ← hamplitude] at hexact
  convert hexact using 1 <;> ring

/-- Periodic Frobenius estimate with the cancellation-preserving Euclidean quotient. -/
theorem periodicDirectorGradientFrobeniusSq_regularizedDirector_le
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y)) :
    periodicDirectorGradientFrobeniusSq (regularizedDirector ω c) x ≤
      (14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) *
        periodicGradientFrobeniusSq ω x /
        ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 := by
  have hcomponent : ∀ i : Fin 3,
      (∑ j : Fin 3, ∑ k : Fin 3,
        periodicDirectorDerivative (regularizedDirector ω c) i j k x ^ 2) ≤
        (14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) *
          (∑ q : Fin 3, periodicFirstDerivative ω i q x ^ 2) /
          ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 := by
    intro i
    calc
      (∑ j : Fin 3, ∑ k : Fin 3,
          periodicDirectorDerivative (regularizedDirector ω c) i j k x ^ 2) =
          ∑ j : Fin 3, ∑ k : Fin 3,
            regularizedDirectorDifferential (ω x)
              (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x) c j k ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro k _hk
        rw [periodicDirectorDerivative_regularizedDirector ω c hc i j k x
          (fun q => hω i q (Fin.removeNth i x))]
      _ ≤ (14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) *
          (∑ q : Fin 3, periodicFirstDerivative ω i q x ^ 2) /
          ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 := by
        simpa using regularizedDirectorDifferential_frobenius_sq_le
          (ω x) (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x) c hc
  unfold periodicDirectorGradientFrobeniusSq periodicGradientFrobeniusSq
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        periodicDirectorDerivative (regularizedDirector ω c) i j k x ^ 2) ≤
        ∑ i : Fin 3, (14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) *
          (∑ q : Fin 3, periodicFirstDerivative ω i q x ^ 2) /
          ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 :=
      Finset.sum_le_sum fun i _hi => hcomponent i
    _ = (14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) *
        (∑ i : Fin 3, ∑ q : Fin 3, periodicFirstDerivative ω i q x ^ 2) /
        ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring

/-- Componentwise concrete derivative bound for the regularized vorticity director. -/
theorem abs_periodicDirectorDerivative_regularizedDirector_le
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (i j k : Fin 3) (x : Torus3)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y)) :
    |periodicDirectorDerivative (regularizedDirector ω c) i j k x| ≤
      4 * (∑ q : Fin 3, |periodicFirstDerivative ω i q x|) /
        Real.sqrt ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) := by
  rw [periodicDirectorDerivative_regularizedDirector ω c hc i j k x
    (fun q => hω i q (Fin.removeNth i x))]
  simpa using abs_regularizedDirectorDifferential_le
    (ω x) (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x) c hc j k

/-- Periodic componentwise form of the cancellation-preserving director estimate. -/
theorem abs_periodicDirectorDerivative_regularizedDirector_le_sharp
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (i j k : Fin 3) (x : Torus3)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y)) :
    |periodicDirectorDerivative (regularizedDirector ω c) i j k x| ≤
      15 * (∑ q : Fin 3, |ω x q|) *
          (∑ q : Fin 3, |periodicFirstDerivative ω i q x|) /
        ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) := by
  rw [periodicDirectorDerivative_regularizedDirector ω c hc i j k x
    (fun q => hω i q (Fin.removeNth i x))]
  simpa using abs_regularizedDirectorDifferential_le_sharp
    (ω x) (WithLp.toLp 2 fun q => periodicFirstDerivative ω i q x) c hc j k

/-- Coordinate `ℓ¹` envelope of the director-tensor derivative. -/
def periodicDirectorGradientL1 (P : DirectorTensorField) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    |periodicDirectorDerivative P i j k x|

/-- The full concrete tensor gradient has the critical nonsingular scaling
`|∇P_c| ≲ |∇ω| / sqrt(|ω|²+c²)`.  The explicit constant `36` comes from the nine
tensor entries in the coordinate `ℓ¹` norm. -/
theorem periodicDirectorGradientL1_regularizedDirector_le
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y)) :
    periodicDirectorGradientL1 (regularizedDirector ω c) x ≤
      36 * periodicGradientL1 ω x /
        Real.sqrt ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) := by
  unfold periodicDirectorGradientL1
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        |periodicDirectorDerivative (regularizedDirector ω c) i j k x|) ≤
        ∑ i : Fin 3, ∑ _j : Fin 3, ∑ _k : Fin 3,
          4 * (∑ q : Fin 3, |periodicFirstDerivative ω i q x|) /
            Real.sqrt ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) := by
      exact Finset.sum_le_sum fun i _hi =>
        Finset.sum_le_sum fun j _hj =>
          Finset.sum_le_sum fun k _hk =>
            abs_periodicDirectorDerivative_regularizedDirector_le
              ω c hc i j k x hω
    _ = 36 * periodicGradientL1 ω x /
        Real.sqrt ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) := by
      simp only [periodicGradientL1, Fin.sum_univ_three]
      ring

/-- Full cancellation-preserving tensor-gradient estimate.  The factor
`|ω|₁ / (|ω|² + c²)` is zero on the vorticity zero set; the constant `135` is nine
tensor entries times the component constant `15`. -/
theorem periodicDirectorGradientL1_regularizedDirector_le_sharp
    (ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y)) :
    periodicDirectorGradientL1 (regularizedDirector ω c) x ≤
      135 * (∑ q : Fin 3, |ω x q|) * periodicGradientL1 ω x /
        ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) := by
  unfold periodicDirectorGradientL1
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        |periodicDirectorDerivative (regularizedDirector ω c) i j k x|) ≤
        ∑ i : Fin 3, ∑ _j : Fin 3, ∑ _k : Fin 3,
          15 * (∑ q : Fin 3, |ω x q|) *
              (∑ q : Fin 3, |periodicFirstDerivative ω i q x|) /
            ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) := by
      exact Finset.sum_le_sum fun i _hi =>
        Finset.sum_le_sum fun j _hj =>
          Finset.sum_le_sum fun k _hk =>
            abs_periodicDirectorDerivative_regularizedDirector_le_sharp
              ω c hc i j k x hω
    _ = 135 * (∑ q : Fin 3, |ω x q|) * periodicGradientL1 ω x /
        ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) := by
      simp only [periodicGradientL1, Fin.sum_univ_three]
      ring

/-- The second `L²` factor in the regularized-director Cauchy ledger. -/
def periodicRegularizedDirectorCauchyFactor
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  36 * (‖u x‖ * periodicGradientL1 u x) /
    Real.sqrt ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2)

/-- Nonsingular quotient density left by the regularized director. -/
def periodicRegularizedDirectorQuotientDensity
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  ‖u x‖ ^ 2 * periodicGradientL1 u x ^ 2 /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2)

/-- Second Cauchy factor retaining the trace-free cancellation in the director derivative. -/
def periodicRegularizedDirectorSharpCauchyFactor
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  135 * (‖u x‖ * periodicGradientL1 u x * (∑ q : Fin 3, |ω x q|)) /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2)

/-- Cancellation-preserving quotient density.  Its vorticity factor is
`|ω|₁² / (|ω|² + c²)²`, so it vanishes on the zero set instead of assigning the
worst regularization weight there. -/
def periodicRegularizedDirectorSharpQuotientDensity
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  ‖u x‖ ^ 2 * periodicGradientL1 u x ^ 2 *
      (∑ q : Fin 3, |ω x q|) ^ 2 /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2

/-- Euclidean/Frobenius form of the cancellation-preserving quotient. -/
def periodicRegularizedDirectorFrobeniusQuotientDensity
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  ‖u x‖ ^ 2 * periodicGradientFrobeniusSq u x *
      (∑ q : Fin 3, ω x q ^ 2) /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2

/-- Radial-amplitude quotient left by the second exact term of the director differential. -/
def periodicRegularizedDirectorRadialQuotientDensity
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  ‖u x‖ ^ 2 * periodicGradientFrobeniusSq u x *
      (∑ q : Fin 3, ω x q ^ 2) * c ^ 4 /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4

/-- Angular Cauchy factor in the exact direction/amplitude split. -/
def periodicRegularizedDirectorDirectionCauchyFactor
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  ‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) *
    Real.sqrt (2 * (∑ q : Fin 3, ω x q ^ 2) /
      ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2)

/-- Radial-amplitude Cauchy factor in the exact direction/amplitude split. -/
def periodicRegularizedDirectorAmplitudeCauchyFactor
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  ‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) *
    Real.sqrt ((8 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) * c ^ 4 /
      ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4)

/-- Spatial variance weight in the Frobenius sharp quotient. -/
def periodicRegularizedDirectorFrobeniusQuotientWeight
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  periodicGradientFrobeniusSq u x * (∑ q : Fin 3, ω x q ^ 2) /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2

/-- Generic weighted optimal constant frame for a periodic vector field. -/
def periodicWeightedOptimalFrame
    (weight : Torus3 → ℝ) (u : Torus3 → Vec3) : Vec3 :=
  WithLp.toLp 2 fun j =>
    (∫ x : Torus3, weight x * u x j) / (∫ x : Torus3, weight x)

/-- Quotient-optimal frame for the Frobenius sharp director ledger. -/
def periodicRegularizedDirectorFrobeniusOptimalFrame
    (u ω : Torus3 → Vec3) (c : ℝ) : Vec3 :=
  periodicWeightedOptimalFrame
    (periodicRegularizedDirectorFrobeniusQuotientWeight u ω c) u

/-- Exact second Cauchy factor for the Frobenius director ledger. -/
def periodicRegularizedDirectorFrobeniusCauchyFactor
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  ‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) *
    Real.sqrt ((14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) /
      ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2)

/-- Spatial weight whose variance is the regularized quotient. -/
def periodicRegularizedQuotientWeight
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) : ℝ :=
  periodicGradientL1 u x ^ 2 /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2)

/-- Quotient-weighted optimal spatially constant Galilean frame. -/
def periodicRegularizedOptimalFrame
    (u ω : Torus3 → Vec3) (c : ℝ) : Vec3 :=
  WithLp.toLp 2 fun j =>
    (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x * u x j) /
      (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x)

theorem periodicRegularizedQuotientWeight_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    0 ≤ periodicRegularizedQuotientWeight u ω c x := by
  unfold periodicRegularizedQuotientWeight
  apply div_nonneg (sq_nonneg _)
  exact (add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_pos_of_ne_zero hc)).le

theorem periodicRegularizedDirectorQuotientDensity_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    0 ≤ periodicRegularizedDirectorQuotientDensity u ω c x := by
  unfold periodicRegularizedDirectorQuotientDensity
  apply div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact (add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_pos_of_ne_zero hc)).le

theorem periodicRegularizedDirectorSharpQuotientDensity_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    0 ≤ periodicRegularizedDirectorSharpQuotientDensity u ω c x := by
  unfold periodicRegularizedDirectorSharpQuotientDensity
  exact div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
    (sq_nonneg _)

theorem periodicRegularizedDirectorFrobeniusQuotientDensity_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    0 ≤ periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x := by
  unfold periodicRegularizedDirectorFrobeniusQuotientDensity
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (sq_nonneg _) (periodicGradientFrobeniusSq_nonneg u x))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    (sq_nonneg _)

theorem periodicRegularizedDirectorRadialQuotientDensity_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    0 ≤ periodicRegularizedDirectorRadialQuotientDensity u ω c x := by
  unfold periodicRegularizedDirectorRadialQuotientDensity
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg _) (periodicGradientFrobeniusSq_nonneg u x))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (by positivity))
    (by positivity)

theorem periodicRegularizedDirectorFrobeniusCauchyFactor_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    0 ≤ periodicRegularizedDirectorFrobeniusCauchyFactor u ω c x := by
  unfold periodicRegularizedDirectorFrobeniusCauchyFactor
  positivity

theorem periodicRegularizedDirectorDirectionCauchyFactor_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    0 ≤ periodicRegularizedDirectorDirectionCauchyFactor u ω c x := by
  unfold periodicRegularizedDirectorDirectionCauchyFactor
  positivity

theorem periodicRegularizedDirectorAmplitudeCauchyFactor_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    0 ≤ periodicRegularizedDirectorAmplitudeCauchyFactor u ω c x := by
  unfold periodicRegularizedDirectorAmplitudeCauchyFactor
  positivity

/-- The sharp quotient assigns zero density at an exact vorticity zero, independently of
the velocity and its gradient. -/
theorem periodicRegularizedDirectorSharpQuotientDensity_eq_zero_of_vorticity_eq_zero
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) (hzero : ω x = 0) :
    periodicRegularizedDirectorSharpQuotientDensity u ω c x = 0 := by
  simp [periodicRegularizedDirectorSharpQuotientDensity, hzero]

theorem periodicRegularizedDirectorFrobeniusQuotientDensity_eq_zero_of_vorticity_eq_zero
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) (hzero : ω x = 0) :
    periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x = 0 := by
  simp [periodicRegularizedDirectorFrobeniusQuotientDensity, hzero]

@[simp]
theorem periodicWeightedOptimalFrame_apply
    (weight : Torus3 → ℝ) (u : Torus3 → Vec3) (j : Fin 3) :
    periodicWeightedOptimalFrame weight u j =
      (∫ x : Torus3, weight x * u x j) / (∫ x : Torus3, weight x) := by
  rfl

/-- Generic vector-valued weighted-centering identity on the torus. -/
theorem periodicWeightedOptimalFrame_centering
    (weight : Torus3 → ℝ) (u : Torus3 → Vec3) (a : Vec3)
    (hweight : Integrable weight)
    (hmoment : ∀ j : Fin 3, Integrable (fun x : Torus3 => weight x * u x j))
    (hraw : ∀ j : Fin 3, Integrable (fun x : Torus3 => weight x * u x j ^ 2))
    (hmass : (0 : ℝ) < ∫ x : Torus3, weight x) :
    (∑ j : Fin 3, ∫ x : Torus3, weight x * (u x j - a j) ^ 2) =
      (∑ j : Fin 3, ∫ x : Torus3,
        weight x * (u x j - periodicWeightedOptimalFrame weight u j) ^ 2) +
        (∫ x : Torus3, weight x) *
          ‖a - periodicWeightedOptimalFrame weight u‖ ^ 2 := by
  have hcomponent : ∀ j : Fin 3,
      (∫ x : Torus3, weight x * (u x j - a j) ^ 2) =
        (∫ x : Torus3,
          weight x * (u x j - periodicWeightedOptimalFrame weight u j) ^ 2) +
        (∫ x : Torus3, weight x) *
          (a j - periodicWeightedOptimalFrame weight u j) ^ 2 := by
    intro j
    have ha := integral_weighted_centering_identity
      weight (fun x => u x j) (a j)
      hweight (hmoment j) (hraw j) hmass.ne'
    have hopt := integral_weighted_centering_identity
      weight (fun x => u x j) (periodicWeightedOptimalFrame weight u j)
      hweight (hmoment j) (hraw j) hmass.ne'
    have hopt' :
        (∫ x : Torus3,
          weight x * (u x j - periodicWeightedOptimalFrame weight u j) ^ 2) =
          (∫ x : Torus3, weight x * u x j ^ 2) -
            (∫ x : Torus3, weight x * u x j) ^ 2 /
              (∫ x : Torus3, weight x) := by
      rw [hopt]
      simp only [periodicWeightedOptimalFrame_apply, sub_self, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    rw [hopt']
    simpa only [periodicWeightedOptimalFrame_apply] using ha
  calc
    (∑ j : Fin 3, ∫ x : Torus3, weight x * (u x j - a j) ^ 2) =
        ∑ j : Fin 3,
          ((∫ x : Torus3,
              weight x * (u x j - periodicWeightedOptimalFrame weight u j) ^ 2) +
            (∫ x : Torus3, weight x) *
              (a j - periodicWeightedOptimalFrame weight u j) ^ 2) := by
      exact Finset.sum_congr rfl fun j _hj => hcomponent j
    _ = (∑ j : Fin 3, ∫ x : Torus3,
          weight x * (u x j - periodicWeightedOptimalFrame weight u j) ^ 2) +
        (∫ x : Torus3, weight x) *
          ‖a - periodicWeightedOptimalFrame weight u‖ ^ 2 := by
      rw [Finset.sum_add_distrib, EuclideanSpace.real_norm_sq_eq,
        Finset.mul_sum]
      simp only [PiLp.sub_apply]

@[simp]
theorem periodicRegularizedDirectorFrobeniusOptimalFrame_apply
    (u ω : Torus3 → Vec3) (c : ℝ) (j : Fin 3) :
    periodicRegularizedDirectorFrobeniusOptimalFrame u ω c j =
      (∫ x : Torus3,
        periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x * u x j) /
      (∫ x : Torus3,
        periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x) := by
  rfl

/-- Pointwise weighted-variance form of the centered Frobenius quotient. -/
theorem periodicRegularizedDirectorFrobeniusQuotientDensity_centered_eq_sum
    (u ω : Torus3 → Vec3) (c : ℝ) (a : Vec3) (x : Torus3) :
    periodicRegularizedDirectorFrobeniusQuotientDensity
        (centeredVelocity u a) ω c x =
      ∑ j : Fin 3, periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x *
        (u x j - a j) ^ 2 := by
  unfold periodicRegularizedDirectorFrobeniusQuotientDensity
    periodicRegularizedDirectorFrobeniusQuotientWeight
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [centeredVelocity_apply,
    periodicGradientFrobeniusSq_centeredVelocity, PiLp.sub_apply]
  simp only [Fin.sum_univ_three]
  ring

/-- The explicitly constructed Frobenius quotient frame gives the exact integrated variance
decomposition. -/
theorem periodicRegularizedDirectorFrobeniusOptimalFrame_quotient_centering
    (u ω : Torus3 → Vec3) (c : ℝ) (a : Vec3)
    (hweight : Integrable
      (periodicRegularizedDirectorFrobeniusQuotientWeight u ω c))
    (hmoment : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x * u x j))
    (hraw : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x * u x j ^ 2))
    (hmass : (0 : ℝ) < ∫ x : Torus3,
      periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x) :
    (∫ x : Torus3, periodicRegularizedDirectorFrobeniusQuotientDensity
      (centeredVelocity u a) ω c x) =
      (∫ x : Torus3, periodicRegularizedDirectorFrobeniusQuotientDensity
        (centeredVelocity u
          (periodicRegularizedDirectorFrobeniusOptimalFrame u ω c)) ω c x) +
        (∫ x : Torus3,
          periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x) *
          ‖a - periodicRegularizedDirectorFrobeniusOptimalFrame u ω c‖ ^ 2 := by
  let weight : Torus3 → ℝ :=
    periodicRegularizedDirectorFrobeniusQuotientWeight u ω c
  have hcentered : ∀ (b : Vec3) (j : Fin 3), Integrable (fun x : Torus3 =>
      weight x * (u x j - b j) ^ 2) := by
    intro b j
    have hexpand : Integrable (fun x : Torus3 =>
        (weight x * u x j ^ 2 - (2 * b j) * (weight x * u x j)) +
          b j ^ 2 * weight x) :=
      ((hraw j).sub ((hmoment j).const_mul _)).add (hweight.const_mul _)
    apply hexpand.congr
    exact Eventually.of_forall fun x => by ring
  have hsum (b : Vec3) :
      (∫ x : Torus3, ∑ j : Fin 3, weight x * (u x j - b j) ^ 2) =
        ∑ j : Fin 3, ∫ x : Torus3, weight x * (u x j - b j) ^ 2 := by
    exact MeasureTheory.integral_finsetSum Finset.univ fun j _hj => hcentered b j
  have hcoordinate := periodicWeightedOptimalFrame_centering
    weight u a hweight hmoment hraw hmass
  change (∫ x : Torus3, periodicRegularizedDirectorFrobeniusQuotientDensity
      (centeredVelocity u a) ω c x) = _
  calc
    (∫ x : Torus3, periodicRegularizedDirectorFrobeniusQuotientDensity
        (centeredVelocity u a) ω c x) =
        ∫ x : Torus3, ∑ j : Fin 3, weight x * (u x j - a j) ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simpa [weight] using
          periodicRegularizedDirectorFrobeniusQuotientDensity_centered_eq_sum
            u ω c a x
    _ = ∑ j : Fin 3, ∫ x : Torus3,
        weight x * (u x j - a j) ^ 2 := hsum a
    _ = (∑ j : Fin 3, ∫ x : Torus3,
          weight x *
            (u x j - periodicRegularizedDirectorFrobeniusOptimalFrame u ω c j) ^ 2) +
        (∫ x : Torus3, weight x) *
          ‖a - periodicRegularizedDirectorFrobeniusOptimalFrame u ω c‖ ^ 2 := by
      simpa [weight, periodicRegularizedDirectorFrobeniusOptimalFrame] using hcoordinate
    _ = (∫ x : Torus3, ∑ j : Fin 3,
          weight x *
            (u x j - periodicRegularizedDirectorFrobeniusOptimalFrame u ω c j) ^ 2) +
        (∫ x : Torus3, weight x) *
          ‖a - periodicRegularizedDirectorFrobeniusOptimalFrame u ω c‖ ^ 2 := by
      rw [hsum]
    _ = (∫ x : Torus3, periodicRegularizedDirectorFrobeniusQuotientDensity
          (centeredVelocity u
            (periodicRegularizedDirectorFrobeniusOptimalFrame u ω c)) ω c x) +
        (∫ x : Torus3,
          periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x) *
          ‖a - periodicRegularizedDirectorFrobeniusOptimalFrame u ω c‖ ^ 2 := by
      have hfirst :
          (∫ x : Torus3, ∑ j : Fin 3,
            weight x *
              (u x j - periodicRegularizedDirectorFrobeniusOptimalFrame u ω c j) ^ 2) =
            ∫ x : Torus3, periodicRegularizedDirectorFrobeniusQuotientDensity
              (centeredVelocity u
                (periodicRegularizedDirectorFrobeniusOptimalFrame u ω c)) ω c x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simpa [weight] using
            (periodicRegularizedDirectorFrobeniusQuotientDensity_centered_eq_sum
              u ω c (periodicRegularizedDirectorFrobeniusOptimalFrame u ω c) x).symm
      rw [hfirst]

/-- The Frobenius quotient frame minimizes the integrated charge among all constant frames. -/
theorem periodicRegularizedDirectorFrobeniusOptimalFrame_quotient_minimum
    (u ω : Torus3 → Vec3) (c : ℝ) (a : Vec3)
    (hweight : Integrable
      (periodicRegularizedDirectorFrobeniusQuotientWeight u ω c))
    (hmoment : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x * u x j))
    (hraw : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x * u x j ^ 2))
    (hmass : (0 : ℝ) < ∫ x : Torus3,
      periodicRegularizedDirectorFrobeniusQuotientWeight u ω c x) :
    (∫ x : Torus3, periodicRegularizedDirectorFrobeniusQuotientDensity
      (centeredVelocity u
        (periodicRegularizedDirectorFrobeniusOptimalFrame u ω c)) ω c x) ≤
      ∫ x : Torus3, periodicRegularizedDirectorFrobeniusQuotientDensity
        (centeredVelocity u a) ω c x := by
  rw [periodicRegularizedDirectorFrobeniusOptimalFrame_quotient_centering
    u ω c a hweight hmoment hraw hmass]
  exact le_add_of_nonneg_right (mul_nonneg hmass.le (sq_nonneg _))

@[simp]
theorem periodicRegularizedOptimalFrame_apply
    (u ω : Torus3 → Vec3) (c : ℝ) (j : Fin 3) :
    periodicRegularizedOptimalFrame u ω c j =
      (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x * u x j) /
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) := by
  rfl

/-- Pointwise coordinate representation of the quotient in a constant Galilean frame. -/
theorem periodicRegularizedQuotientDensity_centered_eq_sum
    (u ω : Torus3 → Vec3) (c : ℝ) (a : Vec3) (x : Torus3) :
    periodicRegularizedDirectorQuotientDensity (centeredVelocity u a) ω c x =
      ∑ j : Fin 3, periodicRegularizedQuotientWeight u ω c x *
        (u x j - a j) ^ 2 := by
  unfold periodicRegularizedDirectorQuotientDensity
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [periodicRegularizedQuotientWeight, centeredVelocity_apply,
    periodicGradientL1_centeredVelocity, PiLp.sub_apply]
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Exact vector-valued weighted-centering identity, expressed as the sum of its three
coordinate Haar integrals.  The optimal frame is constructed from the supplied fields. -/
theorem periodicRegularizedOptimalFrame_centering
    (u ω : Torus3 → Vec3) (c : ℝ) (a : Vec3)
    (hweight : Integrable (periodicRegularizedQuotientWeight u ω c))
    (hmoment : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedQuotientWeight u ω c x * u x j))
    (hraw : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedQuotientWeight u ω c x * u x j ^ 2))
    (hmass : (0 : ℝ) < ∫ x : Torus3,
      periodicRegularizedQuotientWeight u ω c x) :
    (∑ j : Fin 3, ∫ x : Torus3,
      periodicRegularizedQuotientWeight u ω c x * (u x j - a j) ^ 2) =
      (∑ j : Fin 3, ∫ x : Torus3,
        periodicRegularizedQuotientWeight u ω c x *
          (u x j - periodicRegularizedOptimalFrame u ω c j) ^ 2) +
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) *
          ‖a - periodicRegularizedOptimalFrame u ω c‖ ^ 2 := by
  have hcomponent : ∀ j : Fin 3,
      (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x *
          (u x j - a j) ^ 2) =
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x *
          (u x j - periodicRegularizedOptimalFrame u ω c j) ^ 2) +
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) *
          (a j - periodicRegularizedOptimalFrame u ω c j) ^ 2 := by
    intro j
    have ha := integral_weighted_centering_identity
      (periodicRegularizedQuotientWeight u ω c) (fun x => u x j) (a j)
      hweight (hmoment j) (hraw j) hmass.ne'
    have hopt := integral_weighted_centering_identity
      (periodicRegularizedQuotientWeight u ω c) (fun x => u x j)
      (periodicRegularizedOptimalFrame u ω c j)
      hweight (hmoment j) (hraw j) hmass.ne'
    have hopt' :
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x *
          (u x j - periodicRegularizedOptimalFrame u ω c j) ^ 2) =
          (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x * u x j ^ 2) -
            (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x * u x j) ^ 2 /
              (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) := by
      rw [hopt]
      simp only [periodicRegularizedOptimalFrame_apply, sub_self, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    rw [hopt']
    simpa only [periodicRegularizedOptimalFrame_apply] using ha
  calc
    (∑ j : Fin 3, ∫ x : Torus3,
        periodicRegularizedQuotientWeight u ω c x * (u x j - a j) ^ 2) =
        ∑ j : Fin 3,
          ((∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x *
              (u x j - periodicRegularizedOptimalFrame u ω c j) ^ 2) +
            (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) *
              (a j - periodicRegularizedOptimalFrame u ω c j) ^ 2) := by
      exact Finset.sum_congr rfl fun j _hj => hcomponent j
    _ = (∑ j : Fin 3, ∫ x : Torus3,
          periodicRegularizedQuotientWeight u ω c x *
            (u x j - periodicRegularizedOptimalFrame u ω c j) ^ 2) +
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) *
          ‖a - periodicRegularizedOptimalFrame u ω c‖ ^ 2 := by
      rw [Finset.sum_add_distrib, EuclideanSpace.real_norm_sq_eq,
        Finset.mul_sum]
      simp only [PiLp.sub_apply]

/-- Integrated quotient form of the optimal-frame identity. -/
theorem periodicRegularizedOptimalFrame_quotient_centering
    (u ω : Torus3 → Vec3) (c : ℝ) (a : Vec3)
    (hweight : Integrable (periodicRegularizedQuotientWeight u ω c))
    (hmoment : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedQuotientWeight u ω c x * u x j))
    (hraw : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedQuotientWeight u ω c x * u x j ^ 2))
    (hmass : (0 : ℝ) < ∫ x : Torus3,
      periodicRegularizedQuotientWeight u ω c x) :
    (∫ x : Torus3, periodicRegularizedDirectorQuotientDensity
      (centeredVelocity u a) ω c x) =
      (∫ x : Torus3, periodicRegularizedDirectorQuotientDensity
        (centeredVelocity u (periodicRegularizedOptimalFrame u ω c)) ω c x) +
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) *
          ‖a - periodicRegularizedOptimalFrame u ω c‖ ^ 2 := by
  have hcentered : ∀ (b : Vec3) (j : Fin 3), Integrable (fun x : Torus3 =>
      periodicRegularizedQuotientWeight u ω c x * (u x j - b j) ^ 2) := by
    intro b j
    have hexpand : Integrable (fun x : Torus3 =>
        (periodicRegularizedQuotientWeight u ω c x * u x j ^ 2 -
          (2 * b j) * (periodicRegularizedQuotientWeight u ω c x * u x j)) +
          b j ^ 2 * periodicRegularizedQuotientWeight u ω c x) :=
      ((hraw j).sub ((hmoment j).const_mul _)).add (hweight.const_mul _)
    apply hexpand.congr
    exact Eventually.of_forall fun x => by ring
  have hsum (b : Vec3) :
      (∫ x : Torus3, ∑ j : Fin 3,
        periodicRegularizedQuotientWeight u ω c x * (u x j - b j) ^ 2) =
        ∑ j : Fin 3, ∫ x : Torus3,
          periodicRegularizedQuotientWeight u ω c x * (u x j - b j) ^ 2 := by
    exact MeasureTheory.integral_finsetSum Finset.univ fun j _hj => hcentered b j
  calc
    (∫ x : Torus3, periodicRegularizedDirectorQuotientDensity
        (centeredVelocity u a) ω c x) =
        ∫ x : Torus3, ∑ j : Fin 3,
          periodicRegularizedQuotientWeight u ω c x * (u x j - a j) ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        periodicRegularizedQuotientDensity_centered_eq_sum u ω c a x
    _ = ∑ j : Fin 3, ∫ x : Torus3,
        periodicRegularizedQuotientWeight u ω c x * (u x j - a j) ^ 2 := hsum a
    _ = (∑ j : Fin 3, ∫ x : Torus3,
          periodicRegularizedQuotientWeight u ω c x *
            (u x j - periodicRegularizedOptimalFrame u ω c j) ^ 2) +
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) *
          ‖a - periodicRegularizedOptimalFrame u ω c‖ ^ 2 :=
      periodicRegularizedOptimalFrame_centering u ω c a
        hweight hmoment hraw hmass
    _ = (∫ x : Torus3, ∑ j : Fin 3,
          periodicRegularizedQuotientWeight u ω c x *
            (u x j - periodicRegularizedOptimalFrame u ω c j) ^ 2) +
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) *
          ‖a - periodicRegularizedOptimalFrame u ω c‖ ^ 2 := by
      rw [hsum]
    _ = (∫ x : Torus3, periodicRegularizedDirectorQuotientDensity
          (centeredVelocity u (periodicRegularizedOptimalFrame u ω c)) ω c x) +
        (∫ x : Torus3, periodicRegularizedQuotientWeight u ω c x) *
          ‖a - periodicRegularizedOptimalFrame u ω c‖ ^ 2 := by
      congr 2
      funext x
      exact (periodicRegularizedQuotientDensity_centered_eq_sum u ω c
        (periodicRegularizedOptimalFrame u ω c) x).symm

/-- The quotient-weighted frame minimizes the full integrated regularized quotient among all
spatially constant Galilean frames. -/
theorem periodicRegularizedOptimalFrame_quotient_minimum
    (u ω : Torus3 → Vec3) (c : ℝ) (a : Vec3)
    (hweight : Integrable (periodicRegularizedQuotientWeight u ω c))
    (hmoment : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedQuotientWeight u ω c x * u x j))
    (hraw : ∀ j : Fin 3, Integrable (fun x : Torus3 =>
      periodicRegularizedQuotientWeight u ω c x * u x j ^ 2))
    (hmass : (0 : ℝ) < ∫ x : Torus3,
      periodicRegularizedQuotientWeight u ω c x) :
    (∫ x : Torus3, periodicRegularizedDirectorQuotientDensity
      (centeredVelocity u (periodicRegularizedOptimalFrame u ω c)) ω c x) ≤
      ∫ x : Torus3, periodicRegularizedDirectorQuotientDensity
        (centeredVelocity u a) ω c x := by
  rw [periodicRegularizedOptimalFrame_quotient_centering
    u ω c a hweight hmoment hraw hmass]
  exact le_add_of_nonneg_right
    (mul_nonneg hmass.le (sq_nonneg _))

theorem periodicRegularizedDirectorCauchyFactor_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (_hc : c ≠ 0) (x : Torus3) :
    0 ≤ periodicRegularizedDirectorCauchyFactor u ω c x := by
  unfold periodicRegularizedDirectorCauchyFactor
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (mul_nonneg (norm_nonneg _) (periodicGradientL1_nonneg u x)))
    (Real.sqrt_nonneg _)

/-- Squaring the second Cauchy factor gives exactly `36² = 1296` times the nonsingular
quotient density (without the palinstrophy factor). -/
theorem periodicRegularizedDirectorCauchyFactor_sq
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    periodicRegularizedDirectorCauchyFactor u ω c x ^ 2 =
      1296 * periodicRegularizedDirectorQuotientDensity u ω c x := by
  have hD : 0 ≤ (∑ q : Fin 3, ω x q ^ 2) + c ^ 2 :=
    add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg c)
  have hD0 : (∑ q : Fin 3, ω x q ^ 2) + c ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_pos_of_ne_zero hc)).ne'
  unfold periodicRegularizedDirectorCauchyFactor
    periodicRegularizedDirectorQuotientDensity
  rw [div_pow, Real.sq_sqrt hD]
  field_simp [hD0]
  ring

theorem periodicRegularizedDirectorSharpCauchyFactor_nonneg
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    0 ≤ periodicRegularizedDirectorSharpCauchyFactor u ω c x := by
  unfold periodicRegularizedDirectorSharpCauchyFactor
  apply div_nonneg
  · exact mul_nonneg (by norm_num)
      (mul_nonneg
        (mul_nonneg (norm_nonneg _) (periodicGradientL1_nonneg u x))
        (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  · exact (add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_pos_of_ne_zero hc)).le

/-- Squaring the cancellation-preserving Cauchy factor gives exactly `135² = 18225`
times the sharp quotient density. -/
theorem periodicRegularizedDirectorSharpCauchyFactor_sq
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    periodicRegularizedDirectorSharpCauchyFactor u ω c x ^ 2 =
      18225 * periodicRegularizedDirectorSharpQuotientDensity u ω c x := by
  unfold periodicRegularizedDirectorSharpCauchyFactor
    periodicRegularizedDirectorSharpQuotientDensity
  rw [div_pow]
  ring

theorem real_sqrt_add_le_add_sqrt (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A + B) ≤ Real.sqrt A + Real.sqrt B := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
      mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]

/-- Squared angular factor in the exact split. -/
theorem periodicRegularizedDirectorDirectionCauchyFactor_sq
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    periodicRegularizedDirectorDirectionCauchyFactor u ω c x ^ 2 =
      2 * periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x := by
  have hG := periodicGradientFrobeniusSq_nonneg u x
  have hK : 0 ≤ 2 * (∑ q : Fin 3, ω x q ^ 2) /
      ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (sq_nonneg _)
  unfold periodicRegularizedDirectorDirectionCauchyFactor
    periodicRegularizedDirectorFrobeniusQuotientDensity
  rw [mul_pow, mul_pow, Real.sq_sqrt hG, Real.sq_sqrt hK]
  ring

/-- Squared radial-amplitude factor in the exact split. -/
theorem periodicRegularizedDirectorAmplitudeCauchyFactor_sq
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    periodicRegularizedDirectorAmplitudeCauchyFactor u ω c x ^ 2 =
      (8 / 3 : ℝ) *
        periodicRegularizedDirectorRadialQuotientDensity u ω c x := by
  have hG := periodicGradientFrobeniusSq_nonneg u x
  have hK : 0 ≤ (8 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) * c ^ 4 /
      ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4 := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
        (by positivity))
      (by positivity)
  unfold periodicRegularizedDirectorAmplitudeCauchyFactor
    periodicRegularizedDirectorRadialQuotientDensity
  rw [mul_pow, mul_pow, Real.sq_sqrt hG, Real.sq_sqrt hK]
  ring

/-- The Frobenius Cauchy factor squares to exactly `14/3` times the Euclidean sharp
quotient. -/
theorem periodicRegularizedDirectorFrobeniusCauchyFactor_sq
    (u ω : Torus3 → Vec3) (c : ℝ) (x : Torus3) :
    periodicRegularizedDirectorFrobeniusCauchyFactor u ω c x ^ 2 =
      (14 / 3 : ℝ) *
        periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x := by
  have hG : 0 ≤ periodicGradientFrobeniusSq u x :=
    periodicGradientFrobeniusSq_nonneg u x
  have hK : 0 ≤ (14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) /
      ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2 := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (sq_nonneg _)
  unfold periodicRegularizedDirectorFrobeniusCauchyFactor
    periodicRegularizedDirectorFrobeniusQuotientDensity
  rw [mul_pow, mul_pow, Real.sq_sqrt hG, Real.sq_sqrt hK]
  ring

/-- Pointwise Frobenius debit factorization. -/
theorem periodicDirectorFrobeniusDebitDensity_regularizedDirector_le
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y)) :
    periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c) x ≤
      Real.sqrt (periodicGradientFrobeniusSq ω x) *
        periodicRegularizedDirectorFrobeniusCauchyFactor u ω c x := by
  let K : ℝ := (14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (sq_nonneg _)
  have hP := periodicDirectorGradientFrobeniusSq_regularizedDirector_le
    ω c hc x hω
  have hPK :
      periodicDirectorGradientFrobeniusSq (regularizedDirector ω c) x ≤
        periodicGradientFrobeniusSq ω x * K := by
    convert hP using 1 <;> dsimp [K] <;> ring
  have hsqrt := Real.sqrt_le_sqrt hPK
  rw [Real.sqrt_mul (periodicGradientFrobeniusSq_nonneg ω x)] at hsqrt
  have hA : 0 ≤ ‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) :=
    mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsqrt hA
  unfold periodicDirectorFrobeniusDebitDensity
    periodicRegularizedDirectorFrobeniusCauchyFactor
  dsimp [K] at hmul
  calc
    ‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) *
        Real.sqrt (periodicDirectorGradientFrobeniusSq (regularizedDirector ω c) x) ≤
        (‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x)) *
          (Real.sqrt (periodicGradientFrobeniusSq ω x) *
            Real.sqrt ((14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) /
              ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2)) := hmul
    _ = Real.sqrt (periodicGradientFrobeniusSq ω x) *
        (‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) *
          Real.sqrt ((14 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) /
            ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2)) := by ring

/-- Pointwise exact two-channel factorization of the Frobenius debit. -/
theorem periodicDirectorFrobeniusDebitDensity_regularizedDirector_le_direction_amplitude
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y)) :
    periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c) x ≤
      Real.sqrt (periodicVorticityDirectionDissipationSq ω x) *
          periodicRegularizedDirectorDirectionCauchyFactor u ω c x +
        Real.sqrt (periodicVorticityAmplitudeDissipationSq ω x) *
          periodicRegularizedDirectorAmplitudeCauchyFactor u ω c x := by
  let direction : ℝ := periodicVorticityDirectionDissipationSq ω x
  let amplitude : ℝ := periodicVorticityAmplitudeDissipationSq ω x
  let K₁ : ℝ := 2 * (∑ q : Fin 3, ω x q ^ 2) /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2
  let K₂ : ℝ := (8 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) * c ^ 4 /
    ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4
  have hdirection : 0 ≤ direction :=
    periodicVorticityDirectionDissipationSq_nonneg ω x
  have hamplitude : 0 ≤ amplitude :=
    periodicVorticityAmplitudeDissipationSq_nonneg ω x
  have hK₁ : 0 ≤ K₁ := by
    dsimp [K₁]
    positivity
  have hK₂ : 0 ≤ K₂ := by
    dsimp [K₂]
    positivity
  have hgradient :
      periodicDirectorGradientFrobeniusSq (regularizedDirector ω c) x =
        direction * K₁ + amplitude * K₂ := by
    have hexact :=
      periodicDirectorGradientFrobeniusSq_regularizedDirector_direction_amplitude
        ω c hc x hω
    dsimp [direction, amplitude, K₁, K₂]
    convert hexact using 1 <;> ring
  have hsqrt :
      Real.sqrt (periodicDirectorGradientFrobeniusSq (regularizedDirector ω c) x) ≤
        Real.sqrt direction * Real.sqrt K₁ +
          Real.sqrt amplitude * Real.sqrt K₂ := by
    rw [hgradient]
    calc
      Real.sqrt (direction * K₁ + amplitude * K₂) ≤
          Real.sqrt (direction * K₁) + Real.sqrt (amplitude * K₂) :=
        real_sqrt_add_le_add_sqrt _ _
          (mul_nonneg hdirection hK₁) (mul_nonneg hamplitude hK₂)
      _ = Real.sqrt direction * Real.sqrt K₁ +
          Real.sqrt amplitude * Real.sqrt K₂ := by
        rw [Real.sqrt_mul hdirection, Real.sqrt_mul hamplitude]
  have hA : 0 ≤ ‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) :=
    mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsqrt hA
  unfold periodicDirectorFrobeniusDebitDensity
    periodicRegularizedDirectorDirectionCauchyFactor
    periodicRegularizedDirectorAmplitudeCauchyFactor
  dsimp [direction, amplitude, K₁, K₂] at hmul ⊢
  calc
    ‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) *
        Real.sqrt (periodicDirectorGradientFrobeniusSq (regularizedDirector ω c) x) ≤
        (‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x)) *
          (Real.sqrt (periodicVorticityDirectionDissipationSq ω x) *
              Real.sqrt (2 * (∑ q : Fin 3, ω x q ^ 2) /
                ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2) +
            Real.sqrt (periodicVorticityAmplitudeDissipationSq ω x) *
              Real.sqrt ((8 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) * c ^ 4 /
                ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4)) := hmul
    _ = Real.sqrt (periodicVorticityDirectionDissipationSq ω x) *
          (‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) *
            Real.sqrt (2 * (∑ q : Fin 3, ω x q ^ 2) /
              ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 2)) +
        Real.sqrt (periodicVorticityAmplitudeDissipationSq ω x) *
          (‖u x‖ * Real.sqrt (periodicGradientFrobeniusSq u x) *
            Real.sqrt ((8 / 3 : ℝ) * (∑ q : Fin 3, ω x q ^ 2) * c ^ 4 /
              ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2) ^ 4)) := by ring

/-- Frobenius Cauchy handoff for the complete tensor error. -/
theorem sq_integral_regularizedDirector_frobenius_mixed_le
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y))
    (hdebit : Integrable
      (periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c)))
    (hpal : MemLp
      (fun x : Torus3 => Real.sqrt (periodicGradientFrobeniusSq ω x)) 2 volume)
    (hquot : MemLp
      (periodicRegularizedDirectorFrobeniusCauchyFactor u ω c) 2 volume) :
    (∫ x : Torus3,
      periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c) x) ^ 2 ≤
      (∫ x : Torus3, periodicGradientFrobeniusSq ω x) *
        (∫ x : Torus3,
          periodicRegularizedDirectorFrobeniusCauchyFactor u ω c x ^ 2) := by
  have hbase := sq_integral_debit_le_sq_charges
    hdebit
    (Eventually.of_forall fun x =>
      periodicDirectorFrobeniusDebitDensity_nonneg u (regularizedDirector ω c) x)
    (Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (Eventually.of_forall fun x =>
      periodicRegularizedDirectorFrobeniusCauchyFactor_nonneg u ω c x)
    hpal hquot
    (Eventually.of_forall fun x =>
      periodicDirectorFrobeniusDebitDensity_regularizedDirector_le
        u ω c hc x hω)
  convert hbase using 1
  apply congrArg (fun z : ℝ => z *
    ∫ x : Torus3, periodicRegularizedDirectorFrobeniusCauchyFactor u ω c x ^ 2)
  apply integral_congr_ae
  exact Eventually.of_forall fun x =>
    (Real.sq_sqrt (periodicGradientFrobeniusSq_nonneg ω x)).symm

/-- Two-channel Frobenius handoff preserving the exact direction/amplitude split. -/
theorem sq_integral_regularizedDirector_frobenius_mixed_le_direction_amplitude
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y))
    (hdebit : Integrable
      (periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c)))
    (hdirection : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticityDirectionDissipationSq ω x)) 2 volume)
    (hdirectionQuotient : MemLp
      (periodicRegularizedDirectorDirectionCauchyFactor u ω c) 2 volume)
    (hamplitude : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticityAmplitudeDissipationSq ω x)) 2 volume)
    (hamplitudeQuotient : MemLp
      (periodicRegularizedDirectorAmplitudeCauchyFactor u ω c) 2 volume) :
    (∫ x : Torus3,
      periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c) x) ^ 2 ≤
      2 * (∫ x : Torus3, periodicVorticityDirectionDissipationSq ω x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorDirectionCauchyFactor u ω c x ^ 2) +
        2 * (∫ x : Torus3, periodicVorticityAmplitudeDissipationSq ω x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorAmplitudeCauchyFactor u ω c x ^ 2) := by
  have hbase := sq_integral_debit_le_two_sq_charges
    hdebit
    (Eventually.of_forall fun x =>
      periodicDirectorFrobeniusDebitDensity_nonneg u (regularizedDirector ω c) x)
    (Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (Eventually.of_forall fun x =>
      periodicRegularizedDirectorDirectionCauchyFactor_nonneg u ω c x)
    (Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (Eventually.of_forall fun x =>
      periodicRegularizedDirectorAmplitudeCauchyFactor_nonneg u ω c x)
    hdirection hdirectionQuotient hamplitude hamplitudeQuotient
    (Eventually.of_forall fun x =>
      periodicDirectorFrobeniusDebitDensity_regularizedDirector_le_direction_amplitude
        u ω c hc x hω)
  have hdirectionSq :
      (∫ x : Torus3,
        Real.sqrt (periodicVorticityDirectionDissipationSq ω x) ^ 2) =
        ∫ x : Torus3, periodicVorticityDirectionDissipationSq ω x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      Real.sq_sqrt (periodicVorticityDirectionDissipationSq_nonneg ω x)
  have hamplitudeSq :
      (∫ x : Torus3,
        Real.sqrt (periodicVorticityAmplitudeDissipationSq ω x) ^ 2) =
        ∫ x : Torus3, periodicVorticityAmplitudeDissipationSq ω x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x =>
      Real.sq_sqrt (periodicVorticityAmplitudeDissipationSq_nonneg ω x)
  rw [hdirectionSq, hamplitudeSq] at hbase
  exact hbase

/-- Expanded exact-split handoff.  The angular charge costs `4`, while the faster-decaying
radial-amplitude charge costs `16/3`. -/
theorem sq_integral_regularizedDirector_frobenius_mixed_le_direction_amplitude_quotients
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y))
    (hdebit : Integrable
      (periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c)))
    (hdirection : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticityDirectionDissipationSq ω x)) 2 volume)
    (hdirectionQuotient : MemLp
      (periodicRegularizedDirectorDirectionCauchyFactor u ω c) 2 volume)
    (hamplitude : MemLp (fun x : Torus3 =>
      Real.sqrt (periodicVorticityAmplitudeDissipationSq ω x)) 2 volume)
    (hamplitudeQuotient : MemLp
      (periodicRegularizedDirectorAmplitudeCauchyFactor u ω c) 2 volume) :
    (∫ x : Torus3,
      periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c) x) ^ 2 ≤
      4 * (∫ x : Torus3, periodicVorticityDirectionDissipationSq ω x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x) +
        (16 / 3 : ℝ) *
          (∫ x : Torus3, periodicVorticityAmplitudeDissipationSq ω x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorRadialQuotientDensity u ω c x) := by
  have hbase :=
    sq_integral_regularizedDirector_frobenius_mixed_le_direction_amplitude
      u ω c hc hω hdebit hdirection hdirectionQuotient
        hamplitude hamplitudeQuotient
  have hdirectionFactor :
      (∫ x : Torus3,
        periodicRegularizedDirectorDirectionCauchyFactor u ω c x ^ 2) =
        2 * ∫ x : Torus3,
          periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x := by
    calc
      (∫ x : Torus3,
          periodicRegularizedDirectorDirectionCauchyFactor u ω c x ^ 2) =
          ∫ x : Torus3, 2 *
            periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          periodicRegularizedDirectorDirectionCauchyFactor_sq u ω c x
      _ = 2 * ∫ x : Torus3,
          periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x := by
        rw [integral_const_mul]
  have hamplitudeFactor :
      (∫ x : Torus3,
        periodicRegularizedDirectorAmplitudeCauchyFactor u ω c x ^ 2) =
        (8 / 3 : ℝ) * ∫ x : Torus3,
          periodicRegularizedDirectorRadialQuotientDensity u ω c x := by
    calc
      (∫ x : Torus3,
          periodicRegularizedDirectorAmplitudeCauchyFactor u ω c x ^ 2) =
          ∫ x : Torus3, (8 / 3 : ℝ) *
            periodicRegularizedDirectorRadialQuotientDensity u ω c x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          periodicRegularizedDirectorAmplitudeCauchyFactor_sq u ω c x
      _ = (8 / 3 : ℝ) * ∫ x : Torus3,
          periodicRegularizedDirectorRadialQuotientDensity u ω c x := by
        rw [integral_const_mul]
  rw [hdirectionFactor, hamplitudeFactor] at hbase
  nlinarith

/-- Expanded Frobenius handoff.  The geometric constant is `14/3`, compared with
`18225` in the coordinatewise cancellation-preserving estimate. -/
theorem sq_integral_regularizedDirector_frobenius_mixed_le_quotient
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y))
    (hdebit : Integrable
      (periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c)))
    (hpal : MemLp
      (fun x : Torus3 => Real.sqrt (periodicGradientFrobeniusSq ω x)) 2 volume)
    (hquot : MemLp
      (periodicRegularizedDirectorFrobeniusCauchyFactor u ω c) 2 volume) :
    (∫ x : Torus3,
      periodicDirectorFrobeniusDebitDensity u (regularizedDirector ω c) x) ^ 2 ≤
      (14 / 3 : ℝ) *
        (∫ x : Torus3, periodicGradientFrobeniusSq ω x) *
        (∫ x : Torus3,
          periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x) := by
  have hbase := sq_integral_regularizedDirector_frobenius_mixed_le
    u ω c hc hω hdebit hpal hquot
  have hfactor :
      (∫ x : Torus3,
        periodicRegularizedDirectorFrobeniusCauchyFactor u ω c x ^ 2) =
        (14 / 3 : ℝ) * ∫ x : Torus3,
          periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x := by
    calc
      (∫ x : Torus3,
          periodicRegularizedDirectorFrobeniusCauchyFactor u ω c x ^ 2) =
          ∫ x : Torus3, (14 / 3 : ℝ) *
            periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          periodicRegularizedDirectorFrobeniusCauchyFactor_sq u ω c x
      _ = (14 / 3 : ℝ) * ∫ x : Torus3,
          periodicRegularizedDirectorFrobeniusQuotientDensity u ω c x := by
        rw [integral_const_mul]
  rw [hfactor] at hbase
  nlinarith

/-- Cauchy handoff for the regularized director.  The geometric tensor error is reduced to
palinstrophy times one explicit nonsingular quotient factor. -/
theorem sq_integral_regularizedDirector_mixed_le
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y))
    (hdebit : Integrable (fun x : Torus3 =>
      ‖u x‖ * periodicGradientL1 u x *
        periodicDirectorGradientL1 (regularizedDirector ω c) x))
    (hpal : MemLp (fun x : Torus3 => periodicGradientL1 ω x) 2 volume)
    (hquot : MemLp
      (periodicRegularizedDirectorCauchyFactor u ω c) 2 volume) :
    (∫ x : Torus3, ‖u x‖ * periodicGradientL1 u x *
        periodicDirectorGradientL1 (regularizedDirector ω c) x) ^ 2 ≤
      (∫ x : Torus3, periodicGradientL1 ω x ^ 2) *
        (∫ x : Torus3,
          periodicRegularizedDirectorCauchyFactor u ω c x ^ 2) := by
  apply sq_integral_debit_le_sq_charges
    hdebit
    (Eventually.of_forall fun x =>
      mul_nonneg
        (mul_nonneg (norm_nonneg _) (periodicGradientL1_nonneg u x))
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => abs_nonneg _))
    (Eventually.of_forall fun x => periodicGradientL1_nonneg ω x)
    (Eventually.of_forall fun x =>
      periodicRegularizedDirectorCauchyFactor_nonneg u ω c hc x)
    hpal hquot
  exact Eventually.of_forall fun x => by
    have hP := periodicDirectorGradientL1_regularizedDirector_le
      ω c hc x hω
    have hA : 0 ≤ ‖u x‖ * periodicGradientL1 u x :=
      mul_nonneg (norm_nonneg _) (periodicGradientL1_nonneg u x)
    have hmul := mul_le_mul_of_nonneg_left hP hA
    calc
      ‖u x‖ * periodicGradientL1 u x *
          periodicDirectorGradientL1 (regularizedDirector ω c) x ≤
          (‖u x‖ * periodicGradientL1 u x) *
            (36 * periodicGradientL1 ω x /
              Real.sqrt ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2)) := hmul
      _ = periodicGradientL1 ω x *
          periodicRegularizedDirectorCauchyFactor u ω c x := by
        unfold periodicRegularizedDirectorCauchyFactor
        ring

/-- Fully expanded quotient form of the regularized-director handoff. -/
theorem sq_integral_regularizedDirector_mixed_le_quotient
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y))
    (hdebit : Integrable (fun x : Torus3 =>
      ‖u x‖ * periodicGradientL1 u x *
        periodicDirectorGradientL1 (regularizedDirector ω c) x))
    (hpal : MemLp (fun x : Torus3 => periodicGradientL1 ω x) 2 volume)
    (hquot : MemLp
      (periodicRegularizedDirectorCauchyFactor u ω c) 2 volume) :
    (∫ x : Torus3, ‖u x‖ * periodicGradientL1 u x *
        periodicDirectorGradientL1 (regularizedDirector ω c) x) ^ 2 ≤
      1296 * (∫ x : Torus3, periodicGradientL1 ω x ^ 2) *
        (∫ x : Torus3,
          periodicRegularizedDirectorQuotientDensity u ω c x) := by
  have hbase := sq_integral_regularizedDirector_mixed_le
    u ω c hc hω hdebit hpal hquot
  have hfactor :
      (∫ x : Torus3, periodicRegularizedDirectorCauchyFactor u ω c x ^ 2) =
        1296 * ∫ x : Torus3,
          periodicRegularizedDirectorQuotientDensity u ω c x := by
    calc
      (∫ x : Torus3, periodicRegularizedDirectorCauchyFactor u ω c x ^ 2) =
          ∫ x : Torus3,
            1296 * periodicRegularizedDirectorQuotientDensity u ω c x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          periodicRegularizedDirectorCauchyFactor_sq u ω c hc x
      _ = 1296 * ∫ x : Torus3,
          periodicRegularizedDirectorQuotientDensity u ω c x := by
        rw [integral_const_mul]
  rw [hfactor] at hbase
  nlinarith

/-- Cancellation-preserving Cauchy handoff for the regularized director.  The new charge
retains one vorticity factor and therefore vanishes on the vorticity zero set. -/
theorem sq_integral_regularizedDirector_mixed_le_sharp
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y))
    (hdebit : Integrable (fun x : Torus3 =>
      ‖u x‖ * periodicGradientL1 u x *
        periodicDirectorGradientL1 (regularizedDirector ω c) x))
    (hpal : MemLp (fun x : Torus3 => periodicGradientL1 ω x) 2 volume)
    (hquot : MemLp
      (periodicRegularizedDirectorSharpCauchyFactor u ω c) 2 volume) :
    (∫ x : Torus3, ‖u x‖ * periodicGradientL1 u x *
        periodicDirectorGradientL1 (regularizedDirector ω c) x) ^ 2 ≤
      (∫ x : Torus3, periodicGradientL1 ω x ^ 2) *
        (∫ x : Torus3,
          periodicRegularizedDirectorSharpCauchyFactor u ω c x ^ 2) := by
  apply sq_integral_debit_le_sq_charges
    hdebit
    (Eventually.of_forall fun x =>
      mul_nonneg
        (mul_nonneg (norm_nonneg _) (periodicGradientL1_nonneg u x))
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => abs_nonneg _))
    (Eventually.of_forall fun x => periodicGradientL1_nonneg ω x)
    (Eventually.of_forall fun x =>
      periodicRegularizedDirectorSharpCauchyFactor_nonneg u ω c hc x)
    hpal hquot
  exact Eventually.of_forall fun x => by
    have hP := periodicDirectorGradientL1_regularizedDirector_le_sharp
      ω c hc x hω
    have hA : 0 ≤ ‖u x‖ * periodicGradientL1 u x :=
      mul_nonneg (norm_nonneg _) (periodicGradientL1_nonneg u x)
    have hmul := mul_le_mul_of_nonneg_left hP hA
    calc
      ‖u x‖ * periodicGradientL1 u x *
          periodicDirectorGradientL1 (regularizedDirector ω c) x ≤
          (‖u x‖ * periodicGradientL1 u x) *
            (135 * (∑ q : Fin 3, |ω x q|) * periodicGradientL1 ω x /
              ((∑ q : Fin 3, ω x q ^ 2) + c ^ 2)) := hmul
      _ = periodicGradientL1 ω x *
          periodicRegularizedDirectorSharpCauchyFactor u ω c x := by
        unfold periodicRegularizedDirectorSharpCauchyFactor
        ring

/-- Fully expanded cancellation-preserving quotient handoff. -/
theorem sq_integral_regularizedDirector_mixed_le_sharp_quotient
    (u ω : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hω : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => ω z q) a y))
    (hdebit : Integrable (fun x : Torus3 =>
      ‖u x‖ * periodicGradientL1 u x *
        periodicDirectorGradientL1 (regularizedDirector ω c) x))
    (hpal : MemLp (fun x : Torus3 => periodicGradientL1 ω x) 2 volume)
    (hquot : MemLp
      (periodicRegularizedDirectorSharpCauchyFactor u ω c) 2 volume) :
    (∫ x : Torus3, ‖u x‖ * periodicGradientL1 u x *
        periodicDirectorGradientL1 (regularizedDirector ω c) x) ^ 2 ≤
      18225 * (∫ x : Torus3, periodicGradientL1 ω x ^ 2) *
        (∫ x : Torus3,
          periodicRegularizedDirectorSharpQuotientDensity u ω c x) := by
  have hbase := sq_integral_regularizedDirector_mixed_le_sharp
    u ω c hc hω hdebit hpal hquot
  have hfactor :
      (∫ x : Torus3,
        periodicRegularizedDirectorSharpCauchyFactor u ω c x ^ 2) =
        18225 * ∫ x : Torus3,
          periodicRegularizedDirectorSharpQuotientDensity u ω c x := by
    calc
      (∫ x : Torus3,
          periodicRegularizedDirectorSharpCauchyFactor u ω c x ^ 2) =
          ∫ x : Torus3,
            18225 * periodicRegularizedDirectorSharpQuotientDensity u ω c x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          periodicRegularizedDirectorSharpCauchyFactor_sq u ω c x
      _ = 18225 * ∫ x : Torus3,
          periodicRegularizedDirectorSharpQuotientDensity u ω c x := by
        rw [integral_const_mul]
  rw [hfactor] at hbase
  nlinarith

/-- Rank-one director associated with an oriented unit field; its sign is forgotten. -/
def rankOneDirector (e : Torus3 → Vec3) : DirectorTensorField :=
  fun x j k => e x j * e x k

/-- Pointwise convex interpolation of two director fields. -/
def blendDirector
    (χ : Torus3 → ℝ) (P Q : DirectorTensorField) : DirectorTensorField :=
  fun x j k => χ x * P x j k + (1 - χ x) * Q x j k

theorem rankOneDirector_symmetric (e : Torus3 → Vec3) (x : Torus3) (j k : Fin 3) :
    rankOneDirector e x j k = rankOneDirector e x k j := by
  simp [rankOneDirector, mul_comm]

theorem rankOneDirector_trace_eq_one
    (e : Torus3 → Vec3) (x : Torus3) (hunit : ‖e x‖ = 1) :
    (∑ j : Fin 3, rankOneDirector e x j j) = 1 := by
  change (∑ j : Fin 3, e x j * e x j) = 1
  have hinner : inner ℝ (e x) (e x) = 1 := by
    calc
      inner ℝ (e x) (e x) = ‖e x‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
      _ = 1 := by rw [hunit]; norm_num
  rw [PiLp.inner_apply] at hinner
  simpa only [Real.inner_apply] using hinner

theorem blendDirector_symmetric
    (χ : Torus3 → ℝ) (P Q : DirectorTensorField)
    (hP : ∀ (x : Torus3) (j k : Fin 3), P x j k = P x k j)
    (hQ : ∀ (x : Torus3) (j k : Fin 3), Q x j k = Q x k j)
    (x : Torus3) (j k : Fin 3) :
    blendDirector χ P Q x j k = blendDirector χ P Q x k j := by
  simp [blendDirector, hP x j k, hQ x j k]

theorem blendDirector_trace_eq_one
    (χ : Torus3 → ℝ) (P Q : DirectorTensorField)
    (hP : ∀ x : Torus3, (∑ j : Fin 3, P x j j) = 1)
    (hQ : ∀ x : Torus3, (∑ j : Fin 3, Q x j j) = 1)
    (x : Torus3) :
    (∑ j : Fin 3, blendDirector χ P Q x j j) = 1 := by
  simp only [blendDirector, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hP x, hQ x]
  ring

/-- Tensor contraction with the squared symmetric velocity gradient. -/
def periodicDirectorStrainSq
    (u : Torus3 → Vec3) (P : DirectorTensorField) (x : Torus3) : ℝ :=
  ∑ j : Fin 3, ∑ k : Fin 3, P x j k *
    (∑ q : Fin 3,
      ((periodicFirstDerivative u j q x + periodicFirstDerivative u q j x) / 2) *
      ((periodicFirstDerivative u k q x + periodicFirstDerivative u q k x) / 2))

theorem periodicDirectorStrainSq_rankOneDirector
    (u e : Torus3 → Vec3) (x : Torus3) :
    periodicDirectorStrainSq u (rankOneDirector e) x =
      ‖periodicStrainAction u e x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [periodicDirectorStrainSq, rankOneDirector, periodicStrainAction,
    periodicGradientAction, periodicTransposeGradientAction,
    Fin.sum_univ_three]
  ring

/-- Tensor version of the transverse-vorticity square.  For `P=e⊗e` of trace one this is
`|e × ω|²`. -/
def periodicDirectorCrossCurlSq
    (u : Torus3 → Vec3) (P : DirectorTensorField) (x : Torus3) : ℝ :=
  (∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2) *
      (∑ j : Fin 3, P x j j) -
    ∑ j : Fin 3, ∑ k : Fin 3,
      P x j k * periodicCoordinateCurl u x j * periodicCoordinateCurl u x k

theorem periodicDirectorCrossCurlSq_isotropicDirector
    (u : Torus3 → Vec3) (x : Torus3) :
    periodicDirectorCrossCurlSq u isotropicDirector x =
      (2 : ℝ) / 3 * ∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2 := by
  simp [periodicDirectorCrossCurlSq, isotropicDirector, Fin.sum_univ_three]
  ring

theorem periodicDirectorStrainSq_isotropicDirector
    (u : Torus3 → Vec3) (x : Torus3) :
    periodicDirectorStrainSq u isotropicDirector x =
      (1 : ℝ) / 3 * ∑ j : Fin 3, ∑ q : Fin 3,
        ((periodicFirstDerivative u j q x +
          periodicFirstDerivative u q j x) / 2) ^ 2 := by
  simp [periodicDirectorStrainSq, isotropicDirector, Fin.sum_univ_three]
  ring

theorem periodicDirectorStrainSq_isotropicDirector_nonneg
    (u : Torus3 → Vec3) (x : Torus3) :
    0 ≤ periodicDirectorStrainSq u isotropicDirector x := by
  rw [periodicDirectorStrainSq_isotropicDirector]
  positivity

/-- Exact transverse-vorticity charge of the nonsingular regularized director. -/
theorem periodicDirectorCrossCurlSq_regularizedDirector
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    periodicDirectorCrossCurlSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x =
      ((2 : ℝ) / 3) * c ^ 2 *
        (∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2) /
          ((∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2) + c ^ 2) := by
  have hsum0 : 0 ≤ ∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hden : (∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2) + c ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos hsum0 hc2).ne'
  simp [periodicDirectorCrossCurlSq, regularizedDirector,
    periodicCoordinateCurl, Fin.sum_univ_three]
  field_simp [hden]
  ring

theorem periodicDirectorStrainSq_regularizedDirector
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    periodicDirectorStrainSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x =
      (periodicDirectorStrainSq u
          (rankOneDirector (fun y => periodicCoordinateCurl u y)) x +
        c ^ 2 * periodicDirectorStrainSq u isotropicDirector x) /
        ((∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2) + c ^ 2) := by
  have hsum0 : 0 ≤ ∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hden : (∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2) + c ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos hsum0 hc2).ne'
  simp [periodicDirectorStrainSq, regularizedDirector, rankOneDirector,
    isotropicDirector, periodicCoordinateCurl, Fin.sum_univ_three]
  field_simp [hden]
  ring

theorem periodicDirectorStrainSq_regularizedDirector_nonneg
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    0 ≤ periodicDirectorStrainSq u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x := by
  rw [periodicDirectorStrainSq_regularizedDirector u c hc x]
  have hden : 0 <
      (∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2) + c ^ 2 :=
    add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_pos_of_ne_zero hc)
  apply div_nonneg
  · exact add_nonneg (by
      rw [periodicDirectorStrainSq_rankOneDirector]
      positivity) (mul_nonneg (sq_nonneg c)
        (periodicDirectorStrainSq_isotropicDirector_nonneg u x))
  · exact hden.le

theorem regularizedDirector_cross_charge_le
    (rhoSq c : ℝ) (hrho : 0 ≤ rhoSq) (hc : c ≠ 0) :
    ((2 : ℝ) / 3) * c ^ 2 * rhoSq / (rhoSq + c ^ 2) ≤
      (2 : ℝ) / 3 * c ^ 2 := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hden : 0 < rhoSq + c ^ 2 := add_pos_of_nonneg_of_pos hrho hc2
  rw [div_le_iff₀ hden]
  nlinarith

theorem periodicDirectorCrossCurlSq_regularizedDirector_nonneg
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    0 ≤ periodicDirectorCrossCurlSq u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x := by
  rw [periodicDirectorCrossCurlSq_regularizedDirector u c hc x]
  apply div_nonneg
  · positivity
  · exact add_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg c)

theorem periodicDirectorCrossCurlSq_regularizedDirector_le
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0) (x : Torus3) :
    periodicDirectorCrossCurlSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x ≤
      (2 : ℝ) / 3 * c ^ 2 := by
  rw [periodicDirectorCrossCurlSq_regularizedDirector u c hc x]
  exact regularizedDirector_cross_charge_le _ c
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) hc

/-- The regularized tensor makes the spatial cross charge uniformly bounded, independently of
the vorticity amplitude. -/
theorem integral_periodicDirectorCross_regularized_le
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hcross : Integrable (fun x : Torus3 =>
      periodicDirectorCrossCurlSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x)) :
    (∫ x : Torus3, periodicDirectorCrossCurlSq u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ≤
      ((2 : ℝ) / 3 * c ^ 2) * volume.real (Set.univ : Set Torus3) := by
  calc
    (∫ x : Torus3, periodicDirectorCrossCurlSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ≤
        ∫ _ : Torus3, (2 : ℝ) / 3 * c ^ 2 := by
      apply integral_mono_ae hcross (integrable_const _)
      exact Eventually.of_forall fun x =>
        periodicDirectorCrossCurlSq_regularizedDirector_le u c hc x
    _ = ((2 : ℝ) / 3 * c ^ 2) * volume.real (Set.univ : Set Torus3) := by
      rw [integral_const]
      simp only [Measure.real, smul_eq_mul]
      ring

theorem periodicDirectorCrossFourth_regularized_le
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hcross : Integrable (fun x : Torus3 =>
      periodicDirectorCrossCurlSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x)) :
    (∫ x : Torus3, periodicDirectorCrossCurlSq u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 ≤
      (((2 : ℝ) / 3 * c ^ 2) * volume.real (Set.univ : Set Torus3)) ^ 2 := by
  have hleft0 : 0 ≤ ∫ x : Torus3, periodicDirectorCrossCurlSq u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x :=
    integral_nonneg_of_ae (Eventually.of_forall fun x =>
      periodicDirectorCrossCurlSq_regularizedDirector_nonneg u c hc x)
  have hright0 : 0 ≤ ((2 : ℝ) / 3 * c ^ 2) *
      volume.real (Set.univ : Set Torus3) := by
    positivity
  exact (sq_le_sq₀ hleft0 hright0).2
    (integral_periodicDirectorCross_regularized_le u c hc hcross)

theorem periodicDirectorStrainSq_blendDirector
    (u : Torus3 → Vec3) (χ : Torus3 → ℝ)
    (P Q : DirectorTensorField) (x : Torus3) :
    periodicDirectorStrainSq u (blendDirector χ P Q) x =
      χ x * periodicDirectorStrainSq u P x +
        (1 - χ x) * periodicDirectorStrainSq u Q x := by
  simp [periodicDirectorStrainSq, blendDirector, Fin.sum_univ_three]
  ring

theorem periodicDirectorCrossCurlSq_blendDirector
    (u : Torus3 → Vec3) (χ : Torus3 → ℝ)
    (P Q : DirectorTensorField) (x : Torus3) :
    periodicDirectorCrossCurlSq u (blendDirector χ P Q) x =
      χ x * periodicDirectorCrossCurlSq u P x +
        (1 - χ x) * periodicDirectorCrossCurlSq u Q x := by
  simp [periodicDirectorCrossCurlSq, blendDirector, Fin.sum_univ_three]
  ring

theorem periodicDirectorGradientL1_nonneg (P : DirectorTensorField) (x : Torus3) :
    0 ≤ periodicDirectorGradientL1 P x := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_periodicDirectorDerivative_le_gradientL1
    (P : DirectorTensorField) (i j k : Fin 3) (x : Torus3) :
    |periodicDirectorDerivative P i j k x| ≤ periodicDirectorGradientL1 P x := by
  unfold periodicDirectorGradientL1
  calc
    |periodicDirectorDerivative P i j k x| ≤
        ∑ c : Fin 3, |periodicDirectorDerivative P i j c x| :=
      Finset.single_le_sum (f := fun c : Fin 3 =>
        |periodicDirectorDerivative P i j c x|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ b : Fin 3, ∑ c : Fin 3,
        |periodicDirectorDerivative P i b c x| :=
      Finset.single_le_sum (f := fun b : Fin 3 =>
        ∑ c : Fin 3, |periodicDirectorDerivative P i b c x|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        |periodicDirectorDerivative P a b c x| :=
      Finset.single_le_sum (f := fun a : Fin 3 =>
        ∑ b : Fin 3, ∑ c : Fin 3, |periodicDirectorDerivative P a b c x|)
        (fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)

/-- Tensor form of the mixed gradient pairing. -/
def directorMixedIntegrand
    (u : Torus3 → Vec3) (P : DirectorTensorField)
    (i j k : Fin 3) (x : Torus3) : ℝ :=
  periodicFirstDerivative u i j x *
    (periodicFirstDerivative u k i x * P x j k)

/-- Pointwise mixed contraction appearing before periodic integration. -/
def periodicDirectorMixed
    (u : Torus3 → Vec3) (P : DirectorTensorField) (x : Torus3) : ℝ :=
  ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
    directorMixedIntegrand u P i j k x

theorem periodicDirectorMixed_blendDirector
    (u : Torus3 → Vec3) (χ : Torus3 → ℝ)
    (P Q : DirectorTensorField) (x : Torus3) :
    periodicDirectorMixed u (blendDirector χ P Q) x =
      χ x * periodicDirectorMixed u P x +
        (1 - χ x) * periodicDirectorMixed u Q x := by
  simp [periodicDirectorMixed, directorMixedIntegrand,
    blendDirector, Fin.sum_univ_three]
  ring

/-- Pointwise strain/curl/mixed identity for any symmetric trace-one director tensor.  Rank
one is not required. -/
theorem periodicDirectorStrainSq_eq_crossCurl_add_mixed
    (u : Torus3 → Vec3) (P : DirectorTensorField) (x : Torus3)
    (hsym : ∀ j k : Fin 3, P x j k = P x k j)
    (htrace : (∑ j : Fin 3, P x j j) = 1) :
    periodicDirectorStrainSq u P x =
      periodicDirectorCrossCurlSq u P x / 4 + periodicDirectorMixed u P x := by
  have hdiag : P x 2 2 = 1 - P x 0 0 - P x 1 1 := by
    simp only [Fin.sum_univ_three] at htrace
    linarith
  simp only [periodicDirectorStrainSq, periodicDirectorCrossCurlSq,
    periodicDirectorMixed, directorMixedIntegrand, Fin.sum_univ_three]
  rw [hsym 1 0, hsym 2 0, hsym 2 1, hdiag]
  simp [periodicCoordinateCurl]
  ring

/-- Differentiating the unoriented rank-one director reproduces the two oriented direction
derivatives, but the tensor formulation need not choose their signs separately. -/
theorem periodicDirectorDerivative_rankOneDirector
    (e : Torus3 → Vec3) (i j k : Fin 3) (x : Torus3)
    (he : ∀ (a b : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => e z b) a y)) :
    periodicDirectorDerivative (rankOneDirector e) i j k x =
      periodicFirstDerivative e i j x * e x k +
        e x j * periodicFirstDerivative e i k x := by
  simpa [periodicDirectorDerivative, rankOneDirector, periodicFirstDerivative] using
    torusCoordinateDerivative_mul (fun z => e z j) (fun z => e z k) i x
      (he i j (Fin.removeNth i x)) (he i k (Fin.removeNth i x))

/-- Cauchy--Schwarz for a real `3 × 3 × 3` contraction, written in the nested-sum
convention used by the director identity. -/
theorem abs_fin3_triple_sum_mul_le_sqrt
    (a b : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, a i j k * b i j k| ≤
      Real.sqrt (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, a i j k ^ 2) *
        Real.sqrt (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, b i j k ^ 2) := by
  let f : Fin 3 × (Fin 3 × Fin 3) → ℝ := fun p => a p.2.2 p.1 p.2.1
  let g : Fin 3 × (Fin 3 × Fin 3) → ℝ := fun p => b p.2.2 p.1 p.2.1
  have hupper := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin 3 × (Fin 3 × Fin 3))) f g
  have hlower := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin 3 × (Fin 3 × Fin 3))) (fun p => -f p) g
  rw [abs_le]
  constructor
  · have hlower' :
        -(∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, a i j k * b i j k) ≤
          Real.sqrt (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, a i j k ^ 2) *
            Real.sqrt (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, b i j k ^ 2) := by
        simpa [f, g, Fintype.sum_prod_type, mul_assoc] using hlower
    linarith
  · simpa [f, g, Fintype.sum_prod_type, mul_assoc] using hupper

/-- The first Frobenius factor in the director error splits exactly into velocity magnitude
times velocity-gradient magnitude. -/
theorem director_error_velocity_factor_sq
    (u : Torus3 → Vec3) (x : Torus3) :
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      (u x j * periodicFirstDerivative u k i x) ^ 2) =
      ‖u x‖ ^ 2 * periodicGradientFrobeniusSq u x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [periodicGradientFrobeniusSq, Fin.sum_univ_three]
  ring

/-- The sole director-gradient error after differentiating `Pⱼₖ` as one object. -/
def directorErrorIntegrand
    (u : Torus3 → Vec3) (P : DirectorTensorField)
    (i j k : Fin 3) (x : Torus3) : ℝ :=
  u x j *
    (periodicFirstDerivative u k i x * periodicDirectorDerivative P i j k x)

/-- A single Frobenius Cauchy--Schwarz estimate controls the complete 27-component error
contraction.  No dimension-counting constant is lost. -/
theorem abs_directorErrorDensity_le_frobenius
    (u : Torus3 → Vec3) (P : DirectorTensorField) (x : Torus3) :
    |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      directorErrorIntegrand u P i j k x| ≤
      periodicDirectorFrobeniusDebitDensity u P x := by
  have h := abs_fin3_triple_sum_mul_le_sqrt
    (fun i j k => u x j * periodicFirstDerivative u k i x)
    (fun i j k => periodicDirectorDerivative P i j k x)
  have hfactor := director_error_velocity_factor_sq u x
  rw [hfactor] at h
  rw [Real.sqrt_mul (sq_nonneg ‖u x‖), Real.sqrt_sq (norm_nonneg _)] at h
  have hdir :
      (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        periodicDirectorDerivative P i j k x ^ 2) =
        periodicDirectorGradientFrobeniusSq P x := by
    simp only [periodicDirectorGradientFrobeniusSq, Fin.sum_univ_three]
    ring
  rw [hdir] at h
  simpa only [directorErrorIntegrand, periodicDirectorFrobeniusDebitDensity,
    mul_assoc] using h

/-- The differentiated-divergence term before summation in `i`. -/
def directorDivergenceIntegrand
    (u : Torus3 → Vec3) (P : DirectorTensorField)
    (i j k : Fin 3) (x : Torus3) : ℝ :=
  u x j * (periodicSecondDerivative u i k i x * P x j k)

/-- On a smooth oriented representative, the single tensor error is exactly the previously
expanded two-term direction error. -/
theorem directorErrorIntegrand_rankOneDirector_eq
    (u e : Torus3 → Vec3) (i j k : Fin 3) (x : Torus3)
    (he : ∀ (a b : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun z => e z b) a y)) :
    directorErrorIntegrand u (rankOneDirector e) i j k x =
      anisotropicDirectionErrorIntegrand u e i j k x := by
  rw [directorErrorIntegrand, anisotropicDirectionErrorIntegrand,
    periodicDirectorDerivative_rankOneDirector e i j k x he]
  ring

theorem periodicDirectorMixed_rankOneDirector
    (u e : Torus3 → Vec3) (x : Torus3) :
    periodicDirectorMixed u (rankOneDirector e) x =
      ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        anisotropicMixedIntegrand u e i j k x := by
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [directorMixedIntegrand, rankOneDirector, anisotropicMixedIntegrand]
  ring

theorem periodicDirectorCrossCurlSq_rankOneDirector
    (u e : Torus3 → Vec3) (x : Torus3) :
    periodicDirectorCrossCurlSq u (rankOneDirector e) x =
      ‖vec3Cross (e x) (periodicCoordinateCurl u x)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [periodicDirectorCrossCurlSq, rankOneDirector, vec3Cross,
    periodicCoordinateCurl, Fin.sum_univ_three]
  ring

theorem vec3Cross_self_smul_zero (e : Vec3) (ρ : ℝ) :
    vec3Cross e (ρ • e) = 0 := by
  ext q
  fin_cases q <;> simp [vec3Cross] <;> ring

theorem periodicDirectorCrossCurlSq_rankOneDirector_aligned
    (u e : Torus3 → Vec3) (x : Torus3) (ρ : ℝ)
    (halign : periodicCoordinateCurl u x = ρ • e x) :
    periodicDirectorCrossCurlSq u (rankOneDirector e) x = 0 := by
  rw [periodicDirectorCrossCurlSq_rankOneDirector, halign,
    vec3Cross_self_smul_zero]
  simp

/-- In the convex relaxation between an aligned vorticity director and `I/3`, all transverse
vorticity is confined to the isotropic fraction `1 - χ`. -/
theorem periodicDirectorCrossCurlSq_blend_aligned_isotropic
    (u e : Torus3 → Vec3) (χ : Torus3 → ℝ) (x : Torus3) (ρ : ℝ)
    (halign : periodicCoordinateCurl u x = ρ • e x) :
    periodicDirectorCrossCurlSq u
        (blendDirector χ (rankOneDirector e) isotropicDirector) x =
      (1 - χ x) * ((2 : ℝ) / 3) *
        ∑ q : Fin 3, periodicCoordinateCurl u x q ^ 2 := by
  rw [periodicDirectorCrossCurlSq_blendDirector,
    periodicDirectorCrossCurlSq_rankOneDirector_aligned u e x ρ halign,
    periodicDirectorCrossCurlSq_isotropicDirector]
  ring

/-- Full periodic integration identity for an unoriented director tensor. -/
theorem torus3_director_mixed_pairing_eq_error
    (u : Torus3 → Vec3) (P : DirectorTensorField)
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hP : ∀ (i j k : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => P x j k) i y))
    (huFirst : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => periodicFirstDerivative u k j x) i y))
    (hleft : ∀ i j k : Fin 3, Integrable (directorMixedIntegrand u P i j k))
    (herror : ∀ i j k : Fin 3, Integrable (directorErrorIntegrand u P i j k))
    (hmiddle : ∀ i j k : Fin 3,
      Integrable (directorDivergenceIntegrand u P i j k))
    (hdiv : ∀ (x : Torus3) (k : Fin 3),
      ∑ i : Fin 3, periodicSecondDerivative u i k i x = 0) :
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      ∫ x : Torus3, directorMixedIntegrand u P i j k x) =
      -(∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, directorErrorIntegrand u P i j k x) := by
  have hcomponent : ∀ i j k : Fin 3,
      (∫ x : Torus3, directorMixedIntegrand u P i j k x) =
        -(∫ x : Torus3,
          directorDivergenceIntegrand u P i j k x +
            directorErrorIntegrand u P i j k x) := by
    intro i j k
    let f : Torus3 → ℝ := fun x => u x j
    let a : Torus3 → ℝ := fun x => periodicFirstDerivative u k i x
    let b : Torus3 → ℝ := fun x => P x j k
    let c : Torus3 → ℝ := fun _ => 1
    have hright : Integrable (fun x : Torus3 => f x *
        (((torusCoordinateDerivative a i x * b x) * c x +
          (a x * torusCoordinateDerivative b i x) * c x +
            (a x * b x) * torusCoordinateDerivative c i x))) := by
      have hsum := (hmiddle i j k).add (herror i j k)
      apply hsum.congr
      filter_upwards with x
      change directorDivergenceIntegrand u P i j k x +
        directorErrorIntegrand u P i j k x = _
      simp only [f, a, b, c, directorDivergenceIntegrand,
        directorErrorIntegrand, periodicSecondDerivative,
        periodicDirectorDerivative, periodicFirstDerivative,
        torusCoordinateDerivative_const, mul_one, mul_zero, add_zero]
      ring
    have hleft' : Integrable (fun x : Torus3 =>
        torusCoordinateDerivative f i x * ((a x * b x) * c x)) := by
      apply (hleft i j k).congr
      filter_upwards with x
      simp only [f, a, b, c, directorMixedIntegrand,
        periodicFirstDerivative, mul_one]
    have hparts := torus3_integral_coordinateDerivative_mul_three_eq_neg
      f a b c i (hu i j) (huFirst i k i) (hP i j k)
      (fun _ => contDiff_const) hleft' hright
    calc
      (∫ x : Torus3, directorMixedIntegrand u P i j k x) =
          ∫ x : Torus3,
            torusCoordinateDerivative f i x * ((a x * b x) * c x) := by
        congr 1
        funext x
        simp only [f, a, b, c, directorMixedIntegrand,
          periodicFirstDerivative, mul_one]
      _ = -(∫ x : Torus3, f x *
          (((torusCoordinateDerivative a i x * b x) * c x +
            (a x * torusCoordinateDerivative b i x) * c x +
              (a x * b x) * torusCoordinateDerivative c i x))) := hparts
      _ = -(∫ x : Torus3,
          directorDivergenceIntegrand u P i j k x +
            directorErrorIntegrand u P i j k x) := by
        congr 2
        funext x
        simp only [f, a, b, c, directorDivergenceIntegrand,
          directorErrorIntegrand, periodicSecondDerivative,
          periodicDirectorDerivative, periodicFirstDerivative,
          torusCoordinateDerivative_const, mul_one, mul_zero, add_zero]
        ring
  have hmiddleJK : ∀ j k : Fin 3,
      (∑ i : Fin 3,
        ∫ x : Torus3, directorDivergenceIntegrand u P i j k x) = 0 := by
    intro j k
    calc
      (∑ i : Fin 3,
          ∫ x : Torus3, directorDivergenceIntegrand u P i j k x) =
          ∫ x : Torus3,
            ∑ i : Fin 3, directorDivergenceIntegrand u P i j k x := by
        exact (integral_finsetSum Finset.univ
          (fun i _hi => hmiddle i j k)).symm
      _ = 0 := by
        have hzero : (fun x : Torus3 =>
            ∑ i : Fin 3, directorDivergenceIntegrand u P i j k x) = 0 := by
          funext x
          calc
            (∑ i : Fin 3, directorDivergenceIntegrand u P i j k x) =
                (u x j * P x j k) *
                  (∑ i : Fin 3, periodicSecondDerivative u i k i x) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _hi
              simp only [directorDivergenceIntegrand]
              ring
            _ = 0 := by rw [hdiv x k, mul_zero]
        rw [hzero]
        simp
  calc
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, directorMixedIntegrand u P i j k x) =
        ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          -(∫ x : Torus3,
            directorDivergenceIntegrand u P i j k x +
              directorErrorIntegrand u P i j k x) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcomponent i j k
    _ = -(∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ((∫ x : Torus3, directorDivergenceIntegrand u P i j k x) +
          (∫ x : Torus3, directorErrorIntegrand u P i j k x))) := by
      simp only [integral_add (hmiddle _ _ _) (herror _ _ _),
        Finset.sum_neg_distrib]
    _ = -(∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, directorErrorIntegrand u P i j k x) := by
      simp only [Finset.sum_add_distrib]
      simp_rw [hmiddleJK]
      simp

/-- Integrated tensor strain identity.  The director need only be symmetric and trace one; it
need not admit a globally oriented rank-one representative. -/
theorem integral_periodicDirectorStrainSq_eq_crossCurl_sub_error
    (u : Torus3 → Vec3) (P : DirectorTensorField)
    (hu : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y))
    (hP_slices : ∀ (i j k : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => P x j k) i y))
    (huFirst : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift (fun x => periodicFirstDerivative u k j x) i y))
    (hleft : ∀ i j k : Fin 3, Integrable (directorMixedIntegrand u P i j k))
    (herror : ∀ i j k : Fin 3, Integrable (directorErrorIntegrand u P i j k))
    (hmiddle : ∀ i j k : Fin 3,
      Integrable (directorDivergenceIntegrand u P i j k))
    (hdiv : ∀ (x : Torus3) (k : Fin 3),
      ∑ i : Fin 3, periodicSecondDerivative u i k i x = 0)
    (hsym : ∀ (x : Torus3) (j k : Fin 3), P x j k = P x k j)
    (htrace : ∀ x : Torus3, (∑ j : Fin 3, P x j j) = 1)
    (hcross : Integrable (fun x : Torus3 => periodicDirectorCrossCurlSq u P x)) :
    (∫ x : Torus3, periodicDirectorStrainSq u P x) =
      (∫ x : Torus3, periodicDirectorCrossCurlSq u P x) / 4 -
        (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, directorErrorIntegrand u P i j k x) := by
  have hmixed : Integrable (fun x : Torus3 => periodicDirectorMixed u P x) := by
    unfold periodicDirectorMixed
    exact integrable_finsetSum Finset.univ fun j _hj =>
      integrable_finsetSum Finset.univ fun k _hk =>
        integrable_finsetSum Finset.univ fun i _hi => hleft i j k
  have hmixedIntegral :
      (∫ x : Torus3, periodicDirectorMixed u P x) =
        ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, directorMixedIntegrand u P i j k x := by
    unfold periodicDirectorMixed
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _hj
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro k _hk
        rw [integral_finsetSum Finset.univ]
        intro i _hi
        exact hleft i j k
      · intro k _hk
        exact integrable_finsetSum Finset.univ fun i _hi => hleft i j k
    · intro j _hj
      exact integrable_finsetSum Finset.univ fun k _hk =>
        integrable_finsetSum Finset.univ fun i _hi => hleft i j k
  have hpairing := torus3_director_mixed_pairing_eq_error
    u P hu hP_slices huFirst hleft herror hmiddle hdiv
  calc
    (∫ x : Torus3, periodicDirectorStrainSq u P x) =
        ∫ x : Torus3,
          (periodicDirectorCrossCurlSq u P x / 4 + periodicDirectorMixed u P x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        periodicDirectorStrainSq_eq_crossCurl_add_mixed u P x (hsym x) (htrace x)
    _ = (∫ x : Torus3, periodicDirectorCrossCurlSq u P x / 4) +
        ∫ x : Torus3, periodicDirectorMixed u P x := by
      rw [integral_add (hcross.div_const 4) hmixed]
    _ = (∫ x : Torus3, periodicDirectorCrossCurlSq u P x) / 4 +
        ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, directorMixedIntegrand u P i j k x := by
      rw [integral_div, hmixedIntegral]
    _ = (∫ x : Torus3, periodicDirectorCrossCurlSq u P x) / 4 -
        (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, directorErrorIntegrand u P i j k x) := by
      rw [hpairing]
      ring

/-- A component director error is controlled by the concrete coordinate envelopes. -/
theorem abs_directorErrorIntegrand_le_gradientL1
    (u : Torus3 → Vec3) (P : DirectorTensorField)
    (i j k : Fin 3) (x : Torus3) :
    |directorErrorIntegrand u P i j k x| ≤
      ‖u x‖ * periodicGradientL1 u x * periodicDirectorGradientL1 P x := by
  rw [directorErrorIntegrand, abs_mul, abs_mul]
  calc
    |u x j| *
        (|periodicFirstDerivative u k i x| *
          |periodicDirectorDerivative P i j k x|) ≤
        ‖u x‖ *
          (periodicGradientL1 u x * periodicDirectorGradientL1 P x) := by
      apply mul_le_mul
      · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (u x) j
      · exact mul_le_mul
          (abs_periodicFirstDerivative_le_gradientL1 u k i x)
          (abs_periodicDirectorDerivative_le_gradientL1 P i j k x)
          (abs_nonneg _) (periodicGradientL1_nonneg u x)
      · positivity
      · positivity
    _ = ‖u x‖ * periodicGradientL1 u x *
        periodicDirectorGradientL1 P x := by ring

/-- The tensor formulation has only `3³ = 27` component errors, rather than the `54` terms
created by expanding `∂(e ⊗ e)` into two oriented-direction derivatives. -/
theorem abs_director_error_sum_le_gradientL1
    (u : Torus3 → Vec3) (P : DirectorTensorField)
    (hintegrable : Integrable (fun x : Torus3 =>
      ‖u x‖ * periodicGradientL1 u x * periodicDirectorGradientL1 P x)) :
    |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      ∫ x : Torus3, directorErrorIntegrand u P i j k x| ≤
      27 * ∫ x : Torus3,
        ‖u x‖ * periodicGradientL1 u x * periodicDirectorGradientL1 P x := by
  let density : Torus3 → ℝ := fun x =>
    ‖u x‖ * periodicGradientL1 u x * periodicDirectorGradientL1 P x
  have hcomponent : ∀ i j k : Fin 3,
      |∫ x : Torus3, directorErrorIntegrand u P i j k x| ≤
        ∫ x : Torus3, density x := by
    intro i j k
    have h := norm_integral_le_of_norm_le
      (f := directorErrorIntegrand u P i j k) (g := density) hintegrable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, density] using
          abs_directorErrorIntegrand_le_gradientL1 u P i j k x)
    simpa only [Real.norm_eq_abs] using h
  calc
    |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, directorErrorIntegrand u P i j k x| ≤
        ∑ j : Fin 3, |∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, directorErrorIntegrand u P i j k x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, |∑ i : Fin 3,
          ∫ x : Torus3, directorErrorIntegrand u P i j k x| := by
      apply Finset.sum_le_sum
      intro j _hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          |∫ x : Torus3, directorErrorIntegrand u P i j k x| := by
      apply Finset.sum_le_sum
      intro j _hj
      apply Finset.sum_le_sum
      intro k _hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, ∑ _i : Fin 3,
          ∫ x : Torus3, density x := by
      apply Finset.sum_le_sum
      intro j _hj
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro i _hi
      exact hcomponent i j k
    _ = 27 * ∫ x : Torus3, density x := by
      norm_num [Fin.sum_univ_succ]
      ring

/-- Integrating the complete error contraction before applying Cauchy--Schwarz removes the
spurious factor `27`. -/
theorem abs_director_error_sum_le_frobenius
    (u : Torus3 → Vec3) (P : DirectorTensorField)
    (herror : ∀ i j k : Fin 3, Integrable (directorErrorIntegrand u P i j k))
    (hintegrable : Integrable (periodicDirectorFrobeniusDebitDensity u P)) :
    |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      ∫ x : Torus3, directorErrorIntegrand u P i j k x| ≤
      ∫ x : Torus3, periodicDirectorFrobeniusDebitDensity u P x := by
  have hsumIntegral :
      (∫ x : Torus3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        directorErrorIntegrand u P i j k x) =
        ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, directorErrorIntegrand u P i j k x := by
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _hj
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro k _hk
        rw [integral_finsetSum Finset.univ]
        intro i _hi
        exact herror i j k
      · intro k _hk
        exact integrable_finsetSum Finset.univ fun i _hi => herror i j k
    · intro j _hj
      exact integrable_finsetSum Finset.univ fun k _hk =>
        integrable_finsetSum Finset.univ fun i _hi => herror i j k
  rw [← hsumIntegral]
  have h := norm_integral_le_of_norm_le
    (f := fun x : Torus3 => ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      directorErrorIntegrand u P i j k x)
    (g := periodicDirectorFrobeniusDebitDensity u P) hintegrable
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using
        abs_directorErrorDensity_le_frobenius u P x)
  simpa only [Real.norm_eq_abs] using h

/-- Named concrete hypotheses for the tensor ledger.  This is a predicate on supplied fields,
not a typeclass postulating a selector. -/
structure IsPeriodicDirectorPair
    (u : Torus3 → Vec3) (P : DirectorTensorField) : Prop where
  velocitySlices : ∀ (i j : Fin 3) (y : TorusCoordinateComplement),
    ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => u x j) i y)
  directorSlices : ∀ (i j k : Fin 3) (y : TorusCoordinateComplement),
    ContDiff ℝ 1 (torusCoordinateSliceLift (fun x => P x j k) i y)
  firstDerivativeSlices : ∀ (i k j : Fin 3) (y : TorusCoordinateComplement),
    ContDiff ℝ 1
      (torusCoordinateSliceLift (fun x => periodicFirstDerivative u k j x) i y)
  mixedIntegrable : ∀ i j k : Fin 3, Integrable (directorMixedIntegrand u P i j k)
  errorIntegrable : ∀ i j k : Fin 3, Integrable (directorErrorIntegrand u P i j k)
  divergenceIntegrable : ∀ i j k : Fin 3,
    Integrable (directorDivergenceIntegrand u P i j k)
  differentiatedDivergence : ∀ (x : Torus3) (k : Fin 3),
    ∑ i : Fin 3, periodicSecondDerivative u i k i x = 0
  symmetric : ∀ (x : Torus3) (j k : Fin 3), P x j k = P x k j
  traceOne : ∀ x : Torus3, (∑ j : Fin 3, P x j j) = 1
  strainNonneg : ∀ x : Torus3, 0 ≤ periodicDirectorStrainSq u P x
  crossNonneg : ∀ x : Torus3, 0 ≤ periodicDirectorCrossCurlSq u P x
  crossIntegrable : Integrable (fun x : Torus3 => periodicDirectorCrossCurlSq u P x)
  densityIntegrable : Integrable (fun x : Torus3 =>
    ‖u x‖ * periodicGradientL1 u x * periodicDirectorGradientL1 P x)

/-- The tensor bundle is nonvacuous: zero velocity and the constant rank-one coordinate
director satisfy every analytic and positivity field. -/
theorem constant_director_zero_velocity_isPeriodicDirectorPair :
    IsPeriodicDirectorPair (fun _ : Torus3 => (0 : Vec3))
      (rankOneDirector constantCoordinateDirection) := by
  constructor
  · intro i j y
    change ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ))
    exact contDiff_const
  · intro i j k y
    change ContDiff ℝ 1 (fun _ : ℝ =>
      constantCoordinateDirection default j * constantCoordinateDirection default k)
    exact contDiff_const
  · intro i k j y
    have hfun : (fun x : Torus3 =>
        periodicFirstDerivative (fun _ : Torus3 => (0 : Vec3)) k j x) =
        fun _ : Torus3 => (0 : ℝ) := by
      funext x
      simp
    rw [hfun]
    change ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ))
    exact contDiff_const
  · intro i j k
    have hfun : directorMixedIntegrand (fun _ : Torus3 => (0 : Vec3))
        (rankOneDirector constantCoordinateDirection) i j k =
        fun _ : Torus3 => (0 : ℝ) := by
      funext x
      simp [directorMixedIntegrand]
    rw [hfun]
    exact integrable_zero Torus3 ℝ volume
  · intro i j k
    have hfun : directorErrorIntegrand (fun _ : Torus3 => (0 : Vec3))
        (rankOneDirector constantCoordinateDirection) i j k =
        fun _ : Torus3 => (0 : ℝ) := by
      funext x
      simp [directorErrorIntegrand]
    rw [hfun]
    exact integrable_zero Torus3 ℝ volume
  · intro i j k
    have hfun : directorDivergenceIntegrand (fun _ : Torus3 => (0 : Vec3))
        (rankOneDirector constantCoordinateDirection) i j k =
        fun _ : Torus3 => (0 : ℝ) := by
      funext x
      simp [directorDivergenceIntegrand]
    rw [hfun]
    exact integrable_zero Torus3 ℝ volume
  · intro x k
    simp
  · exact fun x j k => rankOneDirector_symmetric constantCoordinateDirection x j k
  · intro x
    apply rankOneDirector_trace_eq_one
    simp [constantCoordinateDirection]
  · intro x
    rw [periodicDirectorStrainSq_rankOneDirector]
    positivity
  · intro x
    rw [periodicDirectorCrossCurlSq_rankOneDirector]
    positivity
  · have hfun : (fun x : Torus3 => periodicDirectorCrossCurlSq
        (fun _ : Torus3 => (0 : Vec3))
          (rankOneDirector constantCoordinateDirection) x) =
        fun _ : Torus3 => (0 : ℝ) := by
      funext x
      rw [periodicDirectorCrossCurlSq_rankOneDirector]
      simp [periodicCoordinateCurl, vec3Cross]
    rw [hfun]
    exact integrable_zero Torus3 ℝ volume
  · simp

/-- Concrete fourth-power tensor criterion.  Treating `P` as one unoriented object replaces
`2 · 54² = 5832` by `2 · 27² = 1458` in the coordinate-`ℓ¹` error bound. -/
theorem IsPeriodicDirectorPair.strain_fourth_le
    {u : Torus3 → Vec3} {P : DirectorTensorField}
    (h : IsPeriodicDirectorPair u P) :
    (∫ x : Torus3, periodicDirectorStrainSq u P x) ^ 2 ≤
      (∫ x : Torus3, periodicDirectorCrossCurlSq u P x) ^ 2 / 8 +
      1458 * (∫ x : Torus3,
        ‖u x‖ * periodicGradientL1 u x * periodicDirectorGradientL1 P x) ^ 2 := by
  let strainSq : ℝ := ∫ x : Torus3, periodicDirectorStrainSq u P x
  let crossSq : ℝ := ∫ x : Torus3, periodicDirectorCrossCurlSq u P x
  let density : Torus3 → ℝ := fun x =>
    ‖u x‖ * periodicGradientL1 u x * periodicDirectorGradientL1 P x
  let mixed : ℝ := 27 * ∫ x : Torus3, density x
  let errorSum : ℝ := ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
    ∫ x : Torus3, directorErrorIntegrand u P i j k x
  have hidentity := integral_periodicDirectorStrainSq_eq_crossCurl_sub_error
    u P h.velocitySlices h.directorSlices h.firstDerivativeSlices
      h.mixedIntegrable h.errorIntegrable h.divergenceIntegrable
      h.differentiatedDivergence h.symmetric h.traceOne h.crossIntegrable
  have herrorBound := abs_director_error_sum_le_gradientL1
    u P h.densityIntegrable
  have hstrain0 : 0 ≤ strainSq := by
    exact integral_nonneg_of_ae (Eventually.of_forall h.strainNonneg)
  have hcross0 : 0 ≤ crossSq := by
    exact integral_nonneg_of_ae (Eventually.of_forall h.crossNonneg)
  have hdensity0 : 0 ≤ ∫ x : Torus3, density x := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun x => by
      dsimp [density]
      exact mul_nonneg
        (mul_nonneg (norm_nonneg _) (periodicGradientL1_nonneg u x))
        (periodicDirectorGradientL1_nonneg P x)
  have hmixed0 : 0 ≤ mixed := by
    dsimp [mixed]
    positivity
  have hstrain : strainSq ≤ crossSq / 4 + mixed := by
    dsimp [strainSq, crossSq, mixed, errorSum, density] at hidentity herrorBound ⊢
    rw [hidentity]
    have hneg : - (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, directorErrorIntegrand u P i j k x) ≤
        |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, directorErrorIntegrand u P i j k x| := neg_le_abs _
    linarith
  have hfourth := variable_direction_strain_fourth_split
    hstrain0 hcross0 hmixed0 hstrain
  dsimp [strainSq, crossSq, mixed, density] at hfourth ⊢
  convert hfourth using 1
  all_goals ring

/-- Frobenius version of the concrete tensor criterion.  Treating the entire derivative error
as one finite-dimensional contraction improves the coefficient `1458 = 2 · 27²` to `2`. -/
theorem IsPeriodicDirectorPair.strain_fourth_le_frobenius
    {u : Torus3 → Vec3} {P : DirectorTensorField}
    (h : IsPeriodicDirectorPair u P)
    (hFrobenius : Integrable (periodicDirectorFrobeniusDebitDensity u P)) :
    (∫ x : Torus3, periodicDirectorStrainSq u P x) ^ 2 ≤
      (∫ x : Torus3, periodicDirectorCrossCurlSq u P x) ^ 2 / 8 +
      2 * (∫ x : Torus3, periodicDirectorFrobeniusDebitDensity u P x) ^ 2 := by
  let strainSq : ℝ := ∫ x : Torus3, periodicDirectorStrainSq u P x
  let crossSq : ℝ := ∫ x : Torus3, periodicDirectorCrossCurlSq u P x
  let density : Torus3 → ℝ := periodicDirectorFrobeniusDebitDensity u P
  let mixed : ℝ := ∫ x : Torus3, density x
  let errorSum : ℝ := ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
    ∫ x : Torus3, directorErrorIntegrand u P i j k x
  have hidentity := integral_periodicDirectorStrainSq_eq_crossCurl_sub_error
    u P h.velocitySlices h.directorSlices h.firstDerivativeSlices
      h.mixedIntegrable h.errorIntegrable h.divergenceIntegrable
      h.differentiatedDivergence h.symmetric h.traceOne h.crossIntegrable
  have herrorBound := abs_director_error_sum_le_frobenius
    u P h.errorIntegrable hFrobenius
  have hstrain0 : 0 ≤ strainSq := by
    exact integral_nonneg_of_ae (Eventually.of_forall h.strainNonneg)
  have hcross0 : 0 ≤ crossSq := by
    exact integral_nonneg_of_ae (Eventually.of_forall h.crossNonneg)
  have hdensity0 : 0 ≤ ∫ x : Torus3, density x := by
    apply integral_nonneg_of_ae
    exact Eventually.of_forall fun x => by
      dsimp [density, periodicDirectorFrobeniusDebitDensity]
      positivity
  have hmixed0 : 0 ≤ mixed := by
    exact hdensity0
  have hstrain : strainSq ≤ crossSq / 4 + mixed := by
    dsimp [strainSq, crossSq, mixed, errorSum, density] at hidentity herrorBound ⊢
    rw [hidentity]
    have hneg : - (∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x : Torus3, directorErrorIntegrand u P i j k x) ≤
        |∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ x : Torus3, directorErrorIntegrand u P i j k x| := neg_le_abs _
    linarith
  have hfourth := variable_direction_strain_fourth_split
    hstrain0 hcross0 hmixed0 hstrain
  dsimp [strainSq, crossSq, mixed, density] at hfourth ⊢
  exact hfourth

/-- One-time regularized-director ledger with every constant exposed.  The transverse charge
costs `c⁴/18` (times the squared torus volume), while the geometric error costs palinstrophy
times the nonsingular quotient. -/
theorem IsPeriodicDirectorPair.regularized_strain_fourth_le_quotient
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hpair : IsPeriodicDirectorPair u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c))
    (hcurl : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun z => periodicCoordinateCurl u z q) a y))
    (hpal : MemLp (fun x : Torus3 =>
      periodicGradientL1 (fun y => periodicCoordinateCurl u y) x) 2 volume)
    (hquot : MemLp
      (periodicRegularizedDirectorCauchyFactor u
        (fun y => periodicCoordinateCurl u y) c) 2 volume) :
    (∫ x : Torus3, periodicDirectorStrainSq u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 ≤
      c ^ 4 * volume.real (Set.univ : Set Torus3) ^ 2 / 18 +
        1889568 *
          (∫ x : Torus3,
            periodicGradientL1 (fun y => periodicCoordinateCurl u y) x ^ 2) *
          (∫ x : Torus3,
            periodicRegularizedDirectorQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) := by
  have hstrain := hpair.strain_fourth_le
  have hcross := periodicDirectorCrossFourth_regularized_le
    u c hc hpair.crossIntegrable
  have hmixed := sq_integral_regularizedDirector_mixed_le_quotient
    u (fun y => periodicCoordinateCurl u y) c hc hcurl
      hpair.densityIntegrable hpal hquot
  have hcrossScaled :
      (∫ x : Torus3, periodicDirectorCrossCurlSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 / 8 ≤
      (((2 : ℝ) / 3 * c ^ 2) * volume.real (Set.univ : Set Torus3)) ^ 2 / 8 :=
    div_le_div_of_nonneg_right hcross (by norm_num)
  have hmixedScaled := mul_le_mul_of_nonneg_left hmixed (by norm_num : (0 : ℝ) ≤ 1458)
  calc
    (∫ x : Torus3, periodicDirectorStrainSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 ≤
        (∫ x : Torus3, periodicDirectorCrossCurlSq u
          (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 / 8 +
          1458 * (∫ x : Torus3,
            ‖u x‖ * periodicGradientL1 u x *
              periodicDirectorGradientL1
                (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 :=
      hstrain
    _ ≤ (((2 : ℝ) / 3 * c ^ 2) *
          volume.real (Set.univ : Set Torus3)) ^ 2 / 8 +
        1458 * (1296 *
          (∫ x : Torus3,
            periodicGradientL1 (fun y => periodicCoordinateCurl u y) x ^ 2) *
          (∫ x : Torus3,
            periodicRegularizedDirectorQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x)) :=
      add_le_add hcrossScaled hmixedScaled
    _ = c ^ 4 * volume.real (Set.univ : Set Torus3) ^ 2 / 18 +
        1889568 *
          (∫ x : Torus3,
            periodicGradientL1 (fun y => periodicCoordinateCurl u y) x ^ 2) *
          (∫ x : Torus3,
            periodicRegularizedDirectorQuotientDensity u
      (fun y => periodicCoordinateCurl u y) c x) := by ring

/-- Cancellation-preserving version of the one-time regularized-director ledger.  The larger
explicit constant is the price of retaining a vorticity factor in the quotient; in return the
geometric charge vanishes on the vorticity zero set. -/
theorem IsPeriodicDirectorPair.regularized_strain_fourth_le_sharp_quotient
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hpair : IsPeriodicDirectorPair u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c))
    (hcurl : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun z => periodicCoordinateCurl u z q) a y))
    (hpal : MemLp (fun x : Torus3 =>
      periodicGradientL1 (fun y => periodicCoordinateCurl u y) x) 2 volume)
    (hquot : MemLp
      (periodicRegularizedDirectorSharpCauchyFactor u
        (fun y => periodicCoordinateCurl u y) c) 2 volume) :
    (∫ x : Torus3, periodicDirectorStrainSq u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 ≤
      c ^ 4 * volume.real (Set.univ : Set Torus3) ^ 2 / 18 +
        26572050 *
          (∫ x : Torus3,
            periodicGradientL1 (fun y => periodicCoordinateCurl u y) x ^ 2) *
          (∫ x : Torus3,
            periodicRegularizedDirectorSharpQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) := by
  have hstrain := hpair.strain_fourth_le
  have hcross := periodicDirectorCrossFourth_regularized_le
    u c hc hpair.crossIntegrable
  have hmixed := sq_integral_regularizedDirector_mixed_le_sharp_quotient
    u (fun y => periodicCoordinateCurl u y) c hc hcurl
      hpair.densityIntegrable hpal hquot
  have hcrossScaled :
      (∫ x : Torus3, periodicDirectorCrossCurlSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 / 8 ≤
      (((2 : ℝ) / 3 * c ^ 2) * volume.real (Set.univ : Set Torus3)) ^ 2 / 8 :=
    div_le_div_of_nonneg_right hcross (by norm_num)
  have hmixedScaled := mul_le_mul_of_nonneg_left hmixed (by norm_num : (0 : ℝ) ≤ 1458)
  calc
    (∫ x : Torus3, periodicDirectorStrainSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 ≤
        (∫ x : Torus3, periodicDirectorCrossCurlSq u
          (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 / 8 +
          1458 * (∫ x : Torus3,
            ‖u x‖ * periodicGradientL1 u x *
              periodicDirectorGradientL1
                (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 :=
      hstrain
    _ ≤ (((2 : ℝ) / 3 * c ^ 2) *
          volume.real (Set.univ : Set Torus3)) ^ 2 / 8 +
        1458 * (18225 *
          (∫ x : Torus3,
            periodicGradientL1 (fun y => periodicCoordinateCurl u y) x ^ 2) *
          (∫ x : Torus3,
            periodicRegularizedDirectorSharpQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x)) :=
      add_le_add hcrossScaled hmixedScaled
    _ = c ^ 4 * volume.real (Set.univ : Set Torus3) ^ 2 / 18 +
        26572050 *
          (∫ x : Torus3,
            periodicGradientL1 (fun y => periodicCoordinateCurl u y) x ^ 2) *
          (∫ x : Torus3,
            periodicRegularizedDirectorSharpQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) := by ring

/-- Frobenius/cancellation-preserving one-time director ledger.  The complete coefficient of
the palinstrophy--quotient product is `28/3`, replacing `1,889,568` in the coarse coordinate
ledger and `26,572,050` in the coordinatewise sharp ledger. -/
theorem IsPeriodicDirectorPair.regularized_strain_fourth_le_frobenius_quotient
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hpair : IsPeriodicDirectorPair u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c))
    (hcurl : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun z => periodicCoordinateCurl u z q) a y))
    (hFrobenius : Integrable (periodicDirectorFrobeniusDebitDensity u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c)))
    (hpal : MemLp (fun x : Torus3 => Real.sqrt
      (periodicGradientFrobeniusSq (fun y => periodicCoordinateCurl u y) x)) 2 volume)
    (hquot : MemLp
      (periodicRegularizedDirectorFrobeniusCauchyFactor u
        (fun y => periodicCoordinateCurl u y) c) 2 volume) :
    (∫ x : Torus3, periodicDirectorStrainSq u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 ≤
      c ^ 4 * volume.real (Set.univ : Set Torus3) ^ 2 / 18 +
        (28 / 3 : ℝ) *
          (∫ x : Torus3,
            periodicGradientFrobeniusSq
              (fun y => periodicCoordinateCurl u y) x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorFrobeniusQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) := by
  have hstrain := hpair.strain_fourth_le_frobenius hFrobenius
  have hcross := periodicDirectorCrossFourth_regularized_le
    u c hc hpair.crossIntegrable
  have hmixed := sq_integral_regularizedDirector_frobenius_mixed_le_quotient
    u (fun y => periodicCoordinateCurl u y) c hc hcurl
      hFrobenius hpal hquot
  have hcrossScaled :
      (∫ x : Torus3, periodicDirectorCrossCurlSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 / 8 ≤
      (((2 : ℝ) / 3 * c ^ 2) * volume.real (Set.univ : Set Torus3)) ^ 2 / 8 :=
    div_le_div_of_nonneg_right hcross (by norm_num)
  have hmixedScaled := mul_le_mul_of_nonneg_left hmixed (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (∫ x : Torus3, periodicDirectorStrainSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 ≤
        (∫ x : Torus3, periodicDirectorCrossCurlSq u
          (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 / 8 +
          2 * (∫ x : Torus3,
            periodicDirectorFrobeniusDebitDensity u
              (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 :=
      hstrain
    _ ≤ (((2 : ℝ) / 3 * c ^ 2) *
          volume.real (Set.univ : Set Torus3)) ^ 2 / 8 +
        2 * ((14 / 3 : ℝ) *
          (∫ x : Torus3,
            periodicGradientFrobeniusSq
              (fun y => periodicCoordinateCurl u y) x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorFrobeniusQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x)) :=
      add_le_add hcrossScaled hmixedScaled
    _ = c ^ 4 * volume.real (Set.univ : Set Torus3) ^ 2 / 18 +
        (28 / 3 : ℝ) *
          (∫ x : Torus3,
            periodicGradientFrobeniusSq
              (fun y => periodicCoordinateCurl u y) x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorFrobeniusQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) := by ring

/-- Exact angular/radial one-time director ledger.  Constant-direction vorticity has no
angular cost; changes of scalar amplitude are isolated in the faster-decaying radial
quotient. -/
theorem IsPeriodicDirectorPair.regularized_strain_fourth_le_direction_amplitude_quotients
    (u : Torus3 → Vec3) (c : ℝ) (hc : c ≠ 0)
    (hpair : IsPeriodicDirectorPair u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c))
    (hcurl : ∀ (a q : Fin 3) (y : TorusCoordinateComplement),
      ContDiff ℝ 1
        (torusCoordinateSliceLift
          (fun z => periodicCoordinateCurl u z q) a y))
    (hFrobenius : Integrable (periodicDirectorFrobeniusDebitDensity u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c)))
    (hdirection : MemLp (fun x : Torus3 => Real.sqrt
      (periodicVorticityDirectionDissipationSq
        (fun y => periodicCoordinateCurl u y) x)) 2 volume)
    (hdirectionQuotient : MemLp
      (periodicRegularizedDirectorDirectionCauchyFactor u
        (fun y => periodicCoordinateCurl u y) c) 2 volume)
    (hamplitude : MemLp (fun x : Torus3 => Real.sqrt
      (periodicVorticityAmplitudeDissipationSq
        (fun y => periodicCoordinateCurl u y) x)) 2 volume)
    (hamplitudeQuotient : MemLp
      (periodicRegularizedDirectorAmplitudeCauchyFactor u
        (fun y => periodicCoordinateCurl u y) c) 2 volume) :
    (∫ x : Torus3, periodicDirectorStrainSq u
      (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 ≤
      c ^ 4 * volume.real (Set.univ : Set Torus3) ^ 2 / 18 +
        8 * (∫ x : Torus3,
          periodicVorticityDirectionDissipationSq
            (fun y => periodicCoordinateCurl u y) x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorFrobeniusQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) +
        (32 / 3 : ℝ) * (∫ x : Torus3,
          periodicVorticityAmplitudeDissipationSq
            (fun y => periodicCoordinateCurl u y) x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorRadialQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) := by
  have hstrain := hpair.strain_fourth_le_frobenius hFrobenius
  have hcross := periodicDirectorCrossFourth_regularized_le
    u c hc hpair.crossIntegrable
  have hmixed :=
    sq_integral_regularizedDirector_frobenius_mixed_le_direction_amplitude_quotients
      u (fun y => periodicCoordinateCurl u y) c hc hcurl hFrobenius
        hdirection hdirectionQuotient hamplitude hamplitudeQuotient
  have hcrossScaled :
      (∫ x : Torus3, periodicDirectorCrossCurlSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 / 8 ≤
      (((2 : ℝ) / 3 * c ^ 2) * volume.real (Set.univ : Set Torus3)) ^ 2 / 8 :=
    div_le_div_of_nonneg_right hcross (by norm_num)
  have hmixedScaled := mul_le_mul_of_nonneg_left hmixed (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (∫ x : Torus3, periodicDirectorStrainSq u
        (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 ≤
        (∫ x : Torus3, periodicDirectorCrossCurlSq u
          (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 / 8 +
          2 * (∫ x : Torus3,
            periodicDirectorFrobeniusDebitDensity u
              (regularizedDirector (fun y => periodicCoordinateCurl u y) c) x) ^ 2 :=
      hstrain
    _ ≤ (((2 : ℝ) / 3 * c ^ 2) *
          volume.real (Set.univ : Set Torus3)) ^ 2 / 8 +
        2 * (4 * (∫ x : Torus3,
          periodicVorticityDirectionDissipationSq
            (fun y => periodicCoordinateCurl u y) x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorFrobeniusQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) +
        (16 / 3 : ℝ) * (∫ x : Torus3,
          periodicVorticityAmplitudeDissipationSq
            (fun y => periodicCoordinateCurl u y) x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorRadialQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x)) :=
      add_le_add hcrossScaled hmixedScaled
    _ = c ^ 4 * volume.real (Set.univ : Set Torus3) ^ 2 / 18 +
        8 * (∫ x : Torus3,
          periodicVorticityDirectionDissipationSq
            (fun y => periodicCoordinateCurl u y) x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorFrobeniusQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) +
        (32 / 3 : ℝ) * (∫ x : Torus3,
          periodicVorticityAmplitudeDissipationSq
            (fun y => periodicCoordinateCurl u y) x) *
          (∫ x : Torus3,
            periodicRegularizedDirectorRadialQuotientDensity u
              (fun y => periodicCoordinateCurl u y) c x) := by ring

/-- Spatial director-strain fourth power at one time. -/
def periodicDirectorStrainFourthAt
    (u : Torus3 → Vec3) (P : DirectorTensorField) : ℝ :=
  (∫ x : Torus3, periodicDirectorStrainSq u P x) ^ 2

/-- Spatial tensor transverse-vorticity fourth power at one time. -/
def periodicDirectorCrossFourthAt
    (u : Torus3 → Vec3) (P : DirectorTensorField) : ℝ :=
  (∫ x : Torus3, periodicDirectorCrossCurlSq u P x) ^ 2

/-- Square of the tensor-gradient mixed debit at one time. -/
def periodicDirectorMixedSqAt
    (u : Torus3 → Vec3) (P : DirectorTensorField) : ℝ :=
  (∫ x : Torus3,
    ‖u x‖ * periodicGradientL1 u x * periodicDirectorGradientL1 P x) ^ 2

/-- Time-integrated director-tensor handoff.  This accepts positive trace-one tensors directly,
without asking for a globally oriented square root. -/
theorem integrable_periodicDirectorStrainFourth_of_cross_and_mixed
    {τ : Type*} [MeasurableSpace τ] (μ : Measure τ)
    (u : τ → Torus3 → Vec3) (P : τ → DirectorTensorField)
    (hpair : ∀ t : τ, IsPeriodicDirectorPair (u t) (P t))
    (hstrainMeasurable : AEStronglyMeasurable
      (fun t => periodicDirectorStrainFourthAt (u t) (P t)) μ)
    (hcross : Integrable (fun t => periodicDirectorCrossFourthAt (u t) (P t)) μ)
    (hmixed : Integrable (fun t => periodicDirectorMixedSqAt (u t) (P t)) μ) :
    Integrable (fun t => periodicDirectorStrainFourthAt (u t) (P t)) μ := by
  have hright : Integrable (fun t =>
      (8 : ℝ)⁻¹ * periodicDirectorCrossFourthAt (u t) (P t) +
        1458 * periodicDirectorMixedSqAt (u t) (P t)) μ :=
    (hcross.const_mul (8 : ℝ)⁻¹).add (hmixed.const_mul 1458)
  apply hright.mono_nonneg hstrainMeasurable
  · exact Eventually.of_forall fun _ => sq_nonneg _
  · exact Eventually.of_forall fun t => by
      have h := (hpair t).strain_fourth_le
      dsimp [periodicDirectorStrainFourthAt, periodicDirectorCrossFourthAt,
        periodicDirectorMixedSqAt] at h ⊢
      nlinarith
