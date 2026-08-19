import Mathlib

/-!
# Far-field dyadic shell estimate

This file replaces the informal summation in Lemma 7.1(iv) of the manuscript by a finite,
checkable argument.  A shell `k` contains finitely many disjoint cells.  The squared coefficient
of one cell has the scaling

`ell^3 * (2^k * ell)^(-8) = ell^(-5) * 256^(-k)`.

If shell `k` has at most `c * 8^k` cells, its total squared coefficient is therefore bounded by
`c * ell^(-5) * 32^(-k)`.  Cauchy--Schwarz then combines this coefficient budget with the sum of
the squared local `L^2` norms.  The geometric constant is `32 / 31`; the manuscript's `4 / 3`
is a valid, but weaker, corollary.
-/

namespace NSFormal

open scoped BigOperators

/-- A cell is identified by its shell and by an index in that shell. -/
abbrev FarFieldCell {N : ℕ} (shellCount : Fin (N + 1) → ℕ) :=
  Σ k, Fin (shellCount k)

/-- The squared scalar coefficient of a cell, after factoring out the kernel constant.

`scale` represents `ell⁻⁵`.  The factor `256⁻ᵏ` is the square of the kernel decay
`(2ᵏ ell)⁻⁴`, after the cell-volume factor `ell³` has been included. -/
noncomputable def farFieldWeightSq {N : ℕ} {shellCount : Fin (N + 1) → ℕ}
    (scale : ℝ) (q : FarFieldCell shellCount) : ℝ :=
  scale * ((1 : ℝ) / 256) ^ q.1.val

/-- A finite geometric sum with ratio `1/32` is bounded by its infinite sum `32/31`. -/
theorem finite_shell_series_le (N : ℕ) :
    ∑ k : Fin (N + 1), ((1 : ℝ) / 32) ^ k.val ≤ (32 : ℝ) / 31 := by
  rw [Fin.sum_univ_eq_sum_range]
  have h := geom_sum_Ico_le_of_lt_one (K := ℝ) (m := 0) (n := N + 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 32) (by norm_num : (1 : ℝ) / 32 < 1)
  calc
    ∑ k ∈ Finset.range (N + 1), ((1 : ℝ) / 32) ^ k
        ≤ ((1 : ℝ) / 32) ^ 0 / (1 - (1 : ℝ) / 32) := by
          simpa only [Nat.Ico_zero_eq_range] using h
    _ = (32 : ℝ) / 31 := by norm_num

/-- The shell-count estimate gives the stronger squared-weight budget `c * scale * 32/31`.

The hypotheses are concrete numerical data: `shellCount k` is the number of cells in shell `k`,
and `scale` is the nonnegative dimensional factor (physically `ell⁻⁵`). -/
theorem sum_farFieldWeightSq_le {N : ℕ} (shellCount : Fin (N + 1) → ℕ)
    (scale c : ℝ) (hscale : 0 ≤ scale) (hc : 0 ≤ c)
    (hcount : ∀ k, (shellCount k : ℝ) ≤ c * 8 ^ k.val) :
    ∑ q : FarFieldCell shellCount, farFieldWeightSq scale q
      ≤ c * scale * ((32 : ℝ) / 31) := by
  rw [Fintype.sum_sigma]
  simp only [farFieldWeightSq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  calc
    ∑ k : Fin (N + 1), (shellCount k : ℝ) *
        (scale * ((1 : ℝ) / 256) ^ k.val)
        ≤ ∑ k : Fin (N + 1), (c * 8 ^ k.val) *
          (scale * ((1 : ℝ) / 256) ^ k.val) := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right (hcount k) (mul_nonneg hscale (by positivity))
    _ = ∑ k : Fin (N + 1), c * scale * ((1 : ℝ) / 32) ^ k.val := by
          apply Finset.sum_congr rfl
          intro k _
          have hk : (8 : ℝ) ^ k.val * ((1 : ℝ) / 256) ^ k.val
              = ((1 : ℝ) / 32) ^ k.val := by
            rw [← mul_pow]
            norm_num
          rw [← hk]
          ring
    _ = c * scale * ∑ k : Fin (N + 1), ((1 : ℝ) / 32) ^ k.val := by
          rw [Finset.mul_sum]
    _ ≤ c * scale * ((32 : ℝ) / 31) := by
          gcongr
          exact finite_shell_series_le N

/-- Finite Cauchy--Schwarz in the form needed for cellwise far-field contributions. -/
theorem farField_cauchy_schwarz {ι : Type*} [Fintype ι]
    (weightSq localL2 contribution : ι → ℝ) (C U W : ℝ)
    (hweight : ∀ i, 0 ≤ weightSq i) (_hlocal : ∀ i, 0 ≤ localL2 i)
    (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hcontribution : ∀ i, contribution i ≤ C * Real.sqrt (weightSq i) * localL2 i)
    (hweightsum : ∑ i, weightSq i ≤ W)
    (henergy : ∑ i, localL2 i ^ 2 ≤ U ^ 2) :
    ∑ i, contribution i ≤ C * Real.sqrt W * U := by
  calc
    ∑ i, contribution i
        ≤ ∑ i, C * Real.sqrt (weightSq i) * localL2 i :=
          Finset.sum_le_sum fun i _ ↦ hcontribution i
    _ = C * ∑ i, Real.sqrt (weightSq i) * localL2 i := by
          simp_rw [mul_assoc, ← Finset.mul_sum]
    _ ≤ C * (Real.sqrt (∑ i, (Real.sqrt (weightSq i)) ^ 2) *
          Real.sqrt (∑ i, localL2 i ^ 2)) := by
            gcongr
            exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
              (fun i ↦ Real.sqrt (weightSq i)) localL2
    _ = C * (Real.sqrt (∑ i, weightSq i) * Real.sqrt (∑ i, localL2 i ^ 2)) := by
          simp_rw [Real.sq_sqrt (hweight _)]
    _ ≤ C * (Real.sqrt W * Real.sqrt (U ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (Real.sqrt_le_sqrt hweightsum) (Real.sqrt_le_sqrt henergy)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hC
    _ = C * Real.sqrt W * U := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hU]; ring

/-- Strong far-field estimate: shell counting and the local `L²` energy budget imply the
constant `sqrt (c * scale * 32/31)`. -/
theorem farField_sum_le_strong {N : ℕ} (shellCount : Fin (N + 1) → ℕ)
    (localL2 contribution : FarFieldCell shellCount → ℝ) (scale c C U : ℝ)
    (hscale : 0 ≤ scale) (hc : 0 ≤ c) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hcount : ∀ k, (shellCount k : ℝ) ≤ c * 8 ^ k.val)
    (hlocal : ∀ q, 0 ≤ localL2 q)
    (hcontribution : ∀ q, contribution q ≤
      C * Real.sqrt (farFieldWeightSq scale q) * localL2 q)
    (henergy : ∑ q, localL2 q ^ 2 ≤ U ^ 2) :
    ∑ q, contribution q ≤
      C * Real.sqrt (c * scale * ((32 : ℝ) / 31)) * U := by
  apply farField_cauchy_schwarz
    (weightSq := farFieldWeightSq scale) (localL2 := localL2)
    (contribution := contribution) (C := C) (U := U)
    (W := c * scale * ((32 : ℝ) / 31))
  · intro q
    exact mul_nonneg hscale (by positivity)
  · exact hlocal
  · exact hC
  · exact hU
  · exact hcontribution
  · exact sum_farFieldWeightSq_le shellCount scale c hscale hc hcount
  · exact henergy

/-- Manuscript-shaped corollary.  The paper writes `4/3`; the stronger shell calculation above
gives `32/31`, and `32/31 ≤ 4/3`. -/
theorem farField_sum_le_four_thirds {N : ℕ} (shellCount : Fin (N + 1) → ℕ)
    (localL2 contribution : FarFieldCell shellCount → ℝ) (scale c C U : ℝ)
    (hscale : 0 ≤ scale) (hc : 0 ≤ c) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hcount : ∀ k, (shellCount k : ℝ) ≤ c * 8 ^ k.val)
    (hlocal : ∀ q, 0 ≤ localL2 q)
    (hcontribution : ∀ q, contribution q ≤
      C * Real.sqrt (farFieldWeightSq scale q) * localL2 q)
    (henergy : ∑ q, localL2 q ^ 2 ≤ U ^ 2) :
    ∑ q, contribution q ≤ C * Real.sqrt (c * scale * ((4 : ℝ) / 3)) * U := by
  refine (farField_sum_le_strong shellCount localL2 contribution scale c C U hscale hc hC hU
    hcount hlocal hcontribution henergy).trans ?_
  have hconstant : (32 : ℝ) / 31 ≤ 4 / 3 := by norm_num
  have hinside : c * scale * ((32 : ℝ) / 31) ≤ c * scale * ((4 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_left hconstant (mul_nonneg hc hscale)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinside) hC) hU

end NSFormal
