import Mathlib

/-!
# Finite-shell spectral flux identity

For shell transfers `transfer i` and shell weights `weight i`, Abel summation rewrites the
weighted transfer as differences of weights paired with cumulative forward fluxes.  When total
kinetic-energy transfer vanishes, this is the finite-shell algebra behind the identity expressing
nonlinear enstrophy production as wavenumber-weighted kinetic-energy flux.
-/

namespace NSFormal

open scoped BigOperators

/-- Transfer accumulated through shell `n`. -/
def cumulativeTransfer (transfer : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), transfer i

/-- Forward flux out of shells `0, ..., n`. -/
def forwardFlux (transfer : ℕ → ℝ) (n : ℕ) : ℝ :=
  -cumulativeTransfer transfer n

/-- Finite Abel summation for weighted shell transfers. -/
theorem finite_abel_transfer (weight transfer : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), weight i * transfer i =
      weight n * cumulativeTransfer transfer n +
        ∑ j ∈ Finset.range n,
          (weight j - weight (j + 1)) * cumulativeTransfer transfer j := by
  induction n with
  | zero => simp [cumulativeTransfer]
  | succ n ih =>
      simp only [Finset.sum_range_succ, cumulativeTransfer] at ih ⊢
      rw [ih]
      ring

/-- If the total transfer vanishes, weighted transfer is the sum of weight increments times
forward flux. -/
theorem weighted_transfer_eq_forwardFlux (weight transfer : ℕ → ℝ) (n : ℕ)
    (htotal : cumulativeTransfer transfer n = 0) :
    ∑ i ∈ Finset.range (n + 1), weight i * transfer i =
      ∑ j ∈ Finset.range n,
        (weight (j + 1) - weight j) * forwardFlux transfer j := by
  rw [finite_abel_transfer, htotal]
  simp only [mul_zero, zero_add, forwardFlux]
  apply Finset.sum_congr rfl
  intro j _
  ring_nf

/-- Nonnegative increasing shell weights and nonnegative forward fluxes give nonnegative
weighted transfer. -/
theorem weighted_transfer_nonneg_of_forwardFlux_nonneg (weight transfer : ℕ → ℝ) (n : ℕ)
    (htotal : cumulativeTransfer transfer n = 0)
    (hweight : ∀ j < n, weight j ≤ weight (j + 1))
    (hflux : ∀ j < n, 0 ≤ forwardFlux transfer j) :
    0 ≤ ∑ i ∈ Finset.range (n + 1), weight i * transfer i := by
  rw [weighted_transfer_eq_forwardFlux weight transfer n htotal]
  apply Finset.sum_nonneg
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  exact mul_nonneg (sub_nonneg.mpr (hweight j hjn)) (hflux j hjn)

/-- Mass above shell `j`, expressed as total mass through `n` minus cumulative mass through
`j`.  For `j < n` this is the algebraic high-frequency tail. -/
def tailMass (mass : ℕ → ℝ) (n j : ℕ) : ℝ :=
  cumulativeTransfer mass n - cumulativeTransfer mass j

/-- Shell-weight increments telescope. -/
theorem sum_weight_increments (weight : ℕ → ℝ) (n : ℕ) :
    weight 0 + ∑ j ∈ Finset.range n, (weight (j + 1) - weight j) = weight n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      linarith

/-- Finite layer-cake identity: a weighted shell mass is the base weight times total mass plus
weight increments paired with high-frequency tail masses. -/
theorem finite_tail_layer_cake (weight mass : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), weight i * mass i =
      weight 0 * cumulativeTransfer mass n +
        ∑ j ∈ Finset.range n,
          (weight (j + 1) - weight j) * tailMass mass n j := by
  rw [finite_abel_transfer]
  unfold tailMass
  have htail_expand :
      (∑ j ∈ Finset.range n, (weight (j + 1) - weight j) *
          (cumulativeTransfer mass n - cumulativeTransfer mass j)) =
        (∑ j ∈ Finset.range n, (weight (j + 1) - weight j)) *
            cumulativeTransfer mass n -
          ∑ j ∈ Finset.range n,
            (weight (j + 1) - weight j) * cumulativeTransfer mass j := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [htail_expand]
  have hleft :
      (∑ j ∈ Finset.range n,
          (weight j - weight (j + 1)) * cumulativeTransfer mass j) =
        -(∑ j ∈ Finset.range n,
          (weight (j + 1) - weight j) * cumulativeTransfer mass j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hleft]
  have htel : weight 0 + ∑ j ∈ Finset.range n,
      (weight (j + 1) - weight j) = weight n := sum_weight_increments weight n
  linear_combination -(cumulativeTransfer mass n) * htel

/-- Finite recurrence criterion.  If every final high-frequency tail is at most its initial
tail plus a one-sided variation charge, then increasing shell weights bound the final weighted
mass by the initial weighted mass plus the correspondingly weighted variation. -/
theorem finite_recurrence_weighted_bound (weight initial final variation : ℕ → ℝ) (n : ℕ)
    (hweight0 : weight 0 = 0)
    (hweight : ∀ j < n, weight j ≤ weight (j + 1))
    (htail : ∀ j < n,
      tailMass final n j ≤ tailMass initial n j + variation j) :
    ∑ i ∈ Finset.range (n + 1), weight i * final i ≤
      ∑ i ∈ Finset.range (n + 1), weight i * initial i +
        ∑ j ∈ Finset.range n,
          (weight (j + 1) - weight j) * variation j := by
  rw [finite_tail_layer_cake, finite_tail_layer_cake, hweight0]
  simp only [zero_mul, zero_add]
  calc
    ∑ j ∈ Finset.range n, (weight (j + 1) - weight j) * tailMass final n j ≤
        ∑ j ∈ Finset.range n,
          (weight (j + 1) - weight j) * (tailMass initial n j + variation j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      exact mul_le_mul_of_nonneg_left (htail j hjn) (sub_nonneg.mpr (hweight j hjn))
    _ = ∑ j ∈ Finset.range n,
          (weight (j + 1) - weight j) * tailMass initial n j +
        ∑ j ∈ Finset.range n,
          (weight (j + 1) - weight j) * variation j := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]

/-- The bang--bang selector for a positive tail intake. -/
noncomputable def positiveSelector (x : ℝ) : ℝ :=
  if 0 < x then 1 else 0

theorem positiveSelector_nonneg (x : ℝ) : 0 ≤ positiveSelector x := by
  simp only [positiveSelector]
  split_ifs <;> norm_num

theorem positiveSelector_le_one (x : ℝ) : positiveSelector x ≤ 1 := by
  simp only [positiveSelector]
  split_ifs <;> norm_num

theorem positiveSelector_mul (x : ℝ) : positiveSelector x * x = max x 0 := by
  simp only [positiveSelector]
  split_ifs with hx
  · simp [max_eq_left hx.le]
  · simp [max_eq_right (le_of_not_gt hx)]

theorem positiveSelector_eq_one_iff (x : ℝ) : positiveSelector x = 1 ↔ 0 < x := by
  simp [positiveSelector]

/-- The monotone spectral multiplier whose increment is switched on exactly at cutoffs with
positive net high-tail intake.  Its increments are bounded by those of `weight`. -/
noncomputable def selectedTailWeight (weight net : ℕ → ℝ) (n i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i,
    (weight (j + 1) - weight j) * positiveSelector (tailMass net n j)

@[simp] theorem selectedTailWeight_zero (weight net : ℕ → ℝ) (n : ℕ) :
    selectedTailWeight weight net n 0 = 0 := by
  simp [selectedTailWeight]

theorem selectedTailWeight_increment (weight net : ℕ → ℝ) (n j : ℕ) :
    selectedTailWeight weight net n (j + 1) - selectedTailWeight weight net n j =
      (weight (j + 1) - weight j) * positiveSelector (tailMass net n j) := by
  simp [selectedTailWeight, Finset.sum_range_succ]

theorem selectedTailWeight_increment_bounds (weight net : ℕ → ℝ) (n j : ℕ)
    (hweight : weight j ≤ weight (j + 1)) :
    0 ≤ selectedTailWeight weight net n (j + 1) - selectedTailWeight weight net n j ∧
      selectedTailWeight weight net n (j + 1) - selectedTailWeight weight net n j ≤
        weight (j + 1) - weight j := by
  rw [selectedTailWeight_increment]
  have hΔ : 0 ≤ weight (j + 1) - weight j := sub_nonneg.mpr hweight
  constructor
  · exact mul_nonneg hΔ (positiveSelector_nonneg _)
  · calc
      (weight (j + 1) - weight j) * positiveSelector (tailMass net n j) ≤
          (weight (j + 1) - weight j) * 1 :=
        mul_le_mul_of_nonneg_left (positiveSelector_le_one _) hΔ
      _ = weight (j + 1) - weight j := mul_one _

theorem selectedTailWeight_nonneg (weight net : ℕ → ℝ) (n i : ℕ)
    (hweight : ∀ j < i, weight j ≤ weight (j + 1)) :
    0 ≤ selectedTailWeight weight net n i := by
  apply Finset.sum_nonneg
  intro j hj
  have hji : j < i := Finset.mem_range.mp hj
  exact mul_nonneg (sub_nonneg.mpr (hweight j hji)) (positiveSelector_nonneg _)

/-- Exact selector duality.  The weighted sum of positive high-tail intakes is a signed modal
pairing against one monotone bang--bang multiplier.  This is the finite-shell form of the
signed-work target: no absolute value is taken on the modal input. -/
theorem selectedTailWeight_pairing_eq_positive_tails
    (weight net : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), selectedTailWeight weight net n i * net i =
      ∑ j ∈ Finset.range n,
        (weight (j + 1) - weight j) * max (tailMass net n j) 0 := by
  rw [finite_tail_layer_cake, selectedTailWeight_zero]
  simp only [zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [selectedTailWeight_increment, mul_assoc, positiveSelector_mul]

/-- Selector duality is maximal: every spectral multiplier starting at zero whose increments
lie between zero and those of `weight` has no larger signed pairing. -/
theorem subweight_pairing_le_positive_tails
    (weight multiplier net : ℕ → ℝ) (n : ℕ)
    (hzero : multiplier 0 = 0)
    (hincrement_nonneg : ∀ j < n, 0 ≤ multiplier (j + 1) - multiplier j)
    (hincrement_le : ∀ j < n,
      multiplier (j + 1) - multiplier j ≤ weight (j + 1) - weight j) :
    ∑ i ∈ Finset.range (n + 1), multiplier i * net i ≤
      ∑ j ∈ Finset.range n,
        (weight (j + 1) - weight j) * max (tailMass net n j) 0 := by
  rw [finite_tail_layer_cake, hzero]
  simp only [zero_mul, zero_add]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  by_cases htail : 0 ≤ tailMass net n j
  · rw [max_eq_left htail]
    exact mul_le_mul_of_nonneg_right (hincrement_le j hjn) htail
  · have htail' : tailMass net n j ≤ 0 := le_of_not_ge htail
    rw [max_eq_right htail', mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (hincrement_nonneg j hjn) htail'

/-- Tail mass commutes with subtracting a modal dissipation profile. -/
theorem tailMass_sub (transfer dissipation : ℕ → ℝ) (n j : ℕ) :
    tailMass (fun i => transfer i - dissipation i) n j =
      tailMass transfer n j - tailMass dissipation n j := by
  simp only [tailMass, cumulativeTransfer, Finset.sum_sub_distrib]
  ring

/-- For conservative transfer, its high-tail mass is exactly the forward sharp flux. -/
theorem tailMass_eq_forwardFlux (transfer : ℕ → ℝ) (n j : ℕ)
    (htotal : cumulativeTransfer transfer n = 0) :
    tailMass transfer n j = forwardFlux transfer j := by
  rw [tailMass, htotal, zero_sub]
  rfl

/-- Thus the net transfer-minus-dissipation tail is precisely forward flux minus tail
dissipation.  The selector turns on exactly where forward transfer beats viscosity. -/
theorem net_tailMass_eq_flux_sub_dissipation
    (transfer dissipation : ℕ → ℝ) (n j : ℕ)
    (htotal : cumulativeTransfer transfer n = 0) :
    tailMass (fun i => transfer i - dissipation i) n j =
      forwardFlux transfer j - tailMass dissipation n j := by
  rw [tailMass_sub, tailMass_eq_forwardFlux transfer n j htotal]

/-- Exact signed-work form of positive high-tail intake.  The selector pairing equals selected
forward nonlinear flux minus the modal dissipation paid by the same multiplier. -/
theorem weighted_positive_net_tails_eq_selected_flux_sub_dissipation
    (weight transfer dissipation : ℕ → ℝ) (n : ℕ)
    (htotal : cumulativeTransfer transfer n = 0) :
    ∑ j ∈ Finset.range n, (weight (j + 1) - weight j) *
        max (tailMass (fun i => transfer i - dissipation i) n j) 0 =
      (∑ j ∈ Finset.range n, (weight (j + 1) - weight j) *
        positiveSelector (tailMass (fun i => transfer i - dissipation i) n j) *
          forwardFlux transfer j) -
      ∑ i ∈ Finset.range (n + 1),
        selectedTailWeight weight (fun i => transfer i - dissipation i) n i *
          dissipation i := by
  let net : ℕ → ℝ := fun i => transfer i - dissipation i
  let selected : ℕ → ℝ := selectedTailWeight weight net n
  rw [← selectedTailWeight_pairing_eq_positive_tails weight net n]
  calc
    ∑ i ∈ Finset.range (n + 1), selected i * net i =
        (∑ i ∈ Finset.range (n + 1), selected i * transfer i) -
          ∑ i ∈ Finset.range (n + 1), selected i * dissipation i := by
      simp only [net, mul_sub, Finset.sum_sub_distrib]
    _ = (∑ j ∈ Finset.range n,
          (selected (j + 1) - selected j) * forwardFlux transfer j) -
          ∑ i ∈ Finset.range (n + 1), selected i * dissipation i := by
      rw [weighted_transfer_eq_forwardFlux selected transfer n htotal]
    _ = (∑ j ∈ Finset.range n, (weight (j + 1) - weight j) *
          positiveSelector (tailMass (fun i => transfer i - dissipation i) n j) *
            forwardFlux transfer j) -
          ∑ i ∈ Finset.range (n + 1),
            selectedTailWeight weight (fun i => transfer i - dissipation i) n i *
              dissipation i := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      rw [selectedTailWeight_increment]

/-- Positive weighted high-tail intake after modal dissipation is bounded by nonlinear work
against the selected monotone multiplier.  The right side retains the signed forward flux and
charges only cutoffs where the *net* tail is increasing. -/
theorem weighted_positive_net_tails_le_selected_flux
    (weight transfer dissipation : ℕ → ℝ) (n : ℕ)
    (htotal : cumulativeTransfer transfer n = 0)
    (hweight : ∀ j < n, weight j ≤ weight (j + 1))
    (hdissipation : ∀ i ≤ n, 0 ≤ dissipation i) :
    ∑ j ∈ Finset.range n, (weight (j + 1) - weight j) *
        max (tailMass (fun i => transfer i - dissipation i) n j) 0 ≤
      ∑ j ∈ Finset.range n, (weight (j + 1) - weight j) *
        positiveSelector (tailMass (fun i => transfer i - dissipation i) n j) *
          forwardFlux transfer j := by
  let net : ℕ → ℝ := fun i => transfer i - dissipation i
  let selected : ℕ → ℝ := selectedTailWeight weight net n
  rw [← selectedTailWeight_pairing_eq_positive_tails weight net n]
  calc
    ∑ i ∈ Finset.range (n + 1), selected i * net i =
        (∑ i ∈ Finset.range (n + 1), selected i * transfer i) -
          ∑ i ∈ Finset.range (n + 1), selected i * dissipation i := by
      simp only [net, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.range (n + 1), selected i * transfer i := by
      apply sub_le_self
      apply Finset.sum_nonneg
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      apply mul_nonneg
      · apply selectedTailWeight_nonneg
        intro j hji
        exact hweight j (lt_of_lt_of_le hji hin)
      · exact hdissipation i hin
    _ = ∑ j ∈ Finset.range n,
        (selected (j + 1) - selected j) * forwardFlux transfer j :=
      weighted_transfer_eq_forwardFlux selected transfer n htotal
    _ = ∑ j ∈ Finset.range n, (weight (j + 1) - weight j) *
        positiveSelector (tailMass (fun i => transfer i - dissipation i) n j) *
          forwardFlux transfer j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [selectedTailWeight_increment]

/-- Nonlinear energy transfer measured through a heat filter with scale parameter `s`.
The multiplier in the filtered energy is `exp (-2 * s * weight i)`. -/
noncomputable def heatFilteredTransfer (weight transfer : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), Real.exp (-2 * s * weight i) * transfer i

/-- Forward heat-filtered kinetic-energy flux. -/
noncomputable def heatFilteredFlux (weight transfer : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    -(Real.exp (-2 * s * weight i) * transfer i)

/-- The pointwise-sum definition of heat-filtered flux agrees with minus filtered transfer. -/
theorem heatFilteredFlux_eq_neg_transfer (weight transfer : ℕ → ℝ) (n : ℕ) (s : ℝ) :
    heatFilteredFlux weight transfer n s = -heatFilteredTransfer weight transfer n s := by
  unfold heatFilteredFlux heatFilteredTransfer
  rw [Finset.sum_neg_distrib]

/-- Under zero total transfer, heat-filtered flux is a weighted average of the sharp forward
shell fluxes. -/
theorem heatFilteredFlux_eq_forwardFlux_average (weight transfer : ℕ → ℝ) (n : ℕ) (s : ℝ)
    (htotal : cumulativeTransfer transfer n = 0) :
    heatFilteredFlux weight transfer n s =
      ∑ j ∈ Finset.range n,
        (Real.exp (-2 * s * weight j) - Real.exp (-2 * s * weight (j + 1))) *
          forwardFlux transfer j := by
  rw [heatFilteredFlux_eq_neg_transfer]
  have hab := weighted_transfer_eq_forwardFlux
    (fun i => Real.exp (-2 * s * weight i)) transfer n htotal
  unfold heatFilteredTransfer
  rw [hab, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- For nonnegative scale, increasing shell weights and forward shell flux make the
heat-filtered flux nonnegative. -/
theorem heatFilteredFlux_nonneg_of_forwardFlux_nonneg (weight transfer : ℕ → ℝ)
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (htotal : cumulativeTransfer transfer n = 0)
    (hweight : ∀ j < n, weight j ≤ weight (j + 1))
    (hflux : ∀ j < n, 0 ≤ forwardFlux transfer j) :
    0 ≤ heatFilteredFlux weight transfer n s := by
  rw [heatFilteredFlux_eq_forwardFlux_average weight transfer n s htotal]
  apply Finset.sum_nonneg
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  apply mul_nonneg _ (hflux j hjn)
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith [hweight j hjn]

/-- Heat-filtered weighted transfer, corresponding to filtered nonlinear enstrophy
production when `weight i` is squared wavenumber. -/
noncomputable def heatWeightedTransfer (weight transfer : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    weight i * Real.exp (-2 * s * weight i) * transfer i

/-- The scale derivative of forward heat-filtered energy flux is twice the heat-filtered
weighted transfer.  For squared-wavenumber weights this is the exact finite-mode identity
`∂ₛ Πₛ = 2 Bₛ`, where `Bₛ` is nonlinear filtered enstrophy production. -/
theorem heatFilteredFlux_hasDerivAt (weight transfer : ℕ → ℝ) (n : ℕ) (s : ℝ) :
    HasDerivAt (heatFilteredFlux weight transfer n)
      (2 * heatWeightedTransfer weight transfer n s) s := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      HasDerivAt (fun r : ℝ => -(Real.exp (-2 * r * weight i) * transfer i))
        (2 * weight i * Real.exp (-2 * s * weight i) * transfer i) s := by
    intro i _
    have hinner := ((hasDerivAt_id s).const_mul (-2)).mul_const (weight i)
    change HasDerivAt (-(fun r : ℝ =>
      Real.exp (-2 * r * weight i) * transfer i))
        (2 * weight i * Real.exp (-2 * s * weight i) * transfer i) s
    apply (hinner.exp.mul_const (transfer i)).neg.congr_deriv
    simp only [id_eq]
    ring
  have hsum := HasDerivAt.fun_sum hterm
  unfold heatFilteredFlux heatWeightedTransfer
  apply hsum.congr_deriv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Algebraic form of the moving-heat-filter balance.  If `∂ₛY = -2Z`, then adding the
scale velocity `speed * ∂ₛY` changes the dissipation coefficient from `2ν` to
`2(ν + speed)` without changing the right-hand side. -/
theorem moving_heat_filter_balance (dtY dsY Z rhs ν speed : ℝ)
    (hfixed : dtY + 2 * ν * Z = rhs) (hscale : dsY = -2 * Z) :
    dtY + speed * dsY + 2 * (ν + speed) * Z = rhs := by
  rw [hscale]
  calc
    dtY + speed * (-2 * Z) + 2 * (ν + speed) * Z = dtY + 2 * ν * Z := by ring
    _ = rhs := hfixed

/-- A heat-filter scale which shrinks no faster than `ν / 2` retains at least the original
coefficient `ν` in front of the filtered palinstrophy. -/
theorem moving_heat_filter_retains_viscosity (ν speed : ℝ)
    (hspeed : -ν / 2 ≤ speed) :
    ν ≤ 2 * (ν + speed) := by
  linarith

/-- A conservative two-shell transfer: energy leaves shell `0` and enters shell `1`. -/
def twoShellTransfer (amplitude : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then -amplitude else if i = 1 then amplitude else 0

/-- Two shell weights `a` and `2a`. -/
def twoShellWeight (a : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then a else if i = 1 then 2 * a else 0

/-- The two-shell cascade pair conserves total nonlinear kinetic energy. -/
theorem twoShellTransfer_total (amplitude : ℝ) :
    cumulativeTransfer (twoShellTransfer amplitude) 1 = 0 := by
  simp only [cumulativeTransfer, Finset.sum_range_succ, Finset.sum_range_zero,
    twoShellTransfer]
  norm_num

/-- Its sharp forward flux between the two shells is exactly its amplitude. -/
theorem twoShellTransfer_forwardFlux (amplitude : ℝ) :
    forwardFlux (twoShellTransfer amplitude) 0 = amplitude := by
  simp [forwardFlux, cumulativeTransfer, twoShellTransfer]

/-- The heat-filtered flux of a two-shell cascade pair is one positive scale bump. -/
theorem twoShell_heatFilteredFlux (amplitude a s : ℝ) :
    heatFilteredFlux (twoShellWeight a) (twoShellTransfer amplitude) 1 s =
      amplitude * (Real.exp (-2 * a * s) - Real.exp (-4 * a * s)) := by
  simp only [heatFilteredFlux, Finset.sum_range_succ, Finset.sum_range_zero,
    twoShellWeight, twoShellTransfer]
  norm_num
  ring_nf

/-- A nonnegative two-shell amplitude gives nonnegative sharp forward flux. -/
theorem twoShellTransfer_forwardFlux_nonneg (amplitude : ℝ) (h : 0 ≤ amplitude) :
    0 ≤ forwardFlux (twoShellTransfer amplitude) 0 := by
  rw [twoShellTransfer_forwardFlux]
  exact h

/-- The three-shell transfer signature of the explicit planar triad in `DYNAMICS.md`:
the squared-wavenumber shells `1, 2, 5` receive `-3A, 4A, -A`. -/
def planarTriadTransfer (amplitude : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then -3 * amplitude
  else if i = 1 then 4 * amplitude
  else if i = 2 then -amplitude
  else 0

/-- Squared-wavenumber weights of the explicit planar triad. -/
def planarTriadWeight (i : ℕ) : ℝ :=
  if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 5 else 0

/-- The planar triad transfer conserves total kinetic energy. -/
theorem planarTriadTransfer_total (amplitude : ℝ) :
    cumulativeTransfer (planarTriadTransfer amplitude) 2 = 0 := by
  simp only [cumulativeTransfer, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [planarTriadTransfer]
  ring_nf

/-- Its heat-filtered flux is the exact three-exponential profile computed from the smooth
two-dimensional torus field in `DYNAMICS.md`. -/
theorem planarTriad_heatFilteredFlux (amplitude s : ℝ) :
    heatFilteredFlux planarTriadWeight (planarTriadTransfer amplitude) 2 s =
      amplitude *
        (3 * Real.exp (-2 * s) - 4 * Real.exp (-4 * s) + Real.exp (-10 * s)) := by
  simp only [heatFilteredFlux, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [planarTriadWeight, planarTriadTransfer]
  ring_nf

/-- At zero heat scale the conservative planar-triad flux vanishes. -/
theorem planarTriad_heatFilteredFlux_zero (amplitude : ℝ) :
    heatFilteredFlux planarTriadWeight (planarTriadTransfer amplitude) 2 0 = 0 := by
  rw [planarTriad_heatFilteredFlux]
  norm_num

/-- The scalar heat kernel of the planar triad is nonnegative at every real scale.  Algebraically
it is `q * (q - 1)² * (q² + 2q + 3)` with `q = exp (-2s)`. -/
theorem planarTriad_heatKernel_nonneg (s : ℝ) :
    0 ≤ 3 * Real.exp (-2 * s) - 4 * Real.exp (-4 * s) + Real.exp (-10 * s) := by
  let q := Real.exp (-2 * s)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have h4 : Real.exp (-4 * s) = q ^ 2 := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h10 : Real.exp (-10 * s) = q ^ 5 := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h4, h10]
  have hfactor :
      3 * q - 4 * q ^ 2 + q ^ 5 = q * (q - 1) ^ 2 * (q ^ 2 + 2 * q + 3) := by
    ring
  rw [hfactor]
  positivity

/-- At every positive heat scale the planar-triad heat kernel is strictly positive. -/
theorem planarTriad_heatKernel_pos (s : ℝ) (hs : 0 < s) :
    0 < 3 * Real.exp (-2 * s) - 4 * Real.exp (-4 * s) + Real.exp (-10 * s) := by
  let q := Real.exp (-2 * s)
  have hq : 0 < q := Real.exp_pos _
  have hneg : -2 * s < 0 := by linarith
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr hneg
  have h4 : Real.exp (-4 * s) = q ^ 2 := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h10 : Real.exp (-10 * s) = q ^ 5 := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h4, h10]
  have hfactor :
      3 * q - 4 * q ^ 2 + q ^ 5 = q * (q - 1) ^ 2 * (q ^ 2 + 2 * q + 3) := by
    ring
  rw [hfactor]
  exact mul_pos (mul_pos hq (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hq1))))
    (by nlinarith [sq_nonneg q])

/-- A nonnegative amplitude gives nonnegative heat-filtered flux for the planar triad. -/
theorem planarTriad_heatFilteredFlux_nonneg (amplitude s : ℝ) (hA : 0 ≤ amplitude) :
    0 ≤ heatFilteredFlux planarTriadWeight (planarTriadTransfer amplitude) 2 s := by
  rw [planarTriad_heatFilteredFlux]
  exact mul_nonneg hA (planarTriad_heatKernel_nonneg s)

/-- A positive amplitude and positive heat scale give strictly positive planar-triad flux. -/
theorem planarTriad_heatFilteredFlux_pos (amplitude s : ℝ)
    (hA : 0 < amplitude) (hs : 0 < s) :
    0 < heatFilteredFlux planarTriadWeight (planarTriadTransfer amplitude) 2 s := by
  rw [planarTriad_heatFilteredFlux]
  exact mul_pos hA (planarTriad_heatKernel_pos s hs)

end NSFormal
