import Mathlib

/-!
# Vorticity magnitude evolution

This file formalizes the pointwise inner-product calculation that is required before
using a maximum principle for viscous vorticity.  It deliberately retains the
viscous pairing; that term does not vanish along a general fluid trajectory.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- Half the squared vorticity magnitude.  Unlike `‖w‖`, this quantity is
differentiable at `w = 0` and is therefore the natural scalar for a maximum
principle. -/
def vorticityEnergy (w : E) : ℝ := ‖w‖ ^ 2 / 2

@[simp]
theorem vorticityEnergy_nonneg (w : E) : 0 ≤ vorticityEnergy w := by
  unfold vorticityEnergy
  positivity

variable [InnerProductSpace ℝ E]

/-- The derivative of half the squared norm has no nonvanishing hypothesis. -/
theorem hasDerivAt_vorticityEnergy
    {w : ℝ → E} {w' : E} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => vorticityEnergy (w s)) (inner ℝ (w t) w') t := by
  have h := hw.norm_sq.const_mul (2 : ℝ)⁻¹
  simpa [vorticityEnergy, div_eq_mul_inv, mul_comm] using h

/-- Correct pointwise evolution of half the squared vorticity.  The transport
vector is written separately so that its scalar pairing can later be shown to
vanish at a spatial maximum. -/
theorem hasDerivAt_vorticityEnergy_evolution
    {w : ℝ → E} {t ν : ℝ} (S : E →L[ℝ] E) (lapW transportW : E)
    (hw : HasDerivAt w (S (w t) + ν • lapW - transportW) t) :
    HasDerivAt (fun s => vorticityEnergy (w s))
      (inner ℝ (w t) (S (w t)) + ν * inner ℝ (w t) lapW -
        inner ℝ (w t) transportW) t := by
  convert hasDerivAt_vorticityEnergy hw using 1
  rw [inner_sub_right, inner_add_right, real_inner_smul_right]

/-- Second derivative of half the squared norm.  This is the one-dimensional
product rule behind `⟪ω, Δω⟫ = Δ(|ω|²/2) - |∇ω|²`. -/
theorem iteratedDeriv_two_vorticityEnergy
    {w : ℝ → E} (hw : ContDiff ℝ 2 w) (t : ℝ) :
    iteratedDeriv 2 (fun s => vorticityEnergy (w s)) t =
      inner ℝ (w t) (iteratedDeriv 2 w t) + ‖deriv w t‖ ^ 2 := by
  have hw_diff : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hwd_diff : Differentiable ℝ (deriv w) := by
    simpa only [iteratedDeriv_one] using
      (contDiff_iff_iteratedDeriv.mp hw).2 1 (by norm_num)
  have hqderiv : deriv (fun s => vorticityEnergy (w s)) =
      fun s => inner ℝ (w s) (deriv w s) := by
    funext s
    exact (hasDerivAt_vorticityEnergy (hw_diff s).hasDerivAt).deriv
  have hproduct := (hw_diff t).hasDerivAt.inner ℝ (hwd_diff t).hasDerivAt
  have hqsecond : iteratedDeriv 2 (fun s => vorticityEnergy (w s)) =
      deriv (deriv (fun s => vorticityEnergy (w s))) := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hwsecond : iteratedDeriv 2 w = deriv (deriv w) := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [congrFun hqsecond t, hqderiv, congrFun hwsecond t]
  convert hproduct.deriv using 1
  rw [real_inner_self_eq_norm_sq]

/-- The unit direction of a nonzero vector.  Its value at zero is harmless because
all evolution theorems below assume nonvanishing vorticity. -/
def unitDirection (w : E) : E := ‖w‖⁻¹ • w

/-- Stretching in the direction of `w`. -/
def stretchingRate (S : E →L[ℝ] E) (w : E) : ℝ :=
  inner ℝ (unitDirection w) (S (unitDirection w))

/-- The full normalized viscous damping in the vorticity-magnitude equation.

At a spatial maximum of `‖w‖`, the pairing `⟪ξ, Δw⟫` is nonpositive, so this
quantity is nonnegative.  Keeping it intact retains both curvature of the
magnitude peak and variation of the vorticity direction. -/
def normalizedViscousDamping (ν : ℝ) (w lapW : E) : ℝ :=
  -(ν * inner ℝ (unitDirection w) lapW) / ‖w‖

/-- Favorable sign of the full normalized viscous damping. -/
theorem normalizedViscousDamping_nonneg {ν : ℝ} {w lapW : E}
    (hν : 0 ≤ ν) (hvisc : inner ℝ (unitDirection w) lapW ≤ 0) :
    0 ≤ normalizedViscousDamping ν w lapW := by
  unfold normalizedViscousDamping
  exact div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hν hvisc)) (norm_nonneg w)

theorem norm_smul_unitDirection {w : E} (hw : w ≠ 0) : ‖w‖ • unitDirection w = w := by
  simp only [unitDirection, smul_smul]
  rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]

/-- The derivative of the norm of a nonvanishing path in a real inner-product
space is its derivative paired with the unit direction. -/
theorem hasDerivAt_norm_of_ne_zero
    {w : ℝ → E} {w' : E} {t : ℝ} (hw : HasDerivAt w w' t) (hw0 : w t ≠ 0) :
    HasDerivAt (fun s => ‖w s‖) (inner ℝ (unitDirection (w t)) w') t := by
  have hsqrt := hw.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hw0))
  convert hsqrt using 1
  · funext s
    exact (Real.sqrt_sq (norm_nonneg (w s))).symm
  · rw [Real.sqrt_sq (norm_nonneg (w t))]
    simp only [unitDirection, real_inner_smul_left]
    have hn : ‖w t‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    rw [inv_mul_eq_div]
    field_simp [hn]

/-- Correct pointwise evolution of vorticity magnitude.  If the material
derivative of `w` is `S w + ν Δw`, then the derivative of `‖w‖` contains both the
stretching contribution and the viscous pairing `ν ⟪ξ, Δw⟫`. -/
theorem hasDerivAt_vorticity_magnitude
    {w : ℝ → E} {t ν : ℝ} (S : E →L[ℝ] E) (lapW : E) (hw0 : w t ≠ 0)
    (hw : HasDerivAt w (S (w t) + ν • lapW) t) :
    HasDerivAt (fun s => ‖w s‖)
      (stretchingRate S (w t) * ‖w t‖ + ν * inner ℝ (unitDirection (w t)) lapW) t := by
  have hnorm := hasDerivAt_norm_of_ne_zero hw hw0
  convert hnorm using 1
  rw [inner_add_right, real_inner_smul_right]
  have hw_decomp : w t = ‖w t‖ • unitDirection (w t) :=
    (norm_smul_unitDirection hw0).symm
  have hS : S (w t) = ‖w t‖ • S (unitDirection (w t)) := by
    calc
      S (w t) = S (‖w t‖ • unitDirection (w t)) := congrArg S hw_decomp
      _ = ‖w t‖ • S (unitDirection (w t)) := map_smul S _ _
  rw [hS, real_inner_smul_right]
  simp only [stretchingRate]
  ring

/-- The exact magnitude evolution rewritten as stretching minus the full
normalized viscous damping.  No favorable sign is discarded. -/
theorem hasDerivAt_vorticity_magnitude_with_damping
    {w : ℝ → E} {t ν : ℝ} (S : E →L[ℝ] E) (lapW : E) (hw0 : w t ≠ 0)
    (hw : HasDerivAt w (S (w t) + ν • lapW) t) :
    HasDerivAt (fun s => ‖w s‖)
      ((stretchingRate S (w t) - normalizedViscousDamping ν (w t) lapW) * ‖w t‖) t := by
  convert hasDerivAt_vorticity_magnitude S lapW hw0 hw using 1
  unfold normalizedViscousDamping
  have hn : ‖w t‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  field_simp [hn]
  all_goals ring

/-- Algebraic low/high strain split underlying the energy-paid reduction. -/
theorem stretching_split_sub_damping_le
    {full low high damping lowBudget residual : ℝ}
    (hsplit : full = low + high) (hlow : low ≤ lowBudget)
    (hresidual : high - damping ≤ residual) :
    full - damping ≤ lowBudget + residual := by
  linarith

/-- At a point where the viscous pairing is nonpositive, positive viscosity makes
the vorticity-magnitude derivative no larger than the stretching contribution. -/
theorem vorticity_magnitude_deriv_le_stretching
    {w lapW : E} {ν : ℝ} (S : E →L[ℝ] E) (hν : 0 ≤ ν)
    (hvisc : inner ℝ (unitDirection w) lapW ≤ 0) :
    stretchingRate S w * ‖w‖ + ν * inner ℝ (unitDirection w) lapW ≤
      stretchingRate S w * ‖w‖ := by
  exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hν hvisc)

/-- Constant-coefficient Grönwall closure for a nonnegative scalar magnitude.
This is the valid replacement for exponentiating a pointwise growth inequality. -/
theorem magnitude_le_exp_of_deriv_le
    {W W' : ℝ → ℝ} {a b K : ℝ}
    (hW : ContinuousOn W (Icc a b))
    (hW' : ∀ t ∈ Ico a b, HasDerivWithinAt W (W' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, W' t ≤ K * W t) :
    ∀ t ∈ Icc a b, W t ≤ W a * Real.exp (K * (t - a)) := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (δ := W a) (K := K) (ε := 0) (a := a) (b := b) (f' := W') hW
    (fun x hx _r hr => (hW' x hx).liminf_right_slope_le hr) (le_refl (W a))
    (by simpa using hbound) t ht
  simpa [gronwallBound_ε0] using h

/-- A valid exponential vorticity bound along a path on which the viscous pairing
has a favorable sign.  Establishing that sign is a separate spatial
maximum-principle obligation; it is not automatic on a fluid trajectory. -/
theorem norm_le_exp_of_vorticity_evolution
    {w lapW : ℝ → E} {S : ℝ → E →L[ℝ] E} {a b ν K : ℝ}
    (hw_cont : ContinuousOn w (Icc a b))
    (hw0 : ∀ t ∈ Ico a b, w t ≠ 0)
    (hw : ∀ t ∈ Ico a b, HasDerivAt w (S t (w t) + ν • lapW t) t)
    (hν : 0 ≤ ν)
    (hvisc : ∀ t ∈ Ico a b, inner ℝ (unitDirection (w t)) (lapW t) ≤ 0)
    (hstretch : ∀ t ∈ Ico a b, stretchingRate (S t) (w t) ≤ K) :
    ∀ t ∈ Icc a b, ‖w t‖ ≤ ‖w a‖ * Real.exp (K * (t - a)) := by
  let W : ℝ → ℝ := fun t => ‖w t‖
  let W' : ℝ → ℝ := fun t =>
    stretchingRate (S t) (w t) * ‖w t‖ +
      ν * inner ℝ (unitDirection (w t)) (lapW t)
  apply magnitude_le_exp_of_deriv_le
    (W := W) (W' := W') (a := a) (b := b) (K := K)
  · exact continuous_norm.comp_continuousOn hw_cont
  · intro t ht
    exact (hasDerivAt_vorticity_magnitude (S t) (lapW t) (hw0 t ht) (hw t ht)).hasDerivWithinAt
  · intro t ht
    calc
      W' t ≤ stretchingRate (S t) (w t) * ‖w t‖ :=
        vorticity_magnitude_deriv_le_stretching (S t) hν (hvisc t ht)
      _ ≤ K * W t := mul_le_mul_of_nonneg_right (hstretch t ht) (norm_nonneg _)
