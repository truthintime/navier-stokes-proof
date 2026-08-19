import NSFormal.Domain

/-!
# A transverse-direction regression test

Linewise constancy does not control transverse variation of a unit direction field.  The
explicit field below rotates in the `x₂` direction but has zero `x₂` component, so it is
constant on each of its own straight integral lines.  Its rotation frequency is arbitrary.
This is the elementary obstruction that a vortex-line recurrence argument must overcome before
it can invoke a regularity criterion requiring a spatially Lipschitz direction field.
-/

noncomputable section

/-- A unit vector in the coordinate plane, rotating with frequency `N`. -/
def twistingDirection (N z : ℝ) : Vec3 :=
  WithLp.toLp 2 ![Real.cos (N * z), Real.sin (N * z), 0]

/-- A three-dimensional direction field which varies only in the transverse `x₂` coordinate. -/
def transverseTwist (N : ℝ) (x : Vec3) : Vec3 :=
  twistingDirection N (x 2)

@[simp]
theorem twistingDirection_coord_zero (N z : ℝ) :
    twistingDirection N z 0 = Real.cos (N * z) := by
  simp [twistingDirection]

@[simp]
theorem twistingDirection_coord_one (N z : ℝ) :
    twistingDirection N z 1 = Real.sin (N * z) := by
  simp [twistingDirection]

@[simp]
theorem twistingDirection_coord_two (N z : ℝ) :
    twistingDirection N z 2 = 0 := by
  simp [twistingDirection]

/-- Every member of the family is exactly unit length. -/
theorem norm_twistingDirection (N z : ℝ) :
    ‖twistingDirection N z‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [twistingDirection, Fin.sum_univ_succ]

/-- Moving in the direction of the field does not change its transverse coordinate. -/
theorem transverseTwist_self_line (N r : ℝ) (x : Vec3) :
    transverseTwist N (x + r • transverseTwist N x) = transverseTwist N x := by
  unfold transverseTwist
  congr 1
  simp

/-- At transverse phase `π` the direction has reversed, regardless of the frequency. -/
theorem twistingDirection_antipodal_of_phase_pi
    {N z : ℝ} (hphase : N * z = Real.pi) :
    twistingDirection N z = -twistingDirection N 0 := by
  ext i
  fin_cases i <;> simp [twistingDirection, hphase]

/-- Arbitrarily high positive frequencies reverse direction across distance `π / N`. -/
theorem transverseTwist_antipodal_at_pi_div
    {N : ℝ} (hN : 0 < N) :
    transverseTwist N (EuclideanSpace.single 2 (Real.pi / N)) =
      -transverseTwist N 0 := by
  apply twistingDirection_antipodal_of_phase_pi
  change N * (Real.pi / N) = Real.pi
  field_simp [hN.ne']
