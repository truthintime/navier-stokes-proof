import NSFormal.NavierStokes

/-!
# Euclidean vector-calculus identities for periodic lifts

The torus operators are computed on periodic functions on `ℝ³`.  This file
starts the general curl derivation at that lifted level, where ordinary Fréchet
calculus applies.
-/

noncomputable section

/-- A standard-coordinate partial derivative on `ℝ³`. -/
def euclideanPartial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec3 → E) (i : Fin 3) (x : Vec3) : E :=
  fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))

/-- Mixed coordinate partials of a `C²` field commute. -/
theorem euclideanPartial_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec3 → E} (hf : ContDiff ℝ 2 f) (x : Vec3) (i j : Fin 3) :
    euclideanPartial (fun y => euclideanPartial f i y) j x =
      euclideanPartial (fun y => euclideanPartial f j y) i x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hi : fderiv ℝ
      (fun y => fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x =
        (fderiv ℝ (fderiv ℝ f) x).flip (EuclideanSpace.single i (1 : ℝ)) := by
    simpa using
      (hfd.hasFDerivAt.clm_apply
        (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) x)).fderiv
  have hj : fderiv ℝ
      (fun y => fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) x =
        (fderiv ℝ (fderiv ℝ f) x).flip (EuclideanSpace.single j (1 : ℝ)) := by
    simpa using
      (hfd.hasFDerivAt.clm_apply
        (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)).fderiv
  simp only [euclideanPartial]
  rw [hi, hj]
  simp only [ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- The derivative of a smooth torus lift has the same value at any two
Euclidean representatives of the same torus point. -/
theorem fderiv_torusLift_eq_of_torus3Mk_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Torus3 → E) (hf : ContDiff ℝ 1 (torusLift f))
    {x y : Vec3} (hxy : torus3Mk x = torus3Mk y) :
    fderiv ℝ (torusLift f) x = fderiv ℝ (torusLift f) y := by
  let shift : Vec3 := x - y
  let τ : Vec3 → Vec3 := fun z => z + shift
  have hmkShift : ∀ z : Vec3, torus3Mk (z + shift) = torus3Mk z := by
    intro z
    ext i
    have hi := congrArg (fun q : Torus3 => q i) hxy
    change ((x i : ℝ) : AddCircle ((2 : ℝ) * Real.pi)) =
      ((y i : ℝ) : AddCircle ((2 : ℝ) * Real.pi)) at hi
    change (((z i + (x i - y i) : ℝ)) :
      AddCircle ((2 : ℝ) * Real.pi)) =
        ((z i : ℝ) : AddCircle ((2 : ℝ) * Real.pi))
    rw [AddCircle.coe_add, AddCircle.coe_sub, hi, sub_self, add_zero]
  have hfun : torusLift f ∘ τ = torusLift f := by
    funext z
    exact congrArg f (hmkShift z)
  have hτ : DifferentiableAt ℝ τ y := by
    dsimp [τ]
    fun_prop
  have hflift : DifferentiableAt ℝ (torusLift f) (τ y) :=
    (hf.differentiable one_ne_zero).differentiableAt
  have hfd := congrArg (fun g : Vec3 → E => fderiv ℝ g y) hfun
  rw [fderiv_comp y hflift hτ] at hfd
  have hτfd : fderiv ℝ τ y = ContinuousLinearMap.id ℝ Vec3 := by
    dsimp [τ]
    rw [fderiv_add_const]
    exact (hasFDerivAt_id y).fderiv
  rw [hτfd, ContinuousLinearMap.comp_id] at hfd
  have hτy : τ y = x := by
    simp [τ, shift]
  simpa only [hτy] using hfd

/-- A directional Fréchet derivative is the coordinate sum of its standard
partial derivatives. -/
theorem fderiv_apply_eq_sum_euclideanPartial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec3 → E) (x v : Vec3) :
    fderiv ℝ f x v = ∑ i : Fin 3, v i • euclideanPartial f i x := by
  have hv : v = ∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_three]
  calc
    fderiv ℝ f x v =
        fderiv ℝ f x (∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ)) :=
      congrArg (fderiv ℝ f x) hv
    _ = ∑ i : Fin 3, v i • fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) := by
      simp
    _ = ∑ i : Fin 3, v i • euclideanPartial f i x := rfl

theorem euclideanPartial_component
    {u : Vec3 → Vec3} (hu : DifferentiableAt ℝ u x) (i j : Fin 3) :
    euclideanPartial (fun y => u y j) i x = euclideanPartial u i x j := by
  have hcomp := (EuclideanSpace.proj j).hasFDerivAt.comp x hu.hasFDerivAt
  have hfd := hcomp.fderiv
  have hfun : (fun y => u y j) = (EuclideanSpace.proj j) ∘ u := by
    funext y
    rfl
  simp only [euclideanPartial, hfun, hfd, ContinuousLinearMap.comp_apply]
  rfl

theorem ContDiff.euclideanPartial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec3 → E} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) (i : Fin 3) :
    ContDiff ℝ n (fun x => euclideanPartial f i x) := by
  have h := hf.contDiff_fderiv_apply (m := n) (by simp)
  exact h.comp (contDiff_id.prodMk contDiff_const)

theorem euclideanPartial_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : Vec3 → ℝ} {f : Vec3 → E} (hc : DifferentiableAt ℝ c x)
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    euclideanPartial (fun y => c y • f y) i x =
      c x • euclideanPartial f i x + euclideanPartial c i x • f x := by
  simp only [euclideanPartial, fderiv_fun_smul hc hf,
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]

theorem euclideanPartial_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Vec3 → E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    euclideanPartial (fun y => f y - g y) i x =
      euclideanPartial f i x - euclideanPartial g i x := by
  simp only [euclideanPartial, fderiv_fun_sub hf hg,
    sub_apply]

theorem euclideanPartial_finsetSum
    {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ι → Vec3 → E}
    (hf : ∀ j ∈ s, DifferentiableAt ℝ (f j) x) (i : Fin 3) :
    euclideanPartial (fun y => ∑ j ∈ s, f j y) i x =
      ∑ j ∈ s, euclideanPartial (f j) i x := by
  simp only [euclideanPartial, fderiv_fun_sum hf, sum_apply]

theorem euclideanPartial_fintypeSum
    {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ι → Vec3 → E}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (i : Fin 3) :
    euclideanPartial (fun y => ∑ j, f j y) i x =
      ∑ j, euclideanPartial (f j) i x := by
  simp only [euclideanPartial,
    fderiv_fun_sum (u := Finset.univ) (fun j _hj => hf j),
    sum_apply]

/-- The three antisymmetric mixed-partial combinations that form
`curl (gradient f)`. -/
def euclideanCurlGradient (f : Vec3 → ℝ) (x : Vec3) : Vec3 :=
  WithLp.toLp 2 ![
    euclideanPartial (fun y => euclideanPartial f 2 y) 1 x -
      euclideanPartial (fun y => euclideanPartial f 1 y) 2 x,
    euclideanPartial (fun y => euclideanPartial f 0 y) 2 x -
      euclideanPartial (fun y => euclideanPartial f 2 y) 0 x,
    euclideanPartial (fun y => euclideanPartial f 1 y) 0 x -
      euclideanPartial (fun y => euclideanPartial f 0 y) 1 x]

/-- `curl (gradient f) = 0`, proved from symmetry of the second Fréchet
derivative rather than postulated as a vector-calculus axiom. -/
theorem euclideanCurlGradient_eq_zero
    {f : Vec3 → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec3) :
    euclideanCurlGradient f x = 0 := by
  ext i
  fin_cases i
  · simp [euclideanCurlGradient, euclideanPartial_comm hf x 2 1]
  · simp [euclideanCurlGradient, euclideanPartial_comm hf x 0 2]
  · simp [euclideanCurlGradient, euclideanPartial_comm hf x 1 0]

/-- Pressure gradients make no contribution to the lifted torus curl. -/
theorem torusLift_curlGradient_eq_zero
    (p : C(Torus3, ℝ)) (hp : ContDiff ℝ 2 (torusLift p)) (x : Torus3) :
    euclideanCurlGradient (torusLift p) (torus3Representative x) = 0 :=
  euclideanCurlGradient_eq_zero hp _

/-! ## Coordinate algebra for the convection curl -/

/-- Coordinate Jacobian of a lifted vector field. -/
def euclideanJacobian (u : Vec3 → Vec3) (x : Vec3) : Fin 3 → Fin 3 → ℝ :=
  fun i j => euclideanPartial u i x j

/-- Coordinate Hessian of a lifted vector field.  The index convention is
`H k i j = ∂ₖ∂ᵢuⱼ`. -/
def euclideanHessian (u : Vec3 → Vec3) (x : Vec3) :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun k i j => euclideanPartial (fun y => euclideanPartial u i y) k x j

theorem euclideanHessian_symm
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u) (x : Vec3) :
    ∀ i k j, euclideanHessian u x i k j = euclideanHessian u x k i j := by
  intro i k j
  exact congrArg (fun v : Vec3 => v j) (euclideanPartial_comm hu x k i)

/-- Advective derivative of lifted vector fields. -/
def euclideanTransport (u v : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  fderiv ℝ v x (u x)

/-- Curl reconstructed from the coordinate Jacobian `D i j = ∂ᵢuⱼ`. -/
def curlOfJacobian (D : Fin 3 → Fin 3 → ℝ) : Vec3 :=
  WithLp.toLp 2 ![D 1 2 - D 2 1, D 2 0 - D 0 2, D 0 1 - D 1 0]

/-- Curl of a lifted vector field. -/
def euclideanCurl (u : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  curlOfJacobian (euclideanJacobian u x)

/-- Divergence reconstructed from a coordinate Jacobian. -/
def divergenceOfJacobian (D : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, D i i

/-- Divergence of a lifted vector field. -/
def euclideanDivergence (u : Vec3 → Vec3) (x : Vec3) : ℝ :=
  divergenceOfJacobian (euclideanJacobian u x)

/-- Coordinate form of `(a · ∇)u`, where `D i j = ∂ᵢuⱼ`. -/
def transportOfJacobian (a : Vec3) (D : Fin 3 → Fin 3 → ℝ) : Vec3 :=
  WithLp.toLp 2 fun j => ∑ i : Fin 3, a i * D i j

/-- Jacobian of curl reconstructed from
`H k i j = ∂ₖ∂ᵢuⱼ`. -/
def curlJacobianOfHessian (H : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    Fin 3 → Fin 3 → ℝ := fun k j =>
  ![H k 1 2 - H k 2 1, H k 2 0 - H k 0 2, H k 0 1 - H k 1 0] j

/-- Curl of the coordinate convection term, after the product rule has been
expanded. -/
def curlTransportOfJet
    (u : Vec3) (D : Fin 3 → Fin 3 → ℝ)
    (H : Fin 3 → Fin 3 → Fin 3 → ℝ) : Vec3 :=
  let dTransport : Fin 3 → Fin 3 → ℝ := fun k j =>
    ∑ i : Fin 3, (D k i * D i j + u i * H k i j)
  WithLp.toLp 2 ![
    dTransport 1 2 - dTransport 2 1,
    dTransport 2 0 - dTransport 0 2,
    dTransport 0 1 - dTransport 1 0]

/-- Pure coordinate form of the convection-curl identity.  The only analytic
input it needs is symmetry of the first two Hessian indices. -/
theorem curlTransportOfJet_eq
    (u : Vec3) (D : Fin 3 → Fin 3 → ℝ)
    (H : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hH : ∀ i k j, H i k j = H k i j) :
    curlTransportOfJet u D H =
      transportOfJacobian u (curlJacobianOfHessian H) -
        transportOfJacobian (curlOfJacobian D) D +
        divergenceOfJacobian D • curlOfJacobian D := by
  ext j
  fin_cases j
  · simp [curlTransportOfJet, transportOfJacobian, curlJacobianOfHessian,
      curlOfJacobian, divergenceOfJacobian, Fin.sum_univ_three]
    rw [hH 1 0 2, hH 2 0 1, hH 2 1 1, hH 1 2 2]
    ring
  · simp [curlTransportOfJet, transportOfJacobian, curlJacobianOfHessian,
      curlOfJacobian, divergenceOfJacobian, Fin.sum_univ_three]
    rw [hH 2 0 0, hH 0 2 2, hH 2 1 0, hH 0 1 2]
    ring
  · simp [curlTransportOfJet, transportOfJacobian, curlJacobianOfHessian,
      curlOfJacobian, divergenceOfJacobian, Fin.sum_univ_three]
    rw [hH 1 0 0, hH 0 1 1, hH 0 2 1, hH 1 2 0]
    ring

/-- Incompressible specialization of the coordinate convection-curl identity. -/
theorem curlTransportOfJet_eq_of_divergence_zero
    (u : Vec3) (D : Fin 3 → Fin 3 → ℝ)
    (H : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hH : ∀ i k j, H i k j = H k i j)
    (hdiv : divergenceOfJacobian D = 0) :
    curlTransportOfJet u D H =
      transportOfJacobian u (curlJacobianOfHessian H) -
        transportOfJacobian (curlOfJacobian D) D := by
  rw [curlTransportOfJet_eq u D H hH, hdiv, zero_smul, add_zero]

/-- The coordinate transport agrees with application of the Fréchet derivative. -/
theorem transportOfJacobian_euclideanJacobian
    (a : Vec3) (u : Vec3 → Vec3) (x : Vec3) :
    transportOfJacobian a (euclideanJacobian u x) = fderiv ℝ u x a := by
  rw [fderiv_apply_eq_sum_euclideanPartial]
  ext j
  simp [transportOfJacobian, euclideanJacobian, Finset.sum_apply]

theorem euclideanTransport_eq_transportOfJacobian
    (u v : Vec3 → Vec3) (x : Vec3) :
    euclideanTransport u v x =
      transportOfJacobian (u x) (euclideanJacobian v x) := by
  symm
  exact transportOfJacobian_euclideanJacobian (u x) v x

/-- Product-rule expansion of the Jacobian of the convection term. -/
theorem euclideanJacobian_selfTransport_eq_jet
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u) (x : Vec3) :
    euclideanJacobian (fun y => euclideanTransport u u y) x =
      fun k j => ∑ i : Fin 3,
        (euclideanJacobian u x k i * euclideanJacobian u x i j +
          u x i * euclideanHessian u x k i j) := by
  have hu_diff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hpartial : ∀ i : Fin 3,
      Differentiable ℝ (fun y => euclideanPartial u i y) := by
    intro i
    exact (hu.euclideanPartial i).differentiable (by norm_num)
  have hfun : (fun y => euclideanTransport u u y) =
      fun y => ∑ i : Fin 3, u y i • euclideanPartial u i y := by
    funext y
    rw [euclideanTransport, fderiv_apply_eq_sum_euclideanPartial]
  funext k j
  rw [euclideanJacobian, hfun]
  rw [euclideanPartial_fintypeSum (fun i => by fun_prop)]
  change (EuclideanSpace.proj j)
      (∑ i : Fin 3, euclideanPartial
        (fun y => u y i • euclideanPartial u i y) k x) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [euclideanPartial_smul (by fun_prop) (hpartial i x) k]
  rw [euclideanPartial_component (hu_diff x) k i]
  simp [euclideanJacobian, euclideanHessian]
  ring

theorem euclideanCurl_contDiff_one
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (fun y => euclideanCurl u y) := by
  unfold euclideanCurl curlOfJacobian euclideanJacobian
  have hp : ∀ i : Fin 3, ContDiff ℝ 1 (fun y => euclideanPartial u i y) :=
    fun i => hu.euclideanPartial i
  apply contDiff_piLp'
  intro j
  fin_cases j
  · exact (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 2) (hp 1)).sub
      (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 1) (hp 2))
  · exact (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 0) (hp 2)).sub
      (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 2) (hp 0))
  · exact (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 1) (hp 0)).sub
      (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 0) (hp 1))

theorem ContDiff.euclideanCurlField
    {u : Vec3 → Vec3} {n : ℕ} (hu : ContDiff ℝ (n + 1) u) :
    ContDiff ℝ n (fun y => euclideanCurl u y) := by
  unfold euclideanCurl curlOfJacobian euclideanJacobian
  have hp : ∀ i : Fin 3, ContDiff ℝ n
      (fun y => _root_.euclideanPartial u i y) :=
    fun i => hu.euclideanPartial i
  apply contDiff_piLp'
  intro j
  fin_cases j
  · exact (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 2) (hp 1)).sub
      (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 1) (hp 2))
  · exact (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 0) (hp 2)).sub
      (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 2) (hp 0))
  · exact (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 1) (hp 0)).sub
      (ContDiff.continuousLinearMap_comp (EuclideanSpace.proj 0) (hp 1))

/-- The Jacobian of curl is the corresponding antisymmetric part of the
velocity Hessian. -/
theorem euclideanJacobian_curl_eq
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u) (x : Vec3) :
    euclideanJacobian (fun y => euclideanCurl u y) x =
      curlJacobianOfHessian (euclideanHessian u x) := by
  have hpartial : ∀ i : Fin 3,
      Differentiable ℝ (fun y => euclideanPartial u i y) := fun i =>
    (hu.euclideanPartial i).differentiable (by norm_num)
  have hcurl : Differentiable ℝ (fun y => euclideanCurl u y) :=
    (euclideanCurl_contDiff_one hu).differentiable (by norm_num)
  funext k j
  rw [euclideanJacobian]
  rw [← euclideanPartial_component (hcurl x) k j]
  fin_cases j
  · change euclideanPartial
      (fun y => euclideanPartial u 1 y 2 - euclideanPartial u 2 y 1) k x = _
    rw [euclideanPartial_sub (by fun_prop) (by fun_prop) k]
    rw [euclideanPartial_component (hpartial 1 x) k 2,
      euclideanPartial_component (hpartial 2 x) k 1]
    rfl
  · change euclideanPartial
      (fun y => euclideanPartial u 2 y 0 - euclideanPartial u 0 y 2) k x = _
    rw [euclideanPartial_sub (by fun_prop) (by fun_prop) k]
    rw [euclideanPartial_component (hpartial 2 x) k 0,
      euclideanPartial_component (hpartial 0 x) k 2]
    rfl
  · change euclideanPartial
      (fun y => euclideanPartial u 0 y 1 - euclideanPartial u 1 y 0) k x = _
    rw [euclideanPartial_sub (by fun_prop) (by fun_prop) k]
    rw [euclideanPartial_component (hpartial 0 x) k 1,
      euclideanPartial_component (hpartial 1 x) k 0]
    rfl

/-- The divergence of the curl of a `C²` Euclidean field vanishes. -/
theorem euclideanDivergence_curl_eq_zero
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u) (x : Vec3) :
    euclideanDivergence (fun y => euclideanCurl u y) x = 0 := by
  rw [euclideanDivergence, euclideanJacobian_curl_eq hu x]
  simp only [divergenceOfJacobian, Fin.sum_univ_three,
    curlJacobianOfHessian]
  change
    (euclideanHessian u x 0 1 2 - euclideanHessian u x 0 2 1) +
      (euclideanHessian u x 1 2 0 - euclideanHessian u x 1 0 2) +
      (euclideanHessian u x 2 0 1 - euclideanHessian u x 2 1 0) = 0
  rw [euclideanHessian_symm hu x 0 2 1,
    euclideanHessian_symm hu x 1 0 2,
    euclideanHessian_symm hu x 2 1 0]
  ring

/-- Lifted incompressible convection identity:
`curl ((u·∇)u) = (u·∇)ω - (ω·∇)u`, with `ω = curl u`. -/
theorem euclideanCurl_selfTransport_eq
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u) (x : Vec3)
    (hdiv : euclideanDivergence u x = 0) :
    euclideanCurl (fun y => euclideanTransport u u y) x =
      euclideanTransport u (fun y => euclideanCurl u y) x -
        euclideanTransport (fun y => euclideanCurl u y) u x := by
  rw [euclideanCurl, euclideanJacobian_selfTransport_eq_jet hu x]
  change curlTransportOfJet (u x) (euclideanJacobian u x)
    (euclideanHessian u x) = _
  rw [curlTransportOfJet_eq_of_divergence_zero
    (u x) (euclideanJacobian u x) (euclideanHessian u x)
    (euclideanHessian_symm hu x)]
  · rw [← euclideanJacobian_curl_eq hu x]
    rw [transportOfJacobian_euclideanJacobian,
      transportOfJacobian_euclideanJacobian]
    rfl
  · exact hdiv

/-! ## Curl--Laplacian commutation -/

/-- Third coordinate derivative, with convention
`T k i h j = ∂ₖ∂ᵢ∂ₕuⱼ`. -/
def euclideanThirdDerivative (u : Vec3 → Vec3) (x : Vec3) :
    Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun k i h j =>
  euclideanPartial
    (fun y => euclideanPartial (fun z => euclideanPartial u h z) i y) k x j

/-- Componentwise third derivative, convenient for differentiating coordinate
formulas. -/
def euclideanScalarThirdDerivative (u : Vec3 → Vec3) (x : Vec3) :
    Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun k i h j =>
  euclideanPartial
    (fun y => euclideanPartial
      (fun z => euclideanPartial (fun w => u w j) h z) i y) k x

theorem euclideanScalarThirdDerivative_eq
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 3 u) (x : Vec3)
    (k i h j : Fin 3) :
    euclideanScalarThirdDerivative u x k i h j =
      euclideanThirdDerivative u x k i h j := by
  have hu_diff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hp_h : Differentiable ℝ (fun y => euclideanPartial u h y) :=
    (hu.euclideanPartial h).differentiable (by norm_num)
  have hp_ih : Differentiable ℝ
      (fun y => euclideanPartial (fun z => euclideanPartial u h z) i y) :=
    ((hu.euclideanPartial h).euclideanPartial i).differentiable (by norm_num)
  have h0 : (fun z => euclideanPartial (fun w => u w j) h z) =
      fun z => euclideanPartial u h z j := by
    funext z
    exact euclideanPartial_component (hu_diff z) h j
  have h1 :
      (fun y => euclideanPartial
        (fun z => euclideanPartial (fun w => u w j) h z) i y) =
      fun y => euclideanPartial (fun z => euclideanPartial u h z) i y j := by
    funext y
    rw [h0]
    exact euclideanPartial_component (hp_h y) i j
  rw [euclideanScalarThirdDerivative, euclideanThirdDerivative, h1]
  exact euclideanPartial_component (hp_ih x) k j

/-- The permutation needed to commute curl with the Laplacian. -/
theorem euclideanThirdDerivative_repeated_comm
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 3 u) (x : Vec3) :
    ∀ k i j, euclideanThirdDerivative u x k i i j =
      euclideanThirdDerivative u x i i k j := by
  intro k i j
  have hpartial_i : ContDiff ℝ 2 (fun y => euclideanPartial u i y) :=
    hu.euclideanPartial i
  have hswap₁ := euclideanPartial_comm hpartial_i x i k
  have hinner :
      (fun y => euclideanPartial (fun z => euclideanPartial u i z) k y) =
        fun y => euclideanPartial (fun z => euclideanPartial u k z) i y := by
    funext y
    exact euclideanPartial_comm (hu.of_le (by norm_num)) y i k
  apply congrArg (fun v : Vec3 => v j)
  exact hswap₁.trans (by rw [hinner])

/-- Jacobian of a coordinate Laplacian reconstructed from a third derivative. -/
def jacobianLaplacianOfThird
    (T : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun k j => ∑ i : Fin 3, T k i i j

/-- Coordinate Laplacian of curl reconstructed from a third derivative. -/
def laplacianCurlOfThird
    (T : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : Vec3 :=
  WithLp.toLp 2 ![
    ∑ i : Fin 3, (T i i 1 2 - T i i 2 1),
    ∑ i : Fin 3, (T i i 2 0 - T i i 0 2),
    ∑ i : Fin 3, (T i i 0 1 - T i i 1 0)]

theorem curl_laplacian_jet_eq
    (T : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hT : ∀ k i j, T k i i j = T i i k j) :
    curlOfJacobian (jacobianLaplacianOfThird T) =
      laplacianCurlOfThird T := by
  ext j
  fin_cases j
  · simp [curlOfJacobian, jacobianLaplacianOfThird, laplacianCurlOfThird,
      Fin.sum_univ_three]
    rw [hT 1 0 2, hT 1 1 2, hT 1 2 2,
      hT 2 0 1, hT 2 1 1, hT 2 2 1]
  · simp [curlOfJacobian, jacobianLaplacianOfThird, laplacianCurlOfThird,
      Fin.sum_univ_three]
    rw [hT 2 0 0, hT 2 1 0, hT 2 2 0,
      hT 0 0 2, hT 0 1 2, hT 0 2 2]
  · simp [curlOfJacobian, jacobianLaplacianOfThird, laplacianCurlOfThird,
      Fin.sum_univ_three]
    rw [hT 0 0 1, hT 0 1 1, hT 0 2 1,
      hT 1 0 0, hT 1 1 0, hT 1 2 0]

/-- Coordinate-sum Laplacian on lifted vector fields. -/
def euclideanVectorLaplacian (u : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  ∑ i : Fin 3, euclideanPartial (fun y => euclideanPartial u i y) i x

/-- A vector Laplacian may be evaluated componentwise. -/
theorem euclideanVectorLaplacian_apply
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 2 u) (x : Vec3) (j : Fin 3) :
    euclideanVectorLaplacian u x j =
      ∑ i : Fin 3, euclideanPartial
        (fun y => euclideanPartial (fun z => u z j) i y) i x := by
  have hu_diff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hp : ∀ i : Fin 3,
      Differentiable ℝ (fun y => euclideanPartial u i y) := fun i =>
    (hu.euclideanPartial i).differentiable (by norm_num)
  rw [euclideanVectorLaplacian]
  change (EuclideanSpace.proj j)
      (∑ i : Fin 3, euclideanPartial (fun y => euclideanPartial u i y) i x) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  change (euclideanPartial (fun y => euclideanPartial u i y) i x) j = _
  rw [← euclideanPartial_component (hp i x) i j]
  congr 2
  funext y
  exact (euclideanPartial_component (hu_diff y) i j).symm

theorem euclideanSecondPartial_sub
    {f g : Vec3 → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : Vec3) (i : Fin 3) :
    euclideanPartial
        (fun y => euclideanPartial (fun z => f z - g z) i y) i x =
      euclideanPartial (fun y => euclideanPartial f i y) i x -
        euclideanPartial (fun y => euclideanPartial g i y) i x := by
  have hfirst :
      (fun y => euclideanPartial (fun z => f z - g z) i y) =
        fun y => euclideanPartial f i y - euclideanPartial g i y := by
    funext y
    exact euclideanPartial_sub
      (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y) i
  rw [hfirst]
  exact euclideanPartial_sub
    ((hf.euclideanPartial i).differentiable (by norm_num) x)
    ((hg.euclideanPartial i).differentiable (by norm_num) x) i

/-- The coordinate Laplacian of curl is reconstructed by the same third-order
jet used in `curl_laplacian_jet_eq`. -/
theorem euclideanVectorLaplacian_curl_eq_jet
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 3 u) (x : Vec3) :
    euclideanVectorLaplacian (fun y => euclideanCurl u y) x =
      laplacianCurlOfThird (euclideanThirdDerivative u x) := by
  have hu_diff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hcomp : ∀ j : Fin 3, ContDiff ℝ 3 (fun y => u y j) := fun j =>
    ContDiff.continuousLinearMap_comp (EuclideanSpace.proj j) hu
  have hpcomp : ∀ h j : Fin 3,
      ContDiff ℝ 2 (fun y => euclideanPartial (fun z => u z j) h y) :=
    fun h j => (hcomp j).euclideanPartial h
  have hcurl : ContDiff ℝ 2 (fun y => euclideanCurl u y) :=
    hu.euclideanCurlField
  have hc0 : (fun y => euclideanCurl u y 0) = fun y =>
      euclideanPartial (fun z => u z 2) 1 y -
        euclideanPartial (fun z => u z 1) 2 y := by
    funext y
    simp [euclideanCurl, curlOfJacobian, euclideanJacobian]
    rw [euclideanPartial_component (hu_diff y) 1 2,
      euclideanPartial_component (hu_diff y) 2 1]
  have hc1 : (fun y => euclideanCurl u y 1) = fun y =>
      euclideanPartial (fun z => u z 0) 2 y -
        euclideanPartial (fun z => u z 2) 0 y := by
    funext y
    simp [euclideanCurl, curlOfJacobian, euclideanJacobian]
    rw [euclideanPartial_component (hu_diff y) 2 0,
      euclideanPartial_component (hu_diff y) 0 2]
  have hc2 : (fun y => euclideanCurl u y 2) = fun y =>
      euclideanPartial (fun z => u z 1) 0 y -
        euclideanPartial (fun z => u z 0) 1 y := by
    funext y
    simp [euclideanCurl, curlOfJacobian, euclideanJacobian]
    rw [euclideanPartial_component (hu_diff y) 0 1,
      euclideanPartial_component (hu_diff y) 1 0]
  ext j
  fin_cases j
  · change euclideanVectorLaplacian (fun y => euclideanCurl u y) x 0 =
      laplacianCurlOfThird (euclideanThirdDerivative u x) 0
    rw [euclideanVectorLaplacian_apply hcurl x 0, hc0]
    simp [laplacianCurlOfThird]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [euclideanSecondPartial_sub (hpcomp 1 2) (hpcomp 2 1) x i]
    change euclideanScalarThirdDerivative u x i i 1 2 -
      euclideanScalarThirdDerivative u x i i 2 1 = _
    rw [euclideanScalarThirdDerivative_eq hu x,
      euclideanScalarThirdDerivative_eq hu x]
  · change euclideanVectorLaplacian (fun y => euclideanCurl u y) x 1 =
      laplacianCurlOfThird (euclideanThirdDerivative u x) 1
    rw [euclideanVectorLaplacian_apply hcurl x 1, hc1]
    simp [laplacianCurlOfThird]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [euclideanSecondPartial_sub (hpcomp 2 0) (hpcomp 0 2) x i]
    change euclideanScalarThirdDerivative u x i i 2 0 -
      euclideanScalarThirdDerivative u x i i 0 2 = _
    rw [euclideanScalarThirdDerivative_eq hu x,
      euclideanScalarThirdDerivative_eq hu x]
  · change euclideanVectorLaplacian (fun y => euclideanCurl u y) x 2 =
      laplacianCurlOfThird (euclideanThirdDerivative u x) 2
    rw [euclideanVectorLaplacian_apply hcurl x 2, hc2]
    simp [laplacianCurlOfThird]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [euclideanSecondPartial_sub (hpcomp 0 1) (hpcomp 1 0) x i]
    change euclideanScalarThirdDerivative u x i i 0 1 -
      euclideanScalarThirdDerivative u x i i 1 0 = _
    rw [euclideanScalarThirdDerivative_eq hu x,
      euclideanScalarThirdDerivative_eq hu x]

theorem euclideanJacobian_laplacian_eq
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 3 u) (x : Vec3) :
    euclideanJacobian (fun y => euclideanVectorLaplacian u y) x =
      jacobianLaplacianOfThird (euclideanThirdDerivative u x) := by
  have hsecond : ∀ i : Fin 3,
      Differentiable ℝ
        (fun y => euclideanPartial (fun z => euclideanPartial u i z) i y) := by
    intro i
    exact ((hu.euclideanPartial i).euclideanPartial i).differentiable (by norm_num)
  funext k j
  rw [euclideanJacobian]
  simp only [euclideanVectorLaplacian]
  rw [euclideanPartial_fintypeSum (fun i => hsecond i x)]
  change (EuclideanSpace.proj j)
      (∑ i : Fin 3, euclideanPartial
        (fun y => euclideanPartial (fun z => euclideanPartial u i z) i y) k x) = _
  rw [map_sum]
  rfl

/-- Curl commutes with the coordinate Laplacian on every `C³` lifted field. -/
theorem euclideanCurl_laplacian_eq
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 3 u) (x : Vec3) :
    euclideanCurl (fun y => euclideanVectorLaplacian u y) x =
      euclideanVectorLaplacian (fun y => euclideanCurl u y) x := by
  rw [euclideanCurl, euclideanJacobian_laplacian_eq hu x,
    euclideanVectorLaplacian_curl_eq_jet hu x]
  exact curl_laplacian_jet_eq (euclideanThirdDerivative u x)
    (euclideanThirdDerivative_repeated_comm hu x)

/-- The line-based second derivative used by `PeriodicCalculus` agrees with
the repeated coordinate Fréchet derivative. -/
theorem iteratedDeriv_coordinateLine_two_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec3 → E} (hf : ContDiff ℝ 2 f) (x : Vec3) (i : Fin 3) :
    iteratedDeriv 2 (fun s => f (coordinateLine x i s)) 0 =
      euclideanPartial (fun y => euclideanPartial f i y) i x := by
  let e : Vec3 := EuclideanSpace.single i (1 : ℝ)
  let line : ℝ → Vec3 := coordinateLine x i
  have hline : ∀ s : ℝ, HasDerivAt line e s := by
    intro s
    have hs : HasDerivAt (fun r : ℝ => r • e) e s := by
      simpa using (hasDerivAt_id s).smul_const e
    have h := HasDerivAt.const_add x hs
    change HasDerivAt (fun r : ℝ => x + r • e) e s at h
    change HasDerivAt (fun r : ℝ => x + r • e) e s
    exact h
  have hfirst : deriv (fun s => f (line s)) =
      fun s => euclideanPartial f i (line s) := by
    funext s
    have hcomp := (hf.differentiable (by norm_num) (line s)).hasFDerivAt.comp_hasDerivAt
      s (hline s)
    simpa [Function.comp_def, euclideanPartial, e] using hcomp.deriv
  have hp : ContDiff ℝ 1 (fun y => euclideanPartial f i y) :=
    hf.euclideanPartial i
  have hsecond := (hp.differentiable (by norm_num) (line 0)).hasFDerivAt.comp_hasDerivAt
    0 (hline 0)
  rw [show iteratedDeriv 2 (fun s => f (coordinateLine x i s)) 0 =
      deriv (deriv (fun s => f (line s))) 0 by
        simp [line, iteratedDeriv_succ]]
  rw [hfirst]
  simpa [Function.comp_def, line, coordinateLine, euclideanPartial, e] using
    hsecond.deriv

theorem torusLiftVectorLaplacian_eq_euclideanVectorLaplacian
    (u : C(Torus3, Vec3)) (hu : ContDiff ℝ 2 (torusLift u)) (x : Vec3) :
    torusLiftVectorLaplacian u x = euclideanVectorLaplacian (torusLift u) x := by
  rw [torusLiftVectorLaplacian, euclideanVectorLaplacian]
  apply Finset.sum_congr rfl
  intro i _hi
  exact iteratedDeriv_coordinateLine_two_eq hu x i

theorem torusVectorLaplacian_eq_euclideanVectorLaplacian
    (u : C(Torus3, Vec3)) (hu : ContDiff ℝ 2 (torusLift u)) (x : Torus3) :
    torusVectorLaplacian u x =
      euclideanVectorLaplacian (torusLift u) (torus3Representative x) :=
  torusLiftVectorLaplacian_eq_euclideanVectorLaplacian u hu _

theorem torusCurl_eq_euclideanCurl
    (u : C(Torus3, Vec3)) (x : Torus3) :
    torusCurl u x = euclideanCurl (torusLift u) (torus3Representative x) := rfl

/-- The lifted curl is independent of the Euclidean representative of a torus
point. -/
theorem euclideanCurl_torusLift_eq_of_torus3Mk_eq
    (u : C(Torus3, Vec3)) (hu : ContDiff ℝ 1 (torusLift u))
    {x y : Vec3} (hxy : torus3Mk x = torus3Mk y) :
    euclideanCurl (torusLift u) x = euclideanCurl (torusLift u) y := by
  unfold euclideanCurl euclideanJacobian euclideanPartial
  rw [fderiv_torusLift_eq_of_torus3Mk_eq u hu hxy]

/-- Pointwise equality `w = curl u` on the torus is equivalent to the expected
identity between their periodic Euclidean lifts. -/
theorem torusLift_eq_euclideanCurl_of_curl
    (u w : C(Torus3, Vec3))
    (hu : ContDiff ℝ 1 (torusLift u))
    (hw : ∀ x : Torus3, w x = torusCurl u x)
    (y : Vec3) :
    torusLift w y = euclideanCurl (torusLift u) y := by
  calc
    torusLift w y = w (torus3Mk y) := rfl
    _ = torusCurl u (torus3Mk y) := hw _
    _ = euclideanCurl (torusLift u)
        (torus3Representative (torus3Mk y)) :=
      torusCurl_eq_euclideanCurl u _
    _ = euclideanCurl (torusLift u) y :=
      euclideanCurl_torusLift_eq_of_torus3Mk_eq u hu
        (torus3Mk_representative (torus3Mk y))

theorem torusDivergence_eq_euclideanDivergence
    (u : C(Torus3, Vec3)) (x : Torus3) :
    torusDivergence u x =
      euclideanDivergence (torusLift u) (torus3Representative x) := rfl

theorem torusTransport_eq_transportOfJacobian
    (u v : C(Torus3, Vec3)) (x : Torus3) :
    torusTransport u v x =
      transportOfJacobian (u x)
        (euclideanJacobian (torusLift v) (torus3Representative x)) := by
  rw [transportOfJacobian_euclideanJacobian]
  rfl

/-! ## Linearity and lifted operator bridges -/

theorem euclideanCurl_add
    {f g : Vec3 → Vec3} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (x : Vec3) :
    euclideanCurl (fun y => f y + g y) x =
      euclideanCurl f x + euclideanCurl g x := by
  ext j
  fin_cases j <;>
    simp [euclideanCurl, curlOfJacobian, euclideanJacobian, euclideanPartial,
      fderiv_fun_add (hf _) (hg _)] <;> ring

theorem euclideanCurl_sub
    {f g : Vec3 → Vec3} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (x : Vec3) :
    euclideanCurl (fun y => f y - g y) x =
      euclideanCurl f x - euclideanCurl g x := by
  ext j
  fin_cases j <;>
    simp [euclideanCurl, curlOfJacobian, euclideanJacobian, euclideanPartial,
      fderiv_fun_sub (hf _) (hg _)] <;> ring

theorem euclideanCurl_const_smul
    (c : ℝ) {f : Vec3 → Vec3} (hf : Differentiable ℝ f) (x : Vec3) :
    euclideanCurl (fun y => c • f y) x = c • euclideanCurl f x := by
  ext j
  fin_cases j <;>
    simp [euclideanCurl, curlOfJacobian, euclideanJacobian, euclideanPartial,
      fderiv_fun_const_smul (hf _)] <;> ring

theorem torusLiftGradient_eq_euclideanGradient
    (p : C(Torus3, ℝ)) (y : Vec3) :
    torusLiftGradient p y =
      WithLp.toLp 2 fun i => euclideanPartial (torusLift p) i y := rfl

/-- The curl of the directly lifted pressure gradient vanishes. -/
theorem euclideanCurl_torusLiftGradient_eq_zero
    (p : C(Torus3, ℝ)) (hp : ContDiff ℝ 2 (torusLift p)) (x : Vec3) :
    euclideanCurl (fun y => torusLiftGradient p y) x = 0 := by
  have hgrad : Differentiable ℝ (fun y => torusLiftGradient p y) := by
    rw [show (fun y => torusLiftGradient p y) =
        fun y => WithLp.toLp 2 fun i => euclideanPartial (torusLift p) i y by rfl]
    apply (differentiable_piLp 2).mpr
    intro i
    exact (hp.euclideanPartial i).differentiable one_ne_zero
  ext j
  fin_cases j
  · change euclideanPartial (fun y => torusLiftGradient p y) 1 x 2 -
      euclideanPartial (fun y => torusLiftGradient p y) 2 x 1 = 0
    rw [← euclideanPartial_component (hgrad x) 1 2,
      ← euclideanPartial_component (hgrad x) 2 1]
    change euclideanPartial (fun y => euclideanPartial (torusLift p) 2 y) 1 x -
      euclideanPartial (fun y => euclideanPartial (torusLift p) 1 y) 2 x = 0
    rw [euclideanPartial_comm hp x 2 1]
    simp
  · change euclideanPartial (fun y => torusLiftGradient p y) 2 x 0 -
      euclideanPartial (fun y => torusLiftGradient p y) 0 x 2 = 0
    rw [← euclideanPartial_component (hgrad x) 2 0,
      ← euclideanPartial_component (hgrad x) 0 2]
    change euclideanPartial (fun y => euclideanPartial (torusLift p) 0 y) 2 x -
      euclideanPartial (fun y => euclideanPartial (torusLift p) 2 y) 0 x = 0
    rw [euclideanPartial_comm hp x 0 2]
    simp
  · change euclideanPartial (fun y => torusLiftGradient p y) 0 x 1 -
      euclideanPartial (fun y => torusLiftGradient p y) 1 x 0 = 0
    rw [← euclideanPartial_component (hgrad x) 0 1,
      ← euclideanPartial_component (hgrad x) 1 0]
    change euclideanPartial (fun y => euclideanPartial (torusLift p) 1 y) 0 x -
      euclideanPartial (fun y => euclideanPartial (torusLift p) 0 y) 1 x = 0
    rw [euclideanPartial_comm hp x 1 0]
    simp

theorem torusLiftDivergence_eq_euclideanDivergence
    (u : C(Torus3, Vec3)) (x : Vec3) :
    torusLiftDivergence u x = euclideanDivergence (torusLift u) x := rfl

theorem torusLiftTransport_eq_euclideanTransport
    (u v : C(Torus3, Vec3)) (x : Vec3) :
    torusLiftTransport u v x =
      euclideanTransport (torusLift u) (torusLift v) x := rfl

/-! ## Joint time-space calculus -/

/-- Unit time direction in `ℝ × ℝ³`. -/
def spaceTimeTimeDirection : ℝ × Vec3 := (1, 0)

/-- The `i`th spatial coordinate direction in `ℝ × ℝ³`. -/
def spaceTimeSpaceDirection (i : Fin 3) : ℝ × Vec3 :=
  (0, EuclideanSpace.single i (1 : ℝ))

/-- A fixed directional derivative of a joint time-space field. -/
def spaceTimeDirectionalDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (ℝ × Vec3) → E) (v : ℝ × Vec3) (q : ℝ × Vec3) : E :=
  fderiv ℝ F q v

theorem ContDiff.spaceTimeDirectionalDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (ℝ × Vec3) → E} {n : ℕ} (hF : ContDiff ℝ (n + 1) F)
    (v : ℝ × Vec3) :
    ContDiff ℝ n (fun q => spaceTimeDirectionalDerivative F v q) := by
  have h := hF.contDiff_fderiv_apply (m := n) (by simp)
  exact h.comp (contDiff_id.prodMk contDiff_const)

/-- Symmetry of mixed directional derivatives for a jointly `C²` field. -/
theorem spaceTimeDirectionalDerivative_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (ℝ × Vec3) → E} (hF : ContDiff ℝ 2 F)
    (q v w : ℝ × Vec3) :
    spaceTimeDirectionalDerivative
        (fun z => spaceTimeDirectionalDerivative F v z) w q =
      spaceTimeDirectionalDerivative
        (fun z => spaceTimeDirectionalDerivative F w z) v q := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) q :=
    (hF.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hv : fderiv ℝ (fun z => fderiv ℝ F z v) q =
      (fderiv ℝ (fderiv ℝ F) q).flip v := by
    simpa using
      (hfd.hasFDerivAt.clm_apply (hasFDerivAt_const v q)).fderiv
  have hw : fderiv ℝ (fun z => fderiv ℝ F z w) q =
      (fderiv ℝ (fderiv ℝ F) q).flip w := by
    simpa using
      (hfd.hasFDerivAt.clm_apply (hasFDerivAt_const w q)).fderiv
  simp only [spaceTimeDirectionalDerivative]
  rw [hv, hw]
  simp only [ContinuousLinearMap.flip_apply]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- A spatial derivative of a time slice is the corresponding joint
time-space directional derivative. -/
theorem euclideanPartial_timeSlice_eq_spaceTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (ℝ × Vec3) → E} (hF : Differentiable ℝ F)
    (t : ℝ) (x : Vec3) (i : Fin 3) :
    euclideanPartial (fun y => F (t, y)) i x =
      spaceTimeDirectionalDerivative F (spaceTimeSpaceDirection i) (t, x) := by
  have hpair : HasFDerivAt (fun y : Vec3 => (t, y))
      ((0 : Vec3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec3)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hcomp := (hF (t, x)).hasFDerivAt.comp x hpair
  have hcomp' : HasFDerivAt (fun y => F (t, y))
      ((fderiv ℝ F (t, x)).comp
        ((0 : Vec3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec3))) x := by
    simpa [Function.comp_def] using hcomp
  simp only [euclideanPartial, spaceTimeDirectionalDerivative,
    spaceTimeSpaceDirection, hcomp'.fderiv, ContinuousLinearMap.comp_apply]
  simp

/-- At fixed space, differentiating a joint field in time gives its derivative
in the unit time direction. -/
theorem hasDerivAt_timeSlice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (ℝ × Vec3) → E} (hF : Differentiable ℝ F)
    (t : ℝ) (x : Vec3) :
    HasDerivAt (fun s => F (s, x))
      (spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, x)) t := by
  have hpair : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hcomp := (hF (t, x)).hasFDerivAt.comp_hasDerivAt t hpair
  simpa [spaceTimeDirectionalDerivative, spaceTimeTimeDirection,
    Function.comp_def] using hcomp

/-- Time differentiation commutes with a spatial coordinate derivative for a
jointly `C²` field. -/
theorem hasDerivAt_euclideanPartial_timeSlice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (ℝ × Vec3) → E} (hF : ContDiff ℝ 2 F)
    (t : ℝ) (x : Vec3) (i : Fin 3) :
    HasDerivAt
      (fun s => euclideanPartial (fun y => F (s, y)) i x)
      (euclideanPartial
        (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
        i x) t := by
  have hspace : ContDiff ℝ 1
      (fun q => spaceTimeDirectionalDerivative F (spaceTimeSpaceDirection i) q) :=
    hF.spaceTimeDirectionalDerivative (spaceTimeSpaceDirection i)
  have htime := hasDerivAt_timeSlice (hspace.differentiable one_ne_zero) t x
  have hfun : (fun s => euclideanPartial (fun y => F (s, y)) i x) =
      fun s => spaceTimeDirectionalDerivative F (spaceTimeSpaceDirection i) (s, x) := by
    funext s
    exact euclideanPartial_timeSlice_eq_spaceTime
      (hF.differentiable (by norm_num)) s x i
  rw [hfun]
  convert htime using 1
  rw [euclideanPartial_timeSlice_eq_spaceTime
    ((hF.spaceTimeDirectionalDerivative spaceTimeTimeDirection).differentiable
      one_ne_zero)
    t x i]
  exact (spaceTimeDirectionalDerivative_comm hF (t, x)
    (spaceTimeSpaceDirection i) spaceTimeTimeDirection).symm

/-- Time differentiation commutes with curl for a jointly `C²` vector field. -/
theorem hasDerivAt_euclideanCurl_timeSlice
    {F : (ℝ × Vec3) → Vec3} (hF : ContDiff ℝ 2 F)
    (t : ℝ) (x : Vec3) :
    HasDerivAt
      (fun s => euclideanCurl (fun y => F (s, y)) x)
      (euclideanCurl
        (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
        x) t := by
  have hp : ∀ i : Fin 3,
      HasDerivAt (fun s => euclideanPartial (fun y => F (s, y)) i x)
        (euclideanPartial
          (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
          i x) t := fun i => hasDerivAt_euclideanPartial_timeSlice hF t x i
  have hc : ∀ i j : Fin 3,
      HasDerivAt (fun s => euclideanPartial (fun y => F (s, y)) i x j)
        (euclideanPartial
          (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
          i x j) t := by
    intro i j
    simpa [Function.comp_def] using
      (EuclideanSpace.proj j).hasFDerivAt.comp_hasDerivAt t (hp i)
  change HasDerivAt
    (fun s => WithLp.toLp 2 ![
      euclideanPartial (fun y => F (s, y)) 1 x 2 -
        euclideanPartial (fun y => F (s, y)) 2 x 1,
      euclideanPartial (fun y => F (s, y)) 2 x 0 -
        euclideanPartial (fun y => F (s, y)) 0 x 2,
      euclideanPartial (fun y => F (s, y)) 0 x 1 -
        euclideanPartial (fun y => F (s, y)) 1 x 0])
    (WithLp.toLp 2 ![
      euclideanPartial
          (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
          1 x 2 -
        euclideanPartial
          (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
          2 x 1,
      euclideanPartial
          (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
          2 x 0 -
        euclideanPartial
          (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
          0 x 2,
      euclideanPartial
          (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
          0 x 1 -
        euclideanPartial
          (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
          1 x 0]) t
  have hraw : HasDerivAt
      (fun s => ![
        euclideanPartial (fun y => F (s, y)) 1 x 2 -
          euclideanPartial (fun y => F (s, y)) 2 x 1,
        euclideanPartial (fun y => F (s, y)) 2 x 0 -
          euclideanPartial (fun y => F (s, y)) 0 x 2,
        euclideanPartial (fun y => F (s, y)) 0 x 1 -
          euclideanPartial (fun y => F (s, y)) 1 x 0])
      (![
        euclideanPartial
            (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
            1 x 2 -
          euclideanPartial
            (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
            2 x 1,
        euclideanPartial
            (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
            2 x 0 -
          euclideanPartial
            (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
            0 x 2,
        euclideanPartial
            (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
            0 x 1 -
          euclideanPartial
            (fun y => spaceTimeDirectionalDerivative F spaceTimeTimeDirection (t, y))
            1 x 0]) t := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact (hc 1 2).sub (hc 2 1)
    · exact (hc 2 0).sub (hc 0 2)
    · exact (hc 0 1).sub (hc 1 0)
  have hto := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hraw
  simpa [Function.comp_def] using hto

/-- The sup-norm time derivative in the classical solution predicate agrees
pointwise with the unit-time derivative of the joint lift. -/
theorem spaceTimeDirectionalDerivative_eq_torusLift_timeDerivative
    {u uTime : ℝ → C(Torus3, Vec3)} {t : ℝ}
    (hu : HasDerivAt u (uTime t) t)
    (hjoint : Differentiable ℝ (torusSpaceTimeLift u)) (y : Vec3) :
    spaceTimeDirectionalDerivative (torusSpaceTimeLift u)
        spaceTimeTimeDirection (t, y) = torusLift (uTime t) y := by
  have hev := (ContinuousMap.evalCLM ℝ (torus3Mk y)).hasFDerivAt.comp_hasDerivAt t hu
  have hev' : HasDerivAt (fun s => torusSpaceTimeLift u (s, y))
      (torusLift (uTime t) y) t := by
    simpa [torusSpaceTimeLift, torusLift, Function.comp_def] using hev
  have hjoint' := hasDerivAt_timeSlice hjoint t y
  exact hjoint'.unique hev'

/-- Curl commutes with the time derivative of a jointly smooth periodic
velocity field. -/
theorem hasDerivAt_torusCurl
    {u uTime : ℝ → C(Torus3, Vec3)} {t : ℝ}
    (hu : HasDerivAt u (uTime t) t)
    (hjoint : ContDiff ℝ 2 (torusSpaceTimeLift u)) (x : Torus3) :
    HasDerivAt (fun s => torusCurl (u s) x) (torusCurl (uTime t) x) t := by
  have h := hasDerivAt_euclideanCurl_timeSlice hjoint t
    (torus3Representative x)
  have htime : (fun y => spaceTimeDirectionalDerivative (torusSpaceTimeLift u)
      spaceTimeTimeDirection (t, y)) = torusLift (uTime t) := by
    funext y
    exact spaceTimeDirectionalDerivative_eq_torusLift_timeDerivative hu
      (hjoint.differentiable (by norm_num)) y
  rw [htime] at h
  exact h

/-! ## Derivation of the smooth lifted vorticity equation -/

theorem ContDiff.timeSlice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (ℝ × Vec3) → E} {n : ℕ∞} (hF : ContDiff ℝ n F) (t : ℝ) :
    ContDiff ℝ n (fun y => F (t, y)) := by
  exact hF.comp (contDiff_const.prodMk contDiff_id)

theorem differentiable_euclideanVectorLaplacian
    {u : Vec3 → Vec3} (hu : ContDiff ℝ 3 u) :
    Differentiable ℝ (fun y => euclideanVectorLaplacian u y) := by
  have hsecond : ∀ i : Fin 3,
      Differentiable ℝ
        (fun y => euclideanPartial (fun z => euclideanPartial u i z) i y) :=
    fun i => ((hu.euclideanPartial i).euclideanPartial i).differentiable one_ne_zero
  unfold euclideanVectorLaplacian
  fun_prop

theorem differentiable_torusLiftGradient
    (p : C(Torus3, ℝ)) (hp : ContDiff ℝ 2 (torusLift p)) :
    Differentiable ℝ (fun y => torusLiftGradient p y) := by
  rw [show (fun y => torusLiftGradient p y) =
      fun y => WithLp.toLp 2 fun i => euclideanPartial (torusLift p) i y by rfl]
  apply (differentiable_piLp 2).mpr
  intro i
  exact (hp.euclideanPartial i).differentiable one_ne_zero

/-- Taking curl of the smooth lifted momentum equation yields the full
viscous vector-vorticity equation.  In particular, the pressure term is
eliminated by a proved mixed-partial identity, and curl is proved to commute
with the coordinate Laplacian. -/
theorem smoothNavierStokes_lifted_vorticityEquation
    {ν a b : ℝ} {u uTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsSmoothNavierStokesOn ν a b u uTime p)
    {t : ℝ} (ht : t ∈ Set.Ico a b) (x : Vec3) :
    euclideanCurl (torusLift (uTime t)) x =
      euclideanTransport (fun y => euclideanCurl (torusLift (u t)) y)
          (torusLift (u t)) x +
        ν • euclideanVectorLaplacian
          (fun y => euclideanCurl (torusLift (u t)) y) x -
        euclideanTransport (torusLift (u t))
          (fun y => euclideanCurl (torusLift (u t)) y) x := by
  rcases hNS with ⟨hclass, hjointU, hjointP, hdiv, hpde⟩
  rcases hclass with ⟨_hν, _hcont, htime, _hspaceU, _hspaceP,
    _hdivTorus, _hpdeTorus⟩
  have hU : ContDiff ℝ 3 (torusLift (u t)) := by
    simpa [torusSpaceTimeLift] using hjointU.timeSlice t
  have hP : ContDiff ℝ 2 (torusLift (p t)) := by
    simpa [torusSpaceTimeLift] using hjointP.timeSlice t
  have hUt : ContDiff ℝ 2 (torusLift (uTime t)) := by
    have hdir : ContDiff ℝ 2
        (fun q => spaceTimeDirectionalDerivative (torusSpaceTimeLift u)
          spaceTimeTimeDirection q) :=
      hjointU.spaceTimeDirectionalDerivative spaceTimeTimeDirection
    have hslice := hdir.timeSlice t
    have heq : (fun y => spaceTimeDirectionalDerivative (torusSpaceTimeLift u)
        spaceTimeTimeDirection (t, y)) = torusLift (uTime t) := by
      funext y
      exact spaceTimeDirectionalDerivative_eq_torusLift_timeDerivative
        (htime t ht) (hjointU.differentiable (by norm_num)) y
    rwa [heq] at hslice
  have hU2 : ContDiff ℝ 2 (torusLift (u t)) := hU.of_le (by norm_num)
  have hL : Differentiable ℝ
      (fun y => euclideanVectorLaplacian (torusLift (u t)) y) :=
    differentiable_euclideanVectorLaplacian hU
  have hG : Differentiable ℝ (fun y => torusLiftGradient (p t) y) :=
    differentiable_torusLiftGradient (p t) hP
  have hνL : Differentiable ℝ
      (fun y => ν • euclideanVectorLaplacian (torusLift (u t)) y) :=
    hL.const_smul ν
  have hpdeFun :
      (fun y => torusLift (uTime t) y +
        euclideanTransport (torusLift (u t)) (torusLift (u t)) y) =
      (fun y => ν • euclideanVectorLaplacian (torusLift (u t)) y -
        torusLiftGradient (p t) y) := by
    funext y
    rw [← torusLiftTransport_eq_euclideanTransport,
      ← torusLiftVectorLaplacian_eq_euclideanVectorLaplacian
        (u t) hU2 y]
    exact hpde t ht y
  have hN : Differentiable ℝ
      (fun y => euclideanTransport (torusLift (u t)) (torusLift (u t)) y) := by
    have hNfun :
        (fun y => euclideanTransport (torusLift (u t)) (torusLift (u t)) y) =
        (fun y =>
          (ν • euclideanVectorLaplacian (torusLift (u t)) y -
            torusLiftGradient (p t) y) - torusLift (uTime t) y) := by
      funext y
      have hy := congrFun hpdeFun y
      ext j
      have hj := congrArg (fun z : Vec3 => z j) hy
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul] at hj ⊢
      linarith
    rw [hNfun]
    exact (hνL.sub hG).sub (hUt.differentiable (by norm_num))
  have hcurl := congrArg (fun f : Vec3 → Vec3 => euclideanCurl f x) hpdeFun
  rw [euclideanCurl_add (hUt.differentiable (by norm_num)) hN x,
    euclideanCurl_sub hνL hG x,
    euclideanCurl_const_smul ν hL x,
    euclideanCurl_torusLiftGradient_eq_zero (p t) hP x,
    sub_zero,
    euclideanCurl_selfTransport_eq hU2 x,
    euclideanCurl_laplacian_eq hU x] at hcurl
  · ext j
    have hj := congrArg (fun z : Vec3 => z j) hcurl
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] at hj ⊢
    linarith
  · exact hdiv t ⟨ht.1, ht.2.le⟩ x

/-- Along every smooth Navier--Stokes solution, the pointwise derivative of
curl is the stretching--diffusion--transport expression. -/
theorem smoothNavierStokes_hasDerivAt_vorticity
    {ν a b : ℝ} {u uTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsSmoothNavierStokesOn ν a b u uTime p)
    {t : ℝ} (ht : t ∈ Set.Ico a b) (x : Torus3) :
    HasDerivAt (fun s => torusCurl (u s) x)
      (euclideanTransport
          (fun y => euclideanCurl (torusLift (u t)) y) (torusLift (u t))
          (torus3Representative x) +
        ν • euclideanVectorLaplacian
          (fun y => euclideanCurl (torusLift (u t)) y)
          (torus3Representative x) -
        euclideanTransport (torusLift (u t))
          (fun y => euclideanCurl (torusLift (u t)) y)
          (torus3Representative x)) t := by
  rcases hNS with ⟨hclass, hjointU, hjointP, hdiv, hpde⟩
  rcases hclass with ⟨hν, hcont, htime, hspaceU, hspaceP,
    hdivTorus, hpdeTorus⟩
  have hcurl := hasDerivAt_torusCurl (htime t ht)
    (hjointU.of_le (by norm_num)) x
  convert hcurl using 1
  exact (smoothNavierStokes_lifted_vorticityEquation
    ⟨⟨hν, hcont, htime, hspaceU, hspaceP, hdivTorus, hpdeTorus⟩,
      hjointU, hjointP, hdiv, hpde⟩ ht (torus3Representative x)).symm

/-! ## From a concrete curl field to the classical vorticity predicate -/

/-- A concrete periodic vorticity field agrees with curl at every point of the
smooth periodic lift.  This is a proposition about supplied fields, not an
assumed solution type or typeclass. -/
def IsLiftedVorticityOf
    (u ω : ℝ → C(Torus3, Vec3)) : Prop :=
  ∀ t : ℝ, ∀ y : Vec3,
    torusLift (ω t) y = euclideanCurl (torusLift (u t)) y

theorem isLiftedVorticityOf_zero :
    IsLiftedVorticityOf
      (fun _ => (0 : C(Torus3, Vec3)))
      (fun _ => (0 : C(Torus3, Vec3))) := by
  intro t y
  have hzero : torusLift (0 : C(Torus3, Vec3)) =
      fun _ : Vec3 => (0 : Vec3) := by
    funext z
    rfl
  rw [hzero]
  simp [euclideanCurl, euclideanJacobian, euclideanPartial, curlOfJacobian]
  ext i
  fin_cases i <;> rfl

/-- If `ω = curl u` on the lift, uniqueness of time derivatives identifies
`ωₜ` with `curl uₜ`. -/
theorem torusLift_vorticityTime_eq_euclideanCurl_time
    {u uTime ω ωTime : ℝ → C(Torus3, Vec3)} {t : ℝ}
    (hcurl : IsLiftedVorticityOf u ω)
    (huTime : HasDerivAt u (uTime t) t)
    (hωTime : HasDerivAt ω (ωTime t) t)
    (hjoint : ContDiff ℝ 2 (torusSpaceTimeLift u)) (y : Vec3) :
    torusLift (ωTime t) y = euclideanCurl (torusLift (uTime t)) y := by
  have hev := (ContinuousMap.evalCLM ℝ (torus3Mk y)).hasFDerivAt.comp_hasDerivAt
    t hωTime
  have hev' : HasDerivAt (fun s => torusLift (ω s) y)
      (torusLift (ωTime t) y) t := by
    simpa [torusLift, Function.comp_def] using hev
  have hfunctions : (fun s => torusLift (ω s) y) =
      fun s => euclideanCurl (torusLift (u s)) y := by
    funext s
    exact hcurl s y
  rw [hfunctions] at hev'
  have hrhs := hasDerivAt_euclideanCurl_timeSlice hjoint t y
  have htimeField :
      (fun z => spaceTimeDirectionalDerivative (torusSpaceTimeLift u)
        spaceTimeTimeDirection (t, z)) = torusLift (uTime t) := by
    funext z
    exact spaceTimeDirectionalDerivative_eq_torusLift_timeDerivative huTime
      (hjoint.differentiable (by norm_num)) z
  rw [htimeField] at hrhs
  exact hev'.unique hrhs

/-- The lifted vector-vorticity equation derived from smooth Navier--Stokes and
the concrete identity `ω = curl u`. -/
theorem smoothNavierStokes_lifted_vorticityEquation_of_curl
    {ν a b : ℝ} {u uTime ω ωTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsSmoothNavierStokesOn ν a b u uTime p)
    (hcurl : IsLiftedVorticityOf u ω)
    {t : ℝ} (ht : t ∈ Set.Ico a b)
    (hωTime : HasDerivAt ω (ωTime t) t) (y : Vec3) :
    torusLift (ωTime t) y =
      euclideanTransport (torusLift (ω t)) (torusLift (u t)) y +
        ν • euclideanVectorLaplacian (torusLift (ω t)) y -
        euclideanTransport (torusLift (u t)) (torusLift (ω t)) y := by
  rcases hNS with ⟨hclass, hjointU, hjointP, hdiv, hpde⟩
  rcases hclass with ⟨hν, hcont, huTime, hspaceU, hspaceP,
    hdivTorus, hpdeTorus⟩
  have htime := torusLift_vorticityTime_eq_euclideanCurl_time hcurl
    (huTime t ht) hωTime (hjointU.of_le (by norm_num)) y
  rw [htime]
  have heq := smoothNavierStokes_lifted_vorticityEquation
    ⟨⟨hν, hcont, huTime, hspaceU, hspaceP, hdivTorus, hpdeTorus⟩,
      hjointU, hjointP, hdiv, hpde⟩ ht y
  have hcurlFun : (fun z => euclideanCurl (torusLift (u t)) z) =
      torusLift (ω t) := by
    funext z
    exact (hcurl t z).symm
  rwa [hcurlFun] at heq

/-- The previously defined classical vorticity equation is a theorem for every
regular concrete curl field of a smooth Navier--Stokes solution.  Its analytic
regularity hypotheses are explicit and the zero solution witnesses them. -/
theorem isClassicalVorticityEquationOn_of_smoothNavierStokes
    {ν a b : ℝ} {u uTime ω ωTime : ℝ → C(Torus3, Vec3)}
    {p : ℝ → C(Torus3, ℝ)}
    (hNS : IsSmoothNavierStokesOn ν a b u uTime p)
    (hcurl : IsLiftedVorticityOf u ω)
    (hω_cont : ContinuousOn ω (Set.Icc a b))
    (hω_deriv : ∀ t ∈ Set.Ico a b, HasDerivAt ω (ωTime t) t)
    (hω_space : ∀ t ∈ Set.Icc a b, ContDiff ℝ 2 (torusLift (ω t))) :
    IsClassicalVorticityEquationOn ν a b u ω ωTime := by
  refine ⟨hNS.1.1.le, hω_cont, hω_deriv, hω_space, ?_⟩
  intro t ht x
  have htcc : t ∈ Set.Icc a b := ⟨ht.1, ht.2.le⟩
  have heq := smoothNavierStokes_lifted_vorticityEquation_of_curl
    hNS hcurl ht (hω_deriv t ht) (torus3Representative x)
  rw [← torusVectorLaplacian_eq_euclideanVectorLaplacian
    (ω t) (hω_space t htcc) x] at heq
  simpa [euclideanTransport, torusStretching, torusTransport,
    torusDirectionalDerivative, torusLift] using heq
