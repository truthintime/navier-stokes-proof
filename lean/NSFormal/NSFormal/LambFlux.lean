import Mathlib

/-!
# Lamb-vector flux cancellation

The Navier--Stokes nonlinearity modulo gradients is the Lamb vector `u × ω`.  These
finite-dimensional identities are the algebraic cancellation behind the global energy-flux
formula in `DYNAMICS.md`: a low-pass velocity paired with the Lamb vector sees only a
low--high velocity difference.
-/

namespace NSFormal

open Matrix
open scoped Matrix

variable {R : Type*} [CommRing R]

/-- In the first factor of the scalar triple product, the full velocity can be subtracted
without changing the Lamb pairing. -/
theorem lamb_pairing_eq_low_sub_full (low velocity vorticity : Fin 3 → R) :
    low ⬝ᵥ (velocity ⨯₃ vorticity) =
      (low - velocity) ⬝ᵥ (velocity ⨯₃ vorticity) := by
  rw [sub_dotProduct, dot_self_cross, sub_zero]

/-- Equivalently, the velocity inside the Lamb vector may be replaced by its high-pass
difference from the low-pass velocity. -/
theorem lamb_pairing_eq_high_cross (low velocity vorticity : Fin 3 → R) :
    low ⬝ᵥ (velocity ⨯₃ vorticity) =
      low ⬝ᵥ ((velocity - low) ⨯₃ vorticity) := by
  rw [map_sub, LinearMap.sub_apply, dotProduct_sub, dot_self_cross, sub_zero]

/-- The Lamb pairing is the cyclic vorticity-weighted line-integrand used by the vortex-line
disintegration. -/
theorem lamb_pairing_cyclic (low velocity vorticity : Fin 3 → R) :
    low ⬝ᵥ (velocity ⨯₃ vorticity) =
      vorticity ⬝ᵥ (low ⨯₃ velocity) := by
  rw [triple_product_permutation, triple_product_permutation]

section FilterPairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A self-adjoint filter can be moved across an inner product, turning two copies of the
filter into its square.  For the heat semigroup this is
`⟪Pₛu, PₛN⟫ = ⟪P₂ₛu, N⟫`. -/
theorem selfAdjoint_filter_pairing_sq (P : E →L[ℝ] E)
    (hself : ContinuousLinearMap.adjoint P = P) (u nonlinear : E) :
    inner ℝ (P u) (P nonlinear) = inner ℝ ((P.comp P) u) nonlinear := by
  calc
    inner ℝ (P u) (P nonlinear) =
        inner ℝ ((ContinuousLinearMap.adjoint P) (P u)) nonlinear :=
      (ContinuousLinearMap.adjoint_inner_left P nonlinear (P u)).symm
    _ = inner ℝ (P (P u)) nonlinear := by rw [hself]
    _ = inner ℝ ((P.comp P) u) nonlinear := rfl

/-- If the nonlinear term is a Lamb vector plus a gradient orthogonal to the twice-filtered
velocity, the doubly filtered nonlinear energy pairing is exactly the Lamb pairing. -/
theorem selfAdjoint_filtered_pairing_eq_lamb (P : E →L[ℝ] E)
    (hself : ContinuousLinearMap.adjoint P = P)
    (u nonlinear lamb gradient : E) (hnonlinear : nonlinear = lamb + gradient)
    (hgradient : inner ℝ ((P.comp P) u) gradient = 0) :
    inner ℝ (P u) (P nonlinear) = inner ℝ ((P.comp P) u) lamb := by
  rw [selfAdjoint_filter_pairing_sq P hself, hnonlinear, inner_add_right, hgradient, add_zero]

omit [CompleteSpace E] in
/-- The resolved velocity does the same work against a filtered Lamb vector and against the
subgrid vortex force, because the resolved Lamb vector is pointwise orthogonal to it.  In the
PDE application `vortexForce = Pₛ(u × ω) - Pₛu × Pₛω`. -/
theorem filteredLamb_pairing_eq_vortexForce
    (resolved filteredLamb resolvedLamb vortexForce : E)
    (hforce : vortexForce = filteredLamb - resolvedLamb)
    (hresolved : inner ℝ resolved resolvedLamb = 0) :
    inner ℝ resolved filteredLamb = inner ℝ resolved vortexForce := by
  rw [hforce, inner_sub_right, hresolved, sub_zero]

/-- A vector fixed by a self-adjoint projection sees only the projected part of a force.
For the Leray projection this says that gradients are invisible to a divergence-free resolved
velocity, so energy transfer depends only on the solenoidal subgrid vortex force. -/
theorem selfAdjoint_projection_pairing (Q : E →L[ℝ] E)
    (hself : ContinuousLinearMap.adjoint Q = Q) (resolved force : E)
    (hfixed : Q resolved = resolved) :
    inner ℝ resolved force = inner ℝ resolved (Q force) := by
  calc
    inner ℝ resolved force = inner ℝ (Q resolved) force := by rw [hfixed]
    _ = inner ℝ resolved ((ContinuousLinearMap.adjoint Q) force) :=
      (ContinuousLinearMap.adjoint_inner_right Q resolved force).symm
    _ = inner ℝ resolved (Q force) := by rw [hself]

/-- Abstract periodic curl integration by parts.  If a self-adjoint operator `C` maps a
potential to the resolved field, then work against a force equals the potential paired with
the corresponding defect `C force`.  Taking `C = curl` is the Hilbert-space core of the exact
energy--circulation duality in `DYNAMICS.md`. -/
theorem selfAdjoint_potential_pairing (C : E →L[ℝ] E)
    (hself : ContinuousLinearMap.adjoint C = C) (potential resolved force : E)
    (hpotential : C potential = resolved) :
    inner ℝ resolved force = inner ℝ potential (C force) := by
  calc
    inner ℝ resolved force = inner ℝ (C potential) force := by rw [hpotential]
    _ = inner ℝ potential ((ContinuousLinearMap.adjoint C) force) :=
      (ContinuousLinearMap.adjoint_inner_right C potential force).symm
    _ = inner ℝ potential (C force) := by rw [hself]

end FilterPairing

end NSFormal
