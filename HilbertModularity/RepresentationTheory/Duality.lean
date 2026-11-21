/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

/-!
# Duality and Frobenius conventions

The dual representation acts on linear functionals by precomposition with the
inverse group element. Dualizing and inverting the element together preserves
the characteristic polynomial. Biduality also transports representation
isomorphisms without a Tate twist.

## Main results

* `charpoly_dual_inv`: the characteristic polynomial after duality and inversion.
* `representationBidualEquiv`: equivariance of the canonical biduality map.
* `dualEquivOfEquivDual`: dualizing an isomorphism to a dual representation.

## References

[TripathiGoswami], the normalization conventions in §2.4.
-/

namespace HilbertModularity

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The transpose action on the dual preserves the characteristic polynomial. -/
lemma charpoly_dualMap [FiniteDimensional K V] (f : V →ₗ[K] V) :
    f.dualMap.charpoly = f.charpoly := by
  classical
  let b := Module.Free.chooseBasis K V
  rw [← LinearMap.charpoly_toMatrix _ b.dualBasis, ← LinearMap.charpoly_toMatrix _ b]
  have hm : LinearMap.toMatrix b.dualBasis b.dualBasis f.dualMap =
      (LinearMap.toMatrix b b f).transpose := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [hm, Matrix.charpoly_transpose]

/-- Dualizing a representation and inverting the element preserves its
characteristic polynomial in every finite dimension. -/
theorem charpoly_dual_inv [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G) :
    (ρ.dual g⁻¹).charpoly = (ρ g).charpoly := by
  change (ρ (g⁻¹)⁻¹).dualMap.charpoly = _
  rw [inv_inv, charpoly_dualMap]

/-- Equivalence of representations is preserved by taking duals. -/
noncomputable def representationDualEquiv
    {ρ : Representation K G V} {σ : Representation K G W} (e : ρ.Equiv σ) :
    ρ.dual.Equiv σ.dual :=
  .mk e.toLinearEquiv.symm.dualMap fun g => by
    ext φ w
    change φ (ρ g⁻¹ (e.symm w)) = φ (e.symm (σ g⁻¹ w))
    exact congrArg φ (e.symm.toIntertwiningMap.isIntertwining σ ρ g⁻¹ w).symm

/-- In dimension two, inversion alone divides the trace by the determinant. -/
theorem matrix_trace_inv (M : Matrix (Fin 2) (Fin 2) K) :
    M⁻¹.trace = M.trace / M.det := by
  rw [Matrix.inv_def, Matrix.trace_smul, Matrix.adjugate_fin_two]
  simp [Matrix.trace_fin_two, Ring.inverse_eq_inv, div_eq_mul_inv, mul_comm, add_comm]

/-- The trace of the inverse group element in a two-dimensional representation.
Unlike duality combined with inversion, inversion alone need not preserve trace. -/
theorem representation_trace_inv
    (b : Module.Basis (Fin 2) K V) (ρ : Representation K G V) (g : G) :
    LinearMap.trace K V (ρ g⁻¹) = LinearMap.trace K V (ρ g) / LinearMap.det (ρ g) := by
  have hi : (LinearMap.toMatrix b b (ρ g))⁻¹ = LinearMap.toMatrix b b (ρ g⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one]
    exact LinearMap.toMatrix_one b
  rw [LinearMap.trace_eq_matrix_trace K b, ← hi, matrix_trace_inv,
    ← LinearMap.trace_eq_matrix_trace K b, LinearMap.det_toMatrix]

/-- The canonical evaluation isomorphism is equivariant for the double dual. -/
noncomputable def representationBidualEquiv [FiniteDimensional K V]
    (ρ : Representation K G V) : ρ.Equiv ρ.dual.dual :=
  .mk (Module.evalEquiv K V) fun g => by
    ext v φ
    simp [Representation.dual_apply, Module.Dual.transpose_apply]

/-- An isomorphism of a covariant representation to the dual of a fixed
cohomological representation gives an isomorphism of their cohomological duals. -/
noncomputable def dualEquivOfEquivDual [FiniteDimensional K W]
    {ρ : Representation K G V} {σ : Representation K G W} (e : ρ.Equiv σ.dual) :
    ρ.dual.Equiv σ :=
  (representationDualEquiv e).trans (representationBidualEquiv σ).symm

end HilbertModularity
