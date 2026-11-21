/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.IntegralBaseChange

/-! # Naturality of integral scalar-extension lattices

Canonical integral scalar extension and its actual image lattice are natural
for linear maps, as required for the Tate specialization maps in
[TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (R₀ R L M : Type*) [CommRing R₀] [CommRing R] [CommRing L]
  [Algebra R₀ R] [Algebra R₀ L] [Algebra R L] [IsScalarTower R₀ R L]
  [AddCommMonoid M] [Module R₀ M]

variable {N : Type*} [AddCommMonoid N] [Module R₀ N]

/-- The canonical integral tensor map is natural in the original module. -/
theorem integralBaseChangeMap_natural (f : M →ₗ[R₀] N) (x : R ⊗[R₀] M) :
    f.baseChange L (integralBaseChangeMap R₀ R L M x) =
      integralBaseChangeMap R₀ R L N (f.baseChange R x) := by
  induction x using _root_.TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r m => simp only [integralBaseChangeMap_tmul, LinearMap.baseChange_tmul]

/-- An integral module map preserves the actual image lattices after coefficient extension. -/
theorem map_mem_integralBaseChangeLattice (f : M →ₗ[R₀] N)
    {x : L ⊗[R₀] M} (hx : x ∈ integralBaseChangeLattice R₀ R L M) :
    f.baseChange L x ∈ integralBaseChangeLattice R₀ R L N := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨f.baseChange R u, (integralBaseChangeMap_natural R₀ R L M f u).symm⟩


end Algebra.TensorProduct
