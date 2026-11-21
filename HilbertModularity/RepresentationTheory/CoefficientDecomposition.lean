/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.CoefficientDecomposition
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RepresentationTheory.Intertwining

/-! # Equivariant coefficient decomposition

When a coefficient algebra commutes with a representation, each coefficient
idempotent cuts out a subrepresentation. The simultaneous projections give an
equivariant decomposition, as in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {R G ι : Type*} [Semiring R] [Monoid G]
  {V : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)]

/-- The coordinatewise product of a family of representations. -/
def pi (ρ : (i : ι) → Representation R G (V i)) : Representation R G ((i : ι) → V i) where
  toFun g := LinearMap.pi fun i => (ρ i g).comp (LinearMap.proj i)
  map_one' := by ext v i; simp
  map_mul' g h := by ext v i; simp

@[simp]
theorem pi_apply (ρ : (i : ι) → Representation R G (V i)) (g : G)
    (v : (i : ι) → V i) (i : ι) : pi ρ g v i = ρ i g (v i) := rfl

end Representation

namespace Representation

open Algebra.TensorProduct

variable (F K L : Type*) {G V : Type*} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra F L] [FiniteDimensional F K] [Algebra.IsSeparable F K]
  [Monoid G] [AddCommGroup V] [Module L V]
  [Module (L ⊗[F] K) V] [IsScalarTower L (L ⊗[F] K) V]
  (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
  (ρ : Representation L G V)
  (hρ : ∀ (g : G) (a : L ⊗[F] K) (v : V), ρ g (a • v) = a • ρ g v)

/-- The image of a coefficient idempotent is stable under an action commuting with coefficients. -/
def coefficientSubrepresentation (σ : K →ₐ[F] L) : Subrepresentation ρ where
  toSubmodule := coefficientSummand F K L V hL σ
  apply_mem_toSubmodule g := by
    rintro v ⟨w, rfl⟩
    exact ⟨ρ g w, (hρ g (embeddingIdempotent F K L hL σ) w).symm⟩

/-- The coefficient decomposition intertwines the original and coordinatewise actions. -/
def coefficientDecompositionEquiv :
    ρ.Equiv (pi fun σ => (coefficientSubrepresentation F K L hL ρ hρ σ).toRepresentation) :=
  .mk (Algebra.TensorProduct.coefficientDecomposition F K L V hL) (by
    intro g
    ext v σ
    exact (hρ g (embeddingIdempotent F K L hL σ) v).symm)

end Representation
