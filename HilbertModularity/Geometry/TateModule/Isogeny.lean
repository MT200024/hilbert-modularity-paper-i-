/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.Endomorphism
public import HilbertModularity.RepresentationTheory.TateModule.Isogeny

/-! # Isogeny invariance for geometric Tate representations

An actual ground-field group-scheme morphism whose geometric point map is
surjective with finite kernel induces an equivariant rational Tate isomorphism.
These point-map hypotheses are explicit, as required by [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  {A B : Over (Spec (CommRingCat.of K))}
  [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
  (p : ℕ) [Fact p.Prime] (f : A ⟶ B) [IsMonHom f]
  [Finite (pointsMap K (AlgebraicClosure K) f).ker]

/-- Finite geometric kernel gives injectivity on the actual integral Tate module. -/
theorem integralTateMap_injective_of_finite_kernel : Function.Injective (integralTateMap K p f) :=
  TateModule.map_injective_of_finite_kernel p (pointsMap K (AlgebraicClosure K) f)

/-- A geometric point isogeny preserves the actual rational Galois Tate representation. -/
def tateIsogenyEquiv (hf : Function.Surjective (pointsMap K (AlgebraicClosure K) f)) :
    (tateRepresentation K A p).Equiv (tateRepresentation K B p) :=
  TateModule.rationalFiniteKernelRepresentationEquiv p _ (pointsMap K (AlgebraicClosure K) f)
    (pointsMap_galois K (AlgebraicClosure K) f) hf

/-- The isogeny equivalence is the actual covariant map induced by the geometric morphism. -/
@[simp]
theorem tateIsogenyEquiv_apply (hf : Function.Surjective (pointsMap K (AlgebraicClosure K) f))
    (x : rationalTate K A p) : tateIsogenyEquiv K p f hf x = rationalTateMap K p f x := rfl

end AlgebraicGeometry.GroupScheme
