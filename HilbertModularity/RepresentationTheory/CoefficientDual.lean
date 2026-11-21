/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.CoefficientDual
public import HilbertModularity.RepresentationTheory.CoefficientDecomposition
public import Mathlib.RepresentationTheory.Intertwining

/-! # Equivariant duals of coefficient-projector images

Transposition of an equivariant map is equivariant for the contragredient
representations. Restriction then identifies the image of a transposed
idempotent with the contragredient of its original image, preserving the
coefficient label as required in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace Representation.IntertwiningMap

variable {R G V W : Type*} [CommSemiring R] [Group G]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- Transpose an intertwiner to a map between the contragredient representations. -/
def dual (f : IntertwiningMap ρ σ) : IntertwiningMap σ.dual ρ.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' g := by
    ext φ v
    exact congrArg φ (f.isIntertwining ρ σ g⁻¹ v).symm

@[simp]
theorem dual_apply (f : IntertwiningMap ρ σ) (φ : Module.Dual R W) (v : V) :
    dual f φ v = φ (f v) := rfl

/-- Dualizing an equivariant projector preserves its image up to canonical contragredient equivalence. -/
def dualRangeEquiv (e : IntertwiningMap ρ ρ) (he : IsIdempotentElem e.toLinearMap) :
    (dual e).range.toRepresentation.Equiv e.range.toRepresentation.dual :=
  .mk (LinearMap.dualProjectorRangeEquiv e.toLinearMap he) (by
    intro g
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro v
    rfl)

@[simp]
theorem dualRangeEquiv_apply (e : IntertwiningMap ρ ρ) (he : IsIdempotentElem e.toLinearMap)
    (φ : (dual e).range) (v : e.range) : dualRangeEquiv e he φ v = (φ : Module.Dual R V) v := rfl

end Representation.IntertwiningMap

namespace Representation.Equiv

variable {R G ι : Type*} [CommSemiring R] [Monoid G]
  {V W : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)]
  [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)]
  {ρ : (i : ι) → Representation R G (V i)} {σ : (i : ι) → Representation R G (W i)}

/-- Coordinatewise equivariant isomorphisms induce an equivariant isomorphism of products. -/
def pi (e : (i : ι) → (ρ i).Equiv (σ i)) :
    (Representation.pi ρ).Equiv (Representation.pi σ) :=
  .mk (LinearEquiv.piCongrRight fun i => (e i).toLinearEquiv) (by
    intro g
    apply LinearMap.ext
    intro v
    funext i
    exact (e i).toIntertwiningMap.isIntertwining (ρ i) (σ i) g (v i))

end Representation.Equiv
