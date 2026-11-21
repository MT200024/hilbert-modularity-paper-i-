/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Irreducible

/-! # Subrepresentations under surjective restriction

Restriction along a surjective group homomorphism retains the invariant
submodules. This applies to generic arithmetic monodromy on a normal base.
-/

@[expose] public section
namespace Representation
variable {R G H V : Type*} [Field R] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module R V]

/-- Restriction along a surjection identifies the complete orders of invariant submodules. -/
def subrepresentationOrderIsoOfSurjective (ρ : Representation R G V)
    (f : H →* G) (hf : Function.Surjective f) :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp f) where
  toFun S := ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (f h) hv⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => by
    obtain ⟨h, rfl⟩ := hf g
    exact S.apply_mem_toSubmodule h hv⟩
  left_inv S := Subrepresentation.toSubmodule_injective rfl
  right_inv S := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

/-- A representation is irreducible exactly when its restriction along a surjection is. -/
theorem isIrreducible_comp_iff_of_surjective (ρ : Representation R G V)
    (f : H →* G) (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f) ↔ ρ.IsIrreducible :=
  OrderIso.isSimpleOrder_iff (ρ.subrepresentationOrderIsoOfSurjective f hf).symm

namespace Equiv

variable {W : Type*} [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- An equivalence of restricted representations is equivariant for the full
group when the restricting homomorphism is surjective. -/
def ofCompSurjective (f : H →* G) (hf : Function.Surjective f)
    (e : Representation.Equiv (ρ.comp f) (σ.comp f)) : ρ.Equiv σ :=
  .mk e.toLinearEquiv (by
    intro g
    obtain ⟨h, rfl⟩ := hf g
    exact e.isIntertwining' h)

/-- Restriction retains the underlying linear equivalence and intertwining law. -/
def compHom (e : ρ.Equiv σ) (f : H →* G) :
    Representation.Equiv (ρ.comp f) (σ.comp f) :=
  .mk e.toLinearEquiv (fun h => e.isIntertwining' (f h))

end Equiv

end Representation
