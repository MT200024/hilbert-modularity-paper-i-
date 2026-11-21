/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.DualIrreducibility
public import Mathlib.RepresentationTheory.Semisimple

/-! # Semisimplicity of labelled factors

Equivalences, invariant subspaces and contragredient duality preserve
semisimplicity. These are the transports needed for the actual RM Tate factors.
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- An equivariant coordinate change preserves trivial action at an element. -/
theorem Equiv.apply_eq_one_of {ρ : Representation K G V}
    {τ : Representation K G W} (e : ρ.Equiv τ) (g : G) (h : τ g = 1) :
    ρ g = 1 := by
  have he := e.symm.conj_apply_self g
  rw [h] at he
  calc
    ρ g = e.symm.toLinearEquiv.conj 1 := he.symm
    _ = 1 := by
      ext x
      exact e.toLinearEquiv.symm_apply_apply x

/-- An equivariant isomorphism preserves complements of invariant subspaces. -/
theorem Equiv.isSemisimple_iff {ρ : Representation K G V}
    {τ : Representation K G W} (e : ρ.Equiv τ) :
    ρ.IsSemisimpleRepresentation ↔ τ.IsSemisimpleRepresentation :=
  OrderIso.complementedLattice_iff e.subrepresentationOrderIso

/-- A subrepresentation of a semisimple representation is semisimple. -/
theorem isSemisimple_subrepresentation (ρ : Representation K G V)
    (hρ : ρ.IsSemisimpleRepresentation) (S : Subrepresentation ρ) :
    S.toRepresentation.IsSemisimpleRepresentation := by
  let : IsSemisimpleModule K[G] ρ.asModule :=
    ρ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule.mp hρ
  let f : IntertwiningMap S.toRepresentation ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  apply S.toRepresentation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule.mpr
  exact IsSemisimpleModule.of_injective
    (IntertwiningMap.equivLinearMapAsModule S.toRepresentation ρ f) Subtype.val_injective

/-- Finite-dimensional contragredient duality preserves invariant complements. -/
theorem isSemisimple_dual (ρ : Representation K G V) [FiniteDimensional K V]
    (hρ : ρ.IsSemisimpleRepresentation) : ρ.dual.IsSemisimpleRepresentation := by
  have : ComplementedLattice (Subrepresentation ρ.dual)ᵒᵈ :=
    (OrderIso.complementedLattice_iff
      (Subrepresentation.dualAnnihilatorOrderIso ρ)).mp hρ
  refine ⟨fun S => ?_⟩
  obtain ⟨T, hT⟩ := exists_isCompl (α := (Subrepresentation ρ.dual)ᵒᵈ) S
  exact ⟨T, hT.dual⟩

end Representation
