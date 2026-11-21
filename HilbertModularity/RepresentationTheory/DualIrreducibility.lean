/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.DualSubquotient
public import HilbertModularity.RepresentationTheory.DualLattice
public import Mathlib.RepresentationTheory.Irreducible

/-! # Irreducibility under contragredient duality

Invariant annihilators reverse the subrepresentation lattice in finite dimension.
This transports the cusp irreducibility argument to the cohomological convention.
-/

public noncomputable section

namespace Subrepresentation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  {ρ : Representation K G V}

/-- The invariant coannihilator of a subspace in the contragredient representation. -/
def dualCoannihilator (S : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro φ hφ
    have h := hv (ρ.dual g⁻¹ φ) (S.apply_mem_toSubmodule g⁻¹ hφ)
    simpa only [Representation.dual_apply, Module.Dual.transpose_apply, inv_inv, LinearMap.comp_apply] using h

/-- Finite-dimensional invariant subspaces and their annihilators are order dual. -/
def dualAnnihilatorOrderIso [FiniteDimensional K V] (ρ : Representation K G V) :
    Subrepresentation ρ ≃o (Subrepresentation ρ.dual)ᵒᵈ where
  toFun S := S.dualAnnihilator
  invFun S := S.dualCoannihilator
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    exact Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    exact Subspace.dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := by
    intro S T
    constructor
    · intro h v hv
      change v ∈ T.toSubmodule
      rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := T.toSubmodule)]
      rw [Submodule.mem_dualCoannihilator]
      intro φ hφ
      have hφS : φ ∈ S.toSubmodule.dualAnnihilator := h hφ
      rw [Submodule.mem_dualAnnihilator] at hφS
      exact hφS v hv
    · intro h φ hφ
      change φ ∈ S.toSubmodule.dualAnnihilator
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      change φ ∈ T.toSubmodule.dualAnnihilator at hφ
      rw [Submodule.mem_dualAnnihilator] at hφ
      exact hφ v (h hv)

end Subrepresentation

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- Restriction of a contragredient is the contragredient of the restricted action. -/
theorem dual_compHom {H : Type*} [Group H] (ρ : Representation K G V) (f : H →* G) :
    (Representation.dual ρ).comp f = Representation.dual (ρ.comp f) := by
  apply MonoidHom.ext
  intro g
  change (ρ ((f g)⁻¹)).dualMap = (ρ (f g⁻¹)).dualMap
  rw [f.map_inv]

/-- The finite-dimensional contragredient of an irreducible action is irreducible. -/
theorem isIrreducible_dual (ρ : Representation K G V) [ρ.IsIrreducible] :
    ρ.dual.IsIrreducible := by
  have : IsSimpleOrder (Subrepresentation ρ.dual)ᵒᵈ :=
    (OrderIso.isSimpleOrder_iff (Subrepresentation.dualAnnihilatorOrderIso ρ)).mp
      (inferInstance : IsSimpleOrder (Subrepresentation ρ))
  have : Nontrivial (Subrepresentation ρ.dual) :=
    inferInstanceAs (Nontrivial (Subrepresentation ρ.dual)ᵒᵈ)
  exact ⟨fun S => (eq_bot_or_eq_top (α := (Subrepresentation ρ.dual)ᵒᵈ) S).symm⟩

/-- Absolute irreducibility is preserved by finite-dimensional contragredient duality. -/
theorem isIrreducible_dual_baseChange (M : Type*) [Field M] [Algebra K M]
    (ρ : Representation K G V) [(ρ.baseChange M).IsIrreducible] :
    (ρ.dual.baseChange M).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (dualBaseChangeEquiv M ρ).subrepresentationOrderIso).mpr
    (isIrreducible_dual (ρ.baseChange M))

end Representation
