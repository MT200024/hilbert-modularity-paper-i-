/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FixedLine
public import HilbertModularity.RepresentationTheory.Duality
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Contragredient subquotients

The annihilator of an invariant subspace is invariant under the actual
contragredient action. Dualizing reverses the two factors of the flag and
inverts their one-dimensional characters, as used in
[TripathiGoswami, cohomological residual representation].
-/

@[expose] public noncomputable section

namespace Subrepresentation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  {ρ : Representation K G V} (S : Subrepresentation ρ)

/-- The invariant annihilator of a subrepresentation under the contragredient action. -/
def dualAnnihilator : Subrepresentation ρ.dual where
  toSubmodule := S.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g φ hφ := by
    rw [Submodule.mem_dualAnnihilator] at hφ ⊢
    intro v hv
    exact hφ (ρ g⁻¹ v) (S.apply_mem_toSubmodule g⁻¹ hv)

/-- The dual of the quotient is equivariantly the annihilator in the dual representation. -/
def dualQuotientEquiv :
    (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).dual.Equiv
      S.dualAnnihilator.toRepresentation :=
  .mk S.toSubmodule.dualQuotEquivDualAnnihilator (by
    intro g
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rfl)

/-- The quotient by the annihilator is equivariantly the dual of the original subspace. -/
def quotientDualAnnihilatorEquiv :
    (ρ.dual.quotient S.dualAnnihilator.toSubmodule
      S.dualAnnihilator.apply_mem_toSubmodule).Equiv S.toRepresentation.dual :=
  .mk (Subspace.quotAnnihilatorEquiv S.toSubmodule) (by
    intro g
    apply LinearMap.ext
    intro φ
    refine Submodule.Quotient.induction_on _ φ ?_
    intro φ
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply]
    rfl)

end Subrepresentation

namespace Representation

variable {K G : Type*} [Field K] [Group G]

/-- The contragredient of a character line is the line of its inverse character. -/
def dualCharacterEquiv (χ : G →* Kˣ) :
    (ofCharacter χ).dual.Equiv (ofCharacter χ⁻¹) :=
  .mk (LinearMap.ringLmapEquivSelf K K K) (by
    intro g
    apply LinearMap.ext
    intro φ
    change φ ((χ g⁻¹ : K) * 1) = ((χ⁻¹) g : K) * φ 1
    simpa using φ.map_smul (χ g⁻¹ : K) (1 : K))

end Representation

namespace Subrepresentation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  {ρ : Representation K G V} (S : Subrepresentation ρ)

/-- A character quotient becomes its inverse character on the annihilator in the dual. -/
def dualAnnihilatorCharacterEquiv (χ : G →* Kˣ)
    (e : (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).Equiv
      (Representation.ofCharacter χ)) :
    S.dualAnnihilator.toRepresentation.Equiv (Representation.ofCharacter χ⁻¹) :=
  S.dualQuotientEquiv.symm.trans
    ((HilbertModularity.representationDualEquiv e).trans (Representation.dualCharacterEquiv χ))

/-- A character subrepresentation becomes its inverse character in the dual quotient. -/
def quotientDualAnnihilatorCharacterEquiv (χ : G →* Kˣ)
    (e : S.toRepresentation.Equiv (Representation.ofCharacter χ)) :
    (ρ.dual.quotient S.dualAnnihilator.toSubmodule
      S.dualAnnihilator.apply_mem_toSubmodule).Equiv (Representation.ofCharacter χ⁻¹) :=
  S.quotientDualAnnihilatorEquiv.trans
    ((HilbertModularity.representationDualEquiv e).trans (Representation.dualCharacterEquiv χ))

end Subrepresentation

namespace Representation.Equiv

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Exchanging two direct-sum constituents is equivariant. -/
def prodComm (ρ : Representation K G V) (σ : Representation K G W) :
    (ρ.prod σ).Equiv (σ.prod ρ) :=
  .mk (LinearEquiv.prodComm K V W) (by intro g; apply LinearMap.ext; intro x; rfl)

end Representation.Equiv

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (ρ : Representation K G V)

/-- The contragredient of a rank-two representation with a fixed vector has an
actual invariant flag whose irreducible factors are the trivial character and
the inverse determinant character. -/
theorem exists_dual_fixedLine_factors (hV : Module.finrank K V = 2)
    (v : V) (hv : v ≠ 0) (hfix : ∀ g, ρ g v = v) :
    ∃ T : Subrepresentation ρ.dual,
      Module.finrank K T.toSubmodule = 1 ∧
      Module.finrank K (Module.Dual K V ⧸ T.toSubmodule) = 1 ∧
      Representation.IsIrreducible (k := K) (G := G) (V := T.toSubmodule)
        T.toRepresentation ∧
      Representation.IsIrreducible (k := K) (G := G)
        (V := Module.Dual K V ⧸ T.toSubmodule)
        (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule) ∧
      Representation.IsSemisimpleRepresentation (k := K) (G := G)
        (V := T.toSubmodule × (Module.Dual K V ⧸ T.toSubmodule))
        (T.toRepresentation.prod (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule)) ∧
      Nonempty ((T.toRepresentation.prod
        (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((ofCharacter (1 : G →* Kˣ)).prod (ofCharacter ρ.determinantCharacter⁻¹))) := by
  let S := fixedLine ρ v hfix
  let T := S.dualAnnihilator
  have hS : Module.finrank K S.toSubmodule = 1 := finrank_fixedLine ρ v hfix hv
  have hQ : Module.finrank K (V ⧸ S.toSubmodule) = 1 :=
    finrank_quotient_fixedLine ρ v hfix hv hV
  let b := Module.finBasisOfFinrankEq K S.toSubmodule hS
  let c := Module.finBasisOfFinrankEq K (V ⧸ S.toSubmodule) hQ
  let e₁ : T.toRepresentation.Equiv (ofCharacter ρ.determinantCharacter⁻¹) :=
    S.dualAnnihilatorCharacterEquiv ρ.determinantCharacter
    (quotientFixedLineEquiv ρ v hfix b c)
  have e₂ : (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule).Equiv
      (ofCharacter (1 : G →* Kˣ)) := by
    have hunit : (1 : G →* Kˣ)⁻¹ = 1 := by
      ext g
      simp
    have e := S.quotientDualAnnihilatorCharacterEquiv (1 : G →* Kˣ)
      (fixedLineEquiv ρ v hfix b)
    rw [hunit] at e
    exact e
  have hT : Module.finrank K T.toSubmodule = 1 := by
    simpa using e₁.toLinearEquiv.finrank_eq
  have hTQ : Module.finrank K (Module.Dual K V ⧸ T.toSubmodule) = 1 := by
    simpa using e₂.toLinearEquiv.finrank_eq
  let h₁ := isIrreducible_of_finrank_eq_one (K := K) (G := G)
    (V := T.toSubmodule) T.toRepresentation hT
  let h₂ := isIrreducible_of_finrank_eq_one (K := K) (G := G)
    (V := Module.Dual K V ⧸ T.toSubmodule)
    (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule) hTQ
  exact ⟨T, hT, hTQ, h₁, h₂,
    isSemisimple_prod (K := K) (G := G) (V := T.toSubmodule)
      (W := Module.Dual K V ⧸ T.toSubmodule) T.toRepresentation
      (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule),
    ⟨(Equiv.prod (K := K) (G := G) (V := T.toSubmodule)
      (W := Module.Dual K V ⧸ T.toSubmodule) (V' := K) (W' := K) e₁ e₂).trans
        (Equiv.prodComm (ofCharacter ρ.determinantCharacter⁻¹) (ofCharacter (1 : G →* Kˣ)))⟩⟩

end Representation
