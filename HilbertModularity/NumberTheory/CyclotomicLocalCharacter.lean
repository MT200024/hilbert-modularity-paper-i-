/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicLocalGalois
public import HilbertModularity.NumberTheory.CyclotomicCharacter

/-! # Cyclotomic compatibility of the actual local Galois restriction

The local-to-global map defined by the embedded algebraic closure preserves
the action on all prime-power roots of unity. Thus the restricted global
cyclotomic character is the intrinsic continuous character of the actual local
Galois group, as needed in [TripathiGoswami, local ordinary characters].
-/

@[expose] public noncomputable section

namespace cyclotomicCharacter

/-- An equivariant embedding of fields preserves the actual prime-adic cyclotomic character. -/
theorem eq_of_equivariant_embedding {E D : Type*} [Field E] [Field D]
    (p : ℕ) [Fact p.Prime]
    [∀ n, HasEnoughRootsOfUnity E (p ^ n)] [∀ n, HasEnoughRootsOfUnity D (p ^ n)]
    (f : E →+* D) (g : E ≃+* E) (h : D ≃+* D)
    (hf : ∀ x, f (g x) = h (f x)) :
    _root_.cyclotomicCharacter E p g = _root_.cyclotomicCharacter D p h := by
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro ζ hζ
  apply f.injective
  rw [hf, map_pow]
  apply cyclotomicCharacter.spec
  rw [← map_pow, (mem_rootsOfUnity' _ _).mp hζ, map_one]

end cyclotomicCharacter

namespace HilbertModularity.Cyclotomic
open IntermediateField
variable (p k : ℕ) [Fact p.Prime]
attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerPadicAlgebra realPrimePowerPadicTower
  realPrimePowerAlgebraicClosurePadicAlgebra realPrimePowerAlgebraicClosurePadicTower

/-- The intrinsic continuous cyclotomic character on the actual local Galois group. -/
def realPrimePowerLocalCyclotomicCharacter :
    Gal(PadicAlgCl p/RealPrimePowerCompletion p k) →ₜ* ℤ_[p]ˣ where
  __ := (_root_.cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut Gal(PadicAlgCl p/RealPrimePowerCompletion p k) (PadicAlgCl p))
  continuous_toFun := _root_.cyclotomicCharacter.continuous p (RealPrimePowerCompletion p k)
    (PadicAlgCl p)

/-- The actual global cyclotomic character restricts to the intrinsic local root-of-unity character. -/
theorem cyclotomicCharacter_realPrimePowerLocalGaloisRestriction
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p k)) :
    Field.cyclotomicCharacter (realCyclotomicField (p ^ (k + 1))) p
      (realPrimePowerLocalGaloisRestriction p k g) = realPrimePowerLocalCyclotomicCharacter p k g := by
  exact cyclotomicCharacter.eq_of_equivariant_embedding p
    (realPrimePowerAlgebraicClosureEmbedding p k).toRingHom
    (realPrimePowerLocalGaloisRestriction p k g).toRingEquiv g.toRingEquiv
    (realPrimePowerLocalGaloisRestriction_commutes p k g)

end HilbertModularity.Cyclotomic
