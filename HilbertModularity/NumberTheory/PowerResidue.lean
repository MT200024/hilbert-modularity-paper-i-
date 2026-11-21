/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicResidue
public import Mathlib.Data.Fintype.EquivFin
public import HilbertModularity.NumberTheory.CharacterGenerator

@[expose] public section

/-! # The distinguished power-residue character

Reduction identifies the groups of roots of unity at every prime away from the order.
The inverse identification lifts the appropriate power in the residue field uniquely.
-/

namespace rootsOfUnity

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The homomorphism on roots of unity induced by a coefficient homomorphism. -/
def mapHom (N : ℕ) [NeZero N] (f : R →+* S) : rootsOfUnity N R →* rootsOfUnity N S where
  toFun z := mkOfPowEq (f (z : Rˣ)) (by
    rw [← map_pow, (mem_rootsOfUnity' N (z : Rˣ)).mp z.property, map_one])
  map_one' := by apply coe_injective; exact map_one f
  map_mul' x y := by apply coe_injective; exact map_mul f ((x : Rˣ) : R) ((y : Rˣ) : R)

@[simp] theorem coe_mapHom (N : ℕ) [NeZero N] (f : R →+* S) (z : rootsOfUnity N R) :
    ((mapHom N f z : Sˣ) : S) = f (z : Rˣ) := rfl

/-- A homomorphism preserving a primitive root induces an isomorphism on all roots
of that order, even when the coefficient homomorphism is not injective. -/
theorem mapHom_bijective [IsDomain R] [IsDomain S] (N : ℕ) [NeZero N]
    (f : R →+* S) {z : R} (hz : IsPrimitiveRoot z N) (hfz : IsPrimitiveRoot (f z) N) :
    Function.Bijective (mapHom N f) := by
  classical
  have hs : Function.Surjective (mapHom N f) := by
    intro w
    obtain ⟨i, _, hi⟩ := hfz.eq_pow_of_pow_eq_one
      ((mem_rootsOfUnity' N (w : Sˣ)).mp w.property)
    refine ⟨hz.toRootsOfUnity ^ i, ?_⟩
    apply coe_injective
    simpa only [coe_mapHom, rootsOfUnity.coe_pow, hz.val_toRootsOfUnity_coe, map_pow] using hi
  let := Fintype.ofFinite (rootsOfUnity N R)
  let := Fintype.ofFinite (rootsOfUnity N S)
  have hc : Fintype.card (rootsOfUnity N R) = Fintype.card (rootsOfUnity N S) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hz.card_rootsOfUnity, hfz.card_rootsOfUnity]
  exact ⟨hs.injective_of_finite (Fintype.equivOfCardEq hc), hs⟩

end rootsOfUnity

namespace HilbertModularity.Cyclotomic

open scoped NumberField
attribute [local instance] Ideal.Quotient.field

noncomputable section

/-- The fixed algebraic embedding of the cyclotomic integer ring. -/
def integerCoefficientMap (N : ℕ) [NeZero N] : 𝓞 (cyclotomicField N) →+* Qbar :=
  (cyclotomicField N).val.toRingHom.comp
    (algebraMap (𝓞 (cyclotomicField N)) (cyclotomicField N))

/-- Every algebraic `N`th root of unity lies in the cyclotomic integer ring. -/
def rootValueEquiv (N : ℕ) [NeZero N] :
    rootsOfUnity N (𝓞 (cyclotomicField N)) ≃* rootsOfUnity N Qbar :=
  MulEquiv.ofBijective (rootsOfUnity.mapHom N (integerCoefficientMap N))
    (rootsOfUnity.mapHom_bijective N _ (rootInteger_isPrimitiveRoot N)
      (zeta_isPrimitiveRoot N))

/-- Reduction is an isomorphism on `N`th roots of unity at a prime away from `N`. -/
def residueRootsEquiv (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    rootsOfUnity N (𝓞 (cyclotomicField N)) ≃* rootsOfUnity N (𝓞 (cyclotomicField N) ⧸ P) :=
  MulEquiv.ofBijective (rootsOfUnity.mapHom N (Ideal.Quotient.mk P))
    (rootsOfUnity.mapHom_bijective N _ (rootInteger_isPrimitiveRoot N)
      (rootInteger_reduction_isPrimitiveRoot N P hP))

/-- Reduction on algebraic roots of unity, using the fixed coefficient embedding. -/
def algebraicRootReduction (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    rootsOfUnity N Qbar ≃* rootsOfUnity N (𝓞 (cyclotomicField N) ⧸ P) :=
  (rootValueEquiv N).symm.trans (residueRootsEquiv N P hP)

/-- The power map from the residue multiplicative group into its `N`th roots of unity. -/
def residuePower (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    (𝓞 (cyclotomicField N) ⧸ P)ˣ →* rootsOfUnity N (𝓞 (cyclotomicField N) ⧸ P) where
  toFun x := ⟨x ^ ((Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1) / N), by
    rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel (dvd_residue_card_sub_one N P hP)]
    classical
    let := Fintype.ofFinite (𝓞 (cyclotomicField N) ⧸ P)
    rw [Nat.card_eq_fintype_card, ← Fintype.card_units]
    exact pow_card_eq_one⟩
  map_one' := Subtype.ext (one_pow _)
  map_mul' x y := Subtype.ext (mul_pow x y _)

/-- The distinguished power-residue character, with values in algebraic `N`th roots
of unity and the manuscript's positive power convention. -/
def powerResidueCharacter (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    (𝓞 (cyclotomicField N) ⧸ P)ˣ →* rootsOfUnity N Qbar :=
  (algebraicRootReduction N P hP).symm.toMonoidHom.comp (residuePower N P hP)

/-- The defining reduction property of the distinguished character. -/
@[simp] theorem powerResidueCharacter_reduction (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) (x : (𝓞 (cyclotomicField N) ⧸ P)ˣ) :
    algebraicRootReduction N P hP (powerResidueCharacter N P hP x) = residuePower N P hP x :=
  (algebraicRootReduction N P hP).apply_symm_apply _

/-- In the residue multiplicative group, the reduction is exactly the prescribed power. -/
theorem powerResidueCharacter_reduction_val (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) (x : (𝓞 (cyclotomicField N) ⧸ P)ˣ) :
    (algebraicRootReduction N P hP (powerResidueCharacter N P hP x) :
      (𝓞 (cyclotomicField N) ⧸ P)ˣ) =
      x ^ ((Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1) / N) :=
  congrArg Subtype.val (powerResidueCharacter_reduction N P hP x)

/-- The reduction property uniquely determines the character. -/
theorem powerResidueCharacter_unique (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P)
    (χ : (𝓞 (cyclotomicField N) ⧸ P)ˣ →* rootsOfUnity N Qbar)
    (hχ : ∀ x, algebraicRootReduction N P hP (χ x) = residuePower N P hP x) :
    χ = powerResidueCharacter N P hP := by
  apply MonoidHom.ext
  intro x
  apply (algebraicRootReduction N P hP).injective
  rw [hχ, powerResidueCharacter_reduction]

/-- The distinguished character extended by zero, as required in Gauss sums. -/
def powerResidueMulChar (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    MulChar (𝓞 (cyclotomicField N) ⧸ P) Qbar :=
  MulChar.ofUnitHom ((rootsOfUnity N Qbar).subtype.comp (powerResidueCharacter N P hP))

@[simp] theorem powerResidueMulChar_apply_unit (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) (x : (𝓞 (cyclotomicField N) ⧸ P)ˣ) :
    powerResidueMulChar N P hP x = ((powerResidueCharacter N P hP x : Qbarˣ) : Qbar) :=
  MulChar.ofUnitHom_coe _ x

@[simp] theorem powerResidueMulChar_zero (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) : powerResidueMulChar N P hP 0 = 0 :=
  MulChar.map_zero _

/-- The inverse character reduces to the negative power, fixing the opposite
arithmetic power-residue convention unambiguously. -/
theorem powerResidueCharacter_inverse_reduction (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) (x : (𝓞 (cyclotomicField N) ⧸ P)ˣ) :
    (algebraicRootReduction N P hP ((powerResidueCharacter N P hP x)⁻¹) :
      (𝓞 (cyclotomicField N) ⧸ P)ˣ) =
      (x ^ ((Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1) / N))⁻¹ := by
  rw [map_inv]
  exact congrArg Inv.inv (powerResidueCharacter_reduction_val N P hP x)

/-- The distinguished multiplicative character has exactly the specified order. -/
theorem powerResidueMulChar_orderOf (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    orderOf (powerResidueMulChar N P hP) = N := by
  classical
  let := Fintype.ofFinite (𝓞 (cyclotomicField N) ⧸ P)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓞 (cyclotomicField N) ⧸ P)ˣ)
  have hgorder : orderOf g = Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units, Nat.card_eq_fintype_card]
  have hpower : orderOf (g ^ ((Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1) / N)) = N := by
    rw [← hgorder]
    exact orderOf_pow_orderOf_div (orderOf_pos g).ne'
      (hgorder.symm ▸ dvd_residue_card_sub_one N P hP)
  rw [← MulChar.orderOf_apply_generator _ hg, powerResidueMulChar_apply_unit,
    orderOf_units]
  rw [Subgroup.orderOf_coe, ← (algebraicRootReduction N P hP).orderOf_eq,
    powerResidueCharacter_reduction, ← Subgroup.orderOf_coe]
  exact hpower

/-- A generator of the full character group compatible with the distinguished
power-residue convention exists at every prime away from the level. -/
theorem exists_compatible_generator (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    ∃ ω : MulChar (𝓞 (cyclotomicField N) ⧸ P) Qbar,
      orderOf ω = Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1 ∧
      ω ^ ((Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1) / N) =
        powerResidueMulChar N P hP := by
  classical
  let := Fintype.ofFinite (𝓞 (cyclotomicField N) ⧸ P)
  have : NeZero (Fintype.card (𝓞 (cyclotomicField N) ⧸ P) - 1) :=
    ⟨by have := Fintype.one_lt_card (α := 𝓞 (cyclotomicField N) ⧸ P); omega⟩
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.exists_generator_pow_eq (powerResidueMulChar N P hP)
      (powerResidueMulChar_orderOf N P hP)
      (by simpa only [Nat.card_eq_fintype_card] using dvd_residue_card_sub_one N P hP)
      (zeta_isPrimitiveRoot (Fintype.card (𝓞 (cyclotomicField N) ⧸ P) - 1))

/-- A generator of the residue-field character group whose level-th component
is the distinguished positive power-residue character. -/
def powerResidueGenerator (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    MulChar (𝓞 (cyclotomicField N) ⧸ P) Qbar :=
  (exists_compatible_generator N P hP).choose

theorem powerResidueGenerator_orderOf (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    orderOf (powerResidueGenerator N P hP) = Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1 :=
  (exists_compatible_generator N P hP).choose_spec.1

theorem powerResidueGenerator_pow (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    powerResidueGenerator N P hP ^ ((Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1) / N) =
      powerResidueMulChar N P hP :=
  (exists_compatible_generator N P hP).choose_spec.2

end

end HilbertModularity.Cyclotomic
