/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveOrientedPrimes
public import HilbertModularity.Hypergeometric.FrobeniusComparison
import Mathlib.Tactic.NormNum

/-! # The actual power-residue character at the oriented fifth-cyclotomic primes

The specified reduced roots and positive residue power determine the
character value. No curve Frobenius trace is used here.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic

attribute [local instance] Ideal.Quotient.field
local instance orientedCharacterFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance orientedCharacterElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance orientedCharacterFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- A full prime with ζ₅ reducing to four gives the prescribed positive
power-residue value on the generator two. -/
theorem primeFive_orientedPowerResidue_11
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4) :
    (cyclotomicField 5).val
      (cyclotomicPowerResidueMulChar 5 P hP (e.symm 2)) =
        (cyclotomicField 5).val (root 5) := by
  let k := 𝓞 (cyclotomicField 5) ⧸ P
  have htwo : e.symm (2 : ZMod 11) ≠ 0 := by
    intro h
    have heq : (2 : ZMod 11) = 0 := by simpa using congrArg e h
    exact (by decide : (2 : ZMod 11) ≠ 0) heq
  let u : kˣ := Units.mk0 (e.symm 2) htwo
  have hu : (u : k) = e.symm 2 := rfl
  let : Fintype k := Fintype.ofFinite k
  have hcard : Nat.card k = 11 := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using
      Fintype.card_congr e.toEquiv
  have hpow : ((u ^ ((Nat.card k - 1) / 5) : kˣ) : k) =
      Ideal.Quotient.mk P (rootInteger 5) := by
    apply e.injective
    simp only [Units.val_pow_eq_pow_val, hu, map_pow,
      e.apply_symm_apply, hcard, primeFive_generator11_residuePower, he]
  let zI : rootsOfUnity 5 (𝓞 (cyclotomicField 5)) :=
    (rootInteger_isPrimitiveRoot 5).toRootsOfUnity
  let zQ : rootsOfUnity 5 Qbar := rootValueEquiv 5 zI
  have hred : residuePower 5 P hP u = residueRootsEquiv 5 P hP zI := by
    apply Subtype.ext
    apply Units.ext
    simpa [residuePower, residueRootsEquiv, zI] using hpow
  have hχ : powerResidueCharacter 5 P hP u = zQ := by
    apply (algebraicRootReduction 5 P hP).injective
    rw [powerResidueCharacter_reduction]
    simpa [algebraicRootReduction, zQ] using hred
  rw [cyclotomicPowerResidueMulChar_val]
  change powerResidueMulChar 5 P hP u = _
  rw [powerResidueMulChar_apply_unit, hχ]
  rfl

/-- The positive power-residue value on six at an oriented prime above
forty-one is the same chosen fifth root. -/
theorem primeFive_orientedPowerResidue_41
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10) :
    (cyclotomicField 5).val
      (cyclotomicPowerResidueMulChar 5 P hP (e.symm 6)) =
        (cyclotomicField 5).val (root 5) := by
  let k := 𝓞 (cyclotomicField 5) ⧸ P
  have hsix : e.symm (6 : ZMod 41) ≠ 0 := by
    intro h
    have heq : (6 : ZMod 41) = 0 := by simpa using congrArg e h
    exact (by decide : (6 : ZMod 41) ≠ 0) heq
  let u : kˣ := Units.mk0 (e.symm 6) hsix
  have hu : (u : k) = e.symm 6 := rfl
  let : Fintype k := Fintype.ofFinite k
  have hcard : Nat.card k = 41 := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using
      Fintype.card_congr e.toEquiv
  have hpow : ((u ^ ((Nat.card k - 1) / 5) : kˣ) : k) =
      Ideal.Quotient.mk P (rootInteger 5) := by
    apply e.injective
    simp only [Units.val_pow_eq_pow_val, hu, map_pow,
      e.apply_symm_apply, hcard, primeFive_generator41_residuePower, he]
  let zI : rootsOfUnity 5 (𝓞 (cyclotomicField 5)) :=
    (rootInteger_isPrimitiveRoot 5).toRootsOfUnity
  let zQ : rootsOfUnity 5 Qbar := rootValueEquiv 5 zI
  have hred : residuePower 5 P hP u = residueRootsEquiv 5 P hP zI := by
    apply Subtype.ext
    apply Units.ext
    simpa [residuePower, residueRootsEquiv, zI] using hpow
  have hχ : powerResidueCharacter 5 P hP u = zQ := by
    apply (algebraicRootReduction 5 P hP).injective
    rw [powerResidueCharacter_reduction]
    simpa [algebraicRootReduction, zQ] using hred
  rw [cyclotomicPowerResidueMulChar_val]
  change powerResidueMulChar 5 P hP u = _
  rw [powerResidueMulChar_apply_unit, hχ]
  rfl

/-- The normalized value at two already lies in the chosen cyclotomic
coefficient field, with its fixed root rather than a conjugate. -/
theorem primeFive_orientedCyclotomicCharacter_11
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4) :
    cyclotomicPowerResidueMulChar 5 P hP (e.symm 2) = root 5 :=
  (cyclotomicField 5).val.injective (primeFive_orientedPowerResidue_11 P hP e he)

/-- The corresponding normalized value at six at forty-one. -/
theorem primeFive_orientedCyclotomicCharacter_41
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10) :
    cyclotomicPowerResidueMulChar 5 P hP (e.symm 6) = root 5 :=
  (cyclotomicField 5).val.injective (primeFive_orientedPowerResidue_41 P hP e he)

end HilbertModularity.Examples
