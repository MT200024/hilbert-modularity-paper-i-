/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveEulerTransport
public import HilbertModularity.Examples.PrimeFiveOrientedSelectedFiber

/-! # The oriented finite sums and the same selected Jacobian fibres

At each worked prime, one full-cyclotomic prime determines both the actual
power-residue character and the degree-one real prime where the selected plus
Jacobian has the reduced pointed-Jacobian model. The direct McCarthy value is
then evaluated with that character and the fixed complex coefficient embedding.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

attribute [local instance] Ideal.Quotient.field
local instance workedFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance workedElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance workedFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The first direct McCarthy value and the actual selected special fibre
share one oriented prime above eleven. -/
theorem exists_primeFive_workedPrime_11 :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      ∃ hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal,
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) = 11 ∧
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4 ∧
          Nonempty (PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P)) ∧
          ∀ θ : AddChar (ZMod 11) ℂ, θ ≠ 1 →
            Hypergeometric.rankTwoMcCarthySum θ
              (primeFiveComplexCharacter11 P.asIdeal hP e primeFiveComplexEmbedding) 125 =
                ((Real.sqrt 5 : ℂ) - 1) / 2 ∧
              primeFiveComplexEmbedding
                (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1 (e.symm 125)) =
                  ((Real.sqrt 5 : ℂ) - 1) / 2 := by
  obtain ⟨P, hP, hcard, ⟨e, he⟩, hW⟩ :=
    exists_primeFive_orientedSelectedSpecialFiber_11
  exact ⟨P, hP, hcard, e, he, hW,
    fun θ hθ => ⟨primeFiveComplexCharacter11_mccarthyValue P.asIdeal hP e he θ hθ,
      primeFive_orientedEulerValue_11 P.asIdeal hP e he θ hθ⟩⟩

/-- The second direct value uses the same construction and orientation at
forty-one, with no new numeric literature input. -/
theorem exists_primeFive_workedPrime_41 :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      ∃ hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal,
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) = 41 ∧
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10 ∧
          Nonempty (PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P)) ∧
          ∀ θ : AddChar (ZMod 41) ℂ, θ ≠ 1 →
            Hypergeometric.rankTwoMcCarthySum θ
              (primeFiveComplexCharacter41 P.asIdeal hP e primeFiveComplexEmbedding) 125 =
                (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧
              primeFiveComplexEmbedding
                (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1 (e.symm 125)) =
                  (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 := by
  obtain ⟨P, hP, hcard, ⟨e, he⟩, hW⟩ :=
    exists_primeFive_orientedSelectedSpecialFiber_41
  exact ⟨P, hP, hcard, e, he, hW,
    fun θ hθ => ⟨primeFiveComplexCharacter41_mccarthyValue P.asIdeal hP e he θ hθ,
      primeFive_orientedEulerValue_41 P.asIdeal hP e he θ hθ⟩⟩

end HilbertModularity.Examples
