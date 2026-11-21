/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveOrientedPrimes
public import HilbertModularity.Examples.PrimeFiveSelectedSpecialFiber

/-! # The oriented prime and the selected plus special fibre

The full-cyclotomic prime specifying the power-residue character contracts to
the same degree-one real prime at which the selected Jacobian is reduced.
The special fibre is the pointed Jacobian of the actual reduced plus curve.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

attribute [local instance] Ideal.Quotient.field
local instance orientedSelectedElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance orientedSelectedFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

private theorem two_away_of_card_eq_11
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hcard : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11) :
    (2 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal := by
  let k := 𝓞 (realCyclotomicField 5) ⧸ P.asIdeal
  let e : k ≃+* ZMod 11 :=
    FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hcard)
  intro h
  have hz : (2 : k) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr (by simpa using h)
  have he : (2 : ZMod 11) = 0 := by
    calc
      (2 : ZMod 11) = e (2 : k) := (map_ofNat e 2).symm
      _ = e 0 := congrArg e hz
      _ = 0 := map_zero e
  exact (by decide : (2 : ZMod 11) ≠ 0) he

private theorem two_away_of_card_eq_41
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hcard : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 41) :
    (2 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal := by
  let k := 𝓞 (realCyclotomicField 5) ⧸ P.asIdeal
  let e : k ≃+* ZMod 41 :=
    FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hcard)
  intro h
  have hz : (2 : k) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr (by simpa using h)
  have he : (2 : ZMod 41) = 0 := by
    calc
      (2 : ZMod 41) = e (2 : k) := (map_ofNat e 2).symm
      _ = e 0 := congrArg e hz
      _ = 0 := map_zero e
  exact (by decide : (2 : ZMod 41) ≠ 0) he

/-- At eleven the chosen character orientation and the actual special
Jacobian belong to the same contracted arithmetic prime. -/
theorem exists_primeFive_orientedSelectedSpecialFiber_11 :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      ∃ _hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal,
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) = 11 ∧
        (∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4) ∧
        Nonempty (PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P)) := by
  obtain ⟨P, hP, hcard, e, he⟩ := exists_primeFive_orientedPrime_11_withRealResidue
  let q := primeFiveRealPrimeBelow P
  let k := 𝓞 (realCyclotomicField 5) ⧸ q.asIdeal
  let : Fintype k := Fintype.ofFinite k
  have hk : Fintype.card k = 11 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have h2 := two_away_of_card_eq_11 q hk
  have hsep := primeFivePolynomial_separable_of_card_eq_11 hk
  exact ⟨P, hP, hcard, ⟨e, he⟩,
    exists_primeFiveSelectedSpecialJacobian q h2 hsep⟩

/-- The same construction at forty-one retains the reduced-root label ten
and the selected special Jacobian at its contracted real prime. -/
theorem exists_primeFive_orientedSelectedSpecialFiber_41 :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      ∃ _hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal,
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) = 41 ∧
        (∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10) ∧
        Nonempty (PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P)) := by
  obtain ⟨P, hP, hcard, e, he⟩ := exists_primeFive_orientedPrime_41_withRealResidue
  let q := primeFiveRealPrimeBelow P
  let k := 𝓞 (realCyclotomicField 5) ⧸ q.asIdeal
  let : Fintype k := Fintype.ofFinite k
  have hk : Fintype.card k = 41 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have h2 := two_away_of_card_eq_41 q hk
  have hsep := primeFivePolynomial_separable_of_card_eq_41 hk
  exact ⟨P, hP, hcard, ⟨e, he⟩,
    exists_primeFiveSelectedSpecialJacobian q h2 hsep⟩

end HilbertModularity.Examples
