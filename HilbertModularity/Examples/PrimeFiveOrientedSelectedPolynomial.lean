/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveOrientedSelectedFiber
public import HilbertModularity.Examples.PrimeFiveSelectedPolynomialFortyOne

/-! # Selected special polynomials at the oriented example primes

The cyclotomic primes fixed by the manuscript's power-residue characters
contract to the real primes where the selected plus Jacobian has the counted
special-fibre polynomials. The numerical properties are proved in the preceding
modules and use the same selected model witness here.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hyperelliptic GroupScheme

attribute [local instance] Ideal.Quotient.field
@[instance_reducible] local instance orientedPolynomialQuotientCommRing
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5))) :
    CommRing (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) :=
  (Ideal.Quotient.field P.asIdeal).toCommRing
local instance orientedPolynomialResidueFintype
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5))) :
    Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) := Fintype.ofFinite _
local instance orientedPolynomialFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance orientedPolynomialElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance orientedPolynomialFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The character orientation `ζ₅ ↦ 4` lies over a real prime of size 11
where the actual selected special Jacobian has its full polynomial. -/
theorem exists_primeFive_orientedSelectedSpecialPolynomial_11 :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      ∃ _hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal,
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) = 11 ∧
        (∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4) ∧
        ∃ W : PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P),
          RawSpecialPolynomial11
            (𝓞 (realCyclotomicField 5) ⧸ (primeFiveRealPrimeBelow P).asIdeal)
            (selectedPointedData (primeFiveRealPrimeBelow P) W).jacobian := by
  obtain ⟨P, hP, hcard, he, ⟨W⟩⟩ :=
    exists_primeFive_orientedSelectedSpecialFiber_11
  let q := primeFiveRealPrimeBelow P
  let k := 𝓞 (realCyclotomicField 5) ⧸ q.asIdeal
  let : Fintype k := Fintype.ofFinite k
  have hk : Fintype.card k = 11 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  exact ⟨P, hP, hcard, he, W, selectedRawSpecialPolynomial11 q W hk⟩

/-- The character orientation `ζ₅ ↦ 10` yields the forty-one-prime
selected special Jacobian polynomial at its contracted real prime. -/
theorem exists_primeFive_orientedSelectedSpecialPolynomial_41 :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      ∃ _hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal,
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) = 41 ∧
        (∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10) ∧
        ∃ W : PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P),
          RawSpecialPolynomial41
            (𝓞 (realCyclotomicField 5) ⧸ (primeFiveRealPrimeBelow P).asIdeal)
            (selectedPointedData (primeFiveRealPrimeBelow P) W).jacobian := by
  obtain ⟨P, hP, hcard, he, ⟨W⟩⟩ :=
    exists_primeFive_orientedSelectedSpecialFiber_41
  let q := primeFiveRealPrimeBelow P
  let k := 𝓞 (realCyclotomicField 5) ⧸ q.asIdeal
  let : Fintype k := Fintype.ofFinite k
  have hk : Fintype.card k = 41 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  exact ⟨P, hP, hcard, he, W, selectedRawSpecialPolynomial41 q W hk⟩

end HilbertModularity.Examples
