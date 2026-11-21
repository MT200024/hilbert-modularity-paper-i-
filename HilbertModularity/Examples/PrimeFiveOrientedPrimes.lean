/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSplitPrimes
public import HilbertModularity.NumberTheory.CyclotomicResidue
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic.IntervalCases

/-! # Orientation of the fifth root at the worked primes

The standard cyclotomic prime correspondence permits a specified primitive
fifth root in the residue field. This chooses the arithmetic prime needed
for the manuscript's character convention, before any curve trace is used.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic

local instance orientedPrimeFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance orientedPrimeRealToFullAlgebra :
    Algebra (realCyclotomicField 5) (cyclotomicField 5) :=
  (IntermediateField.inclusion (realCyclotomicField_le 5)).toRingHom.toAlgebra

/-- The real prime contracted from an oriented full-cyclotomic prime. -/
def primeFiveRealPrimeBelow
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5))) :
    HeightOneSpectrum (𝓞 (realCyclotomicField 5)) :=
  P.under (𝓞 (realCyclotomicField 5))

/-- The contracted real prime has the original full prime as its ideal
extension. -/
theorem primeFiveRealPrimeBelow_asIdeal
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5))) :
    (primeFiveRealPrimeBelow P).asIdeal =
      P.asIdeal.under (𝓞 (realCyclotomicField 5)) := (rfl)

/-- [MilneANT, Proposition 6.2(b), printed pp.96–97; Example 8.18,
printed p.143]: a specified primitive fifth root `r` in the prime field
gives a full cyclotomic prime with reduced ζ₅ equal to `r`. Its contraction
to the real subfield retains residue cardinality `q`, since both residue
fields contain 𝔽_q and the full one equals 𝔽_q. This standard
Dedekind–Kummer corollary asserts no curve or labelled trace statement. -/
theorem exists_primeFive_cyclotomicPrime_with_reducedRoot_and_realResidue
    (q : ℕ) [Fact q.Prime] (hq5 : q ≠ 5) (hmod : q % 5 = 1)
    (r : ZMod q) (hr : IsPrimitiveRoot r 5) :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal ∧
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) = q ∧
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod q,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = r := by
  sorry

/-- [MilneANT, Proposition 6.2(b), printed pp.96–97; Example 8.18,
printed p.143]: O(Q(ζ₅))=Z[ζ₅], and at q≡1 mod5 the cyclotomic polynomial
splits into linear factors. Each specified primitive fifth root `r` in F_q
therefore gives an actual prime and residue-field equivalence carrying the
chosen integral ζ₅ to `r`. This is a standard Dedekind–Kummer/cyclotomic
corollary. It asserts no hypergeometric value, RM trace or label choice for
the comparison character. -/
theorem exists_primeFive_cyclotomicPrime_with_reducedRoot
    (q : ℕ) [Fact q.Prime] (hq5 : q ≠ 5) (hmod : q % 5 = 1)
    (r : ZMod q) (hr : IsPrimitiveRoot r 5) :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal ∧
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod q,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = r := by
  obtain ⟨P, hP, _, e, he⟩ :=
    exists_primeFive_cyclotomicPrime_with_reducedRoot_and_realResidue q hq5 hmod r hr
  exact ⟨P, hP, e, he⟩

/-- An oriented full prime above eleven and its actual degree-one real
prime use the same contraction. -/
theorem exists_primeFive_orientedPrime_11_withRealResidue :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal ∧
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) = 11 ∧
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact exists_primeFive_cyclotomicPrime_with_reducedRoot_and_realResidue 11
    (by decide) (by decide) 4 (by
      apply (IsPrimitiveRoot.iff (by decide)).mpr
      constructor
      · decide
      · intro j hj0 hj5
        interval_cases j <;> decide)

/-- The corresponding single full prime above forty-one gives a degree-one
real prime and the specified reduced fifth root. -/
theorem exists_primeFive_orientedPrime_41_withRealResidue :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal ∧
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) = 41 ∧
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10 := by
  let : Fact (Nat.Prime 41) := ⟨by decide⟩
  exact exists_primeFive_cyclotomicPrime_with_reducedRoot_and_realResidue 41
    (by decide) (by decide) 10 (by
      apply (IsPrimitiveRoot.iff (by decide)).mpr
      constructor
      · decide
      · intro j hj0 hj5
        interval_cases j <;> decide)

/-- The desired fifth root reduces to four at a chosen prime above eleven. -/
theorem exists_primeFive_orientedPrime_11 :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal ∧
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact exists_primeFive_cyclotomicPrime_with_reducedRoot 11
    (by decide) (by decide) 4 (by
      apply (IsPrimitiveRoot.iff (by decide)).mpr
      constructor
      · decide
      · intro j hj0 hj5
        interval_cases j <;> decide)

/-- The desired fifth root reduces to ten at a chosen prime above forty-one. -/
theorem exists_primeFive_orientedPrime_41 :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal ∧
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10 := by
  let : Fact (Nat.Prime 41) := ⟨by decide⟩
  exact exists_primeFive_cyclotomicPrime_with_reducedRoot 41
    (by decide) (by decide) 10 (by
      apply (IsPrimitiveRoot.iff (by decide)).mpr
      constructor
      · decide
      · intro j hj0 hj5
        interval_cases j <;> decide)

/-- The manuscript's generator at eleven yields the selected reduced root
under the positive power-residue exponent. -/
theorem primeFive_generator11_residuePower : (2 : ZMod 11) ^ ((11 - 1) / 5) = 4 := by
  decide

/-- The manuscript's generator at forty-one yields the selected reduced root
under the same positive power convention. -/
theorem primeFive_generator41_residuePower : (6 : ZMod 41) ^ ((41 - 1) / 5) = 10 := by
  decide

end HilbertModularity.Examples
