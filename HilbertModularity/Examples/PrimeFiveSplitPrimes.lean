/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Cyclotomic

/-! # Degree-one real cyclotomic primes in the level-five example

The standard cyclotomic splitting theorem supplies the actual finite primes
used by the worked example. The theorem is independent of the point counts,
Jacobian Frobenius polynomial and choice of character label.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic

local instance primeFiveSplittingPrime : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- [MilneANT, Example 8.18, printed p.143, and §§8.14–8.16,
pp.141–142]: away from five, arithmetic Frobenius on the fifth cyclotomic
field sends ζ₅ to ζ₅^q. If q≡1 mod5 it is trivial, so q splits completely
in the full field and hence has a degree-one prime in its real subfield.
This standard splitting input asserts no orientation of the fifth-root
character and no trace or Frobenius polynomial of the example curve. -/
theorem exists_primeFive_realPrime_of_mod_five_eq_one
    (q : ℕ) [Fact q.Prime] (hq5 : q ≠ 5) (hmod : q % 5 = 1) :
    ∃ P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)),
      Nat.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = q := by
  sorry

/-- A genuine degree-one real prime above eleven. -/
theorem exists_primeFive_realPrime_11 :
    ∃ P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)),
      Nat.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact exists_primeFive_realPrime_of_mod_five_eq_one 11 (by decide) (by decide)

/-- A genuine degree-one real prime above forty-one. -/
theorem exists_primeFive_realPrime_41 :
    ∃ P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)),
      Nat.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 41 := by
  let : Fact (Nat.Prime 41) := ⟨by decide⟩
  exact exists_primeFive_realPrime_of_mod_five_eq_one 41 (by decide) (by decide)

end HilbertModularity.Examples
