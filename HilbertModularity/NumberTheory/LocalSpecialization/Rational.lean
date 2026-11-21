/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalSpecialization.GoodPrimeDescent
public import Mathlib.Algebra.CharP.Two

/-! # Rational parameters at primes above two

A rational parameter and its complement cannot both be units at a prime above
two. This allows the odd-prime good-reduction calculation to cover every
eligible prime in the rational-parameter manuscript theorems.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.LocalSpecialization

attribute [local instance] Ideal.Quotient.field

/-- A good rational specialization cannot lie above two. Reduce the numerator
and the unit denominator in characteristic two: the residue would be zero or
one, contrary to the two good-unit conditions. -/
theorem two_not_mem_of_rat_goodUnit
    (P : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) (hx : P.GoodUnit x) :
    (2 : 𝓞 ℚ) ∉ P.asIdeal := by
  intro h2
  have h2k : (2 : 𝓞 ℚ ⧸ P.asIdeal) = 0 := by
    simpa only [map_ofNat] using (Ideal.Quotient.eq_zero_iff_mem.mpr h2)
  let : CharP (𝓞 ℚ ⧸ P.asIdeal) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2k
  have hd : (x.den : 𝓞 ℚ) ∉ P.asIdeal :=
    Rat.valuation_le_one_iff_den.mp hx.valuation_eq_one.le
  have hdk : (x.den : 𝓞 ℚ ⧸ P.asIdeal) ≠ 0 := by
    intro h
    apply hd
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_natCast] using h
  have hd1 : (x.den : 𝓞 ℚ ⧸ P.asIdeal) = 1 :=
    (CharTwo.natCast_cases (𝓞 ℚ ⧸ P.asIdeal) x.den).resolve_left hdk
  have he : P.localElement x hx.valuation_eq_one.le *
      (x.den : P.valuationSubringAtPrime ℚ) = (x.num : P.valuationSubringAtPrime ℚ) := by
    apply Subtype.ext
    change x * (x.den : ℚ) = (x.num : ℚ)
    calc
      x * (x.den : ℚ) = ((x.num : ℚ) / (x.den : ℚ)) * (x.den : ℚ) := by
        rw [x.num_div_den]
      _ = (x.num : ℚ) := div_mul_cancel₀ _ (by exact_mod_cast x.den_ne_zero)
  have hr := congrArg (P.localResidue (K := ℚ)) he
  simp only [map_mul, map_natCast, map_intCast, hd1, mul_one] at hr
  have hn := CharTwo.intCast_cases (R := 𝓞 ℚ ⧸ P.asIdeal) x.num
  change P.specialization x hx.valuation_eq_one.le = (x.num : 𝓞 ℚ ⧸ P.asIdeal) at hr
  rcases hn with hn | hn
  · exact hx.specialization_ne_zero_one.1 (hr.trans hn)
  · exact hx.specialization_ne_zero_one.2 (hr.trans hn)

/-- The same exclusion holds at every prime of a number field for a parameter
coming from the rationals, even when its residue field is larger than `𝔽₂`. -/
theorem two_not_mem_of_rational_goodUnit
    {K : Type*} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (x : ℚ)
    (hx : P.GoodUnit (algebraMap ℚ K x)) :
    (2 : 𝓞 K) ∉ P.asIdeal := by
  let q := P.under (𝓞 ℚ)
  let : P.asIdeal.LiesOver q.asIdeal := ⟨by rfl⟩
  have hq := (goodUnit_field_algebraMap_iff q P x).mp hx
  intro h2
  apply two_not_mem_of_rat_goodUnit q x hq
  change algebraMap (𝓞 ℚ) (𝓞 K) 2 ∈ P.asIdeal
  simpa only [map_ofNat] using h2

end HilbertModularity.LocalSpecialization
