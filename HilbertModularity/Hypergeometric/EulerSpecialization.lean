/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerSum
public import HilbertModularity.Hypergeometric.Specialization

/-! # Arithmetic Euler sums at actual good primes

The distinguished power-residue character and the actual local reduction of
the parameter give the cyclic-cover character sum in
[TripathiGoswamiRevised, the argument following equation (2.4)].
The coefficient embedding is the fixed algebraic one used by `mccarthyValue`.
-/

@[expose] public noncomputable section
namespace HilbertModularity.Cyclotomic

open scoped NumberField
open IsDedekindDomain Hypergeometric
attribute [local instance] Ideal.Quotient.field instFintypeSpecializationResidue

variable (N : ℕ) [NeZero N] (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
  (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)

/-- The actual arithmetic McCarthy value is its distinguished Euler character sum. -/
theorem mccarthyValue_eq_eulerCharacterSum (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ ξ hξ =
      -(powerResidueMulChar N P.asIdeal hP ^ m) (-1) *
        eulerCharacterSum (powerResidueMulChar N P.asIdeal hP ^ m)
          (P.specialization ξ hξ.valuation_eq_one.le) := by
  classical
  apply rankTwoMcCarthySum_eq_eulerCharacterSum _ _ θ hθ _
    (P.specialization_ne_zero ξ hξ.valuation_eq_one)
  apply pow_ne_one_of_lt_orderOf (Nat.ne_of_gt hm)
  simpa only [powerResidueMulChar_orderOf] using hmN

/-- The arithmetic value is the actual power-residue character evaluated on the Euler
curve polynomial, with the exact finite character at minus one retained. -/
theorem mccarthyValue_eq_eulerCurveSum (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ ξ hξ =
      -(powerResidueMulChar N P.asIdeal hP ^ m) (-1) *
        ∑ y : 𝓞 (cyclotomicField N) ⧸ P.asIdeal,
          powerResidueMulChar N P.asIdeal hP
            (y ^ m * (1 - y) ^ (N - m) *
              (1 - P.specialization ξ hξ.valuation_eq_one.le * y) ^ m) := by
  classical
  rw [mccarthyValue_eq_eulerCharacterSum N P hP m hm hmN θ hθ ξ hξ]
  rw [eulerCharacterSum_pow_eq _ N m hm hmN]
  simpa only [powerResidueMulChar_orderOf] using
    pow_orderOf_eq_one (powerResidueMulChar N P.asIdeal hP)

end HilbertModularity.Cyclotomic
