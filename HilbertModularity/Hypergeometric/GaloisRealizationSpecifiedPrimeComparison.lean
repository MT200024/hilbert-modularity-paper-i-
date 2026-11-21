/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationSamePlaceComparison
public import HilbertModularity.NumberTheory.PrimeBelowComparison

/-! # One Euler quotient at two compatible local coefficient fields

The common quotient's rational cohomology extends from a canonical
cyclotomic completion to a finite field receiving that completion. Its
full real-field arithmetic action then has the mapped characteristic
polynomial. This uses the same quotient and the same specialization.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open scoped NumberField

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N]
  (𝒞 : SmoothProperEulerFamily N m)
  (R : CommonRealEulerQuotientRealization.{0} N m 𝒞)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField N))

local instance eulerSpecifiedPrimeCompletionNorm (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField N)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField N))
    (WithZero (Multiplicative ℤ))

/-- The same coefficient comparison at an explicitly specified rational
prime below the source place, retaining its canonical p-adic scalar map. -/
def commonEulerCompletionAction_baseChangeEquiv_at_prime
    (ℓ : ℕ) [Fact ℓ.Prime]
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [w.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L]
    [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ_[ℓ]
      (w.adicCompletion (cyclotomicField N)) L]
    (ι : cyclotomicField N →+* L)
    (hι : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    : ((commonEulerCompletionAction N m 𝒞 R ξ w).baseChange L).Equiv
      ((R.placeDescent N m 𝒞 ℓ
        L ι).localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)) := by
  have hbelow : NumberField.primeBelow (cyclotomicField N) w = ℓ :=
    NumberField.primeBelow_eq_of_liesOver (cyclotomicField N) w ℓ
  subst ℓ
  exact commonEulerCompletionAction_baseChangeEquiv N m 𝒞 R ξ w L ι hι

end HilbertModularity.Hypergeometric
