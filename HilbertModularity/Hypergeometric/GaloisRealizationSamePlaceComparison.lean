/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationCompatibleSystem
public import HilbertModularity.RepresentationTheory.CharacteristicPolynomialDescent
public import HilbertModularity.RepresentationTheory.CompatibleSystemCoefficientExtension

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

local instance eulerSamePlaceCompletionNorm (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField N)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField N))
    (WithZero (Multiplicative ℤ))

/-- Extend the canonical completion action to the specified finite local
field and compare it with the arithmetic fibre of the same chosen descent.
The literature input is the scalar extension of the actual quotient H¹;
the rest is transport through the existing coordinate equivalence. -/
def commonEulerCompletionAction_baseChangeEquiv
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [ContinuousSMul ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [FiniteDimensional ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ_[(NumberField.primeBelow (cyclotomicField N) w)]
      (w.adicCompletion (cyclotomicField N)) L]
    (ι : cyclotomicField N →+* L)
    (hι : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    : ((commonEulerCompletionAction N m 𝒞 R ξ w).baseChange L).Equiv
      ((R.placeDescent N m 𝒞 (NumberField.primeBelow (cyclotomicField N) w)
        L ι).localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)) := by
  letI : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let e := R.coefficientBaseChange
    (NumberField.primeBelow (cyclotomicField N) w)
    (w.adicCompletion (cyclotomicField N)) L
    (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N)))
    ι hι ξ
  have e₀' : ((commonEulerCompletionAction N m 𝒞 R ξ w).baseChange L).Equiv
      (((R.atPlace (NumberField.primeBelow (cyclotomicField N) w)
        (w.adicCompletion (cyclotomicField N))
        (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N)))).descent.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)).baseChange L) := by
    have h := (commonEulerCompletionActionEquiv N m 𝒞 R ξ w).baseChange L
    rw [commonEulerCompletionDescent_eq_placeDescent,
      CommonRealEulerQuotientRealization.placeDescent_eq_atPlace] at h
    exact h
  rw [CommonRealEulerQuotientRealization.placeDescent_eq_atPlace]
  exact e₀'.trans e

/-- The local realization of the chosen descent has the mapped
characteristic polynomial at every element of the full real-field Galois
group. Frobenius is a specialization of this equality. -/
theorem commonEulerCompletionAction_local_charpoly
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [ContinuousSMul ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [FiniteDimensional ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ_[(NumberField.primeBelow (cyclotomicField N) w)]
      (w.adicCompletion (cyclotomicField N)) L]
    (ι : cyclotomicField N →+* L)
    (hι : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    (g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N)) :
    (((R.placeDescent N m 𝒞 (NumberField.primeBelow (cyclotomicField N) w)
      L ι).localSystem.arithmeticRepresentation
      (ProjectiveLine.puncturedPoint _ ξ)) g).charpoly =
      ((commonEulerCompletionAction N m 𝒞 R ξ w g).charpoly).map
        (algebraMap (w.adicCompletion (cyclotomicField N)) L) := by
  let : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let e := commonEulerCompletionAction_baseChangeEquiv
    N m 𝒞 R ξ w L ι hι
  calc
    _ = (((commonEulerCompletionAction N m 𝒞 R ξ w).baseChange L) g).charpoly :=
      (e.charpoly_eq g).symm
    _ = _ := LinearMap.charpoly_baseChange _ L

/-- At a geometric good prime away from the coefficient characteristic, the
chosen local descent has the algebraic Frobenius polynomial of the *same*
Euler quotient compatible system, mapped through the compatible label `ι`.
The comparison first uses cohomological scalar extension at this one place,
then the system's already established polynomial compatibility. -/
theorem commonEulerLocalDescent_frobenius_charpoly
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [ContinuousSMul ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [FiniteDimensional ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ_[(NumberField.primeBelow (cyclotomicField N) w)]
      (w.adicCompletion (cyclotomicField N)) L]
    (ι : cyclotomicField N →+* L)
    (hι : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ commonEulerBadPrimes N ξ)
    (hℓ : (NumberField.primeBelow (cyclotomicField N) w :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    (((R.placeDescent N m 𝒞 (NumberField.primeBelow (cyclotomicField N) w)
      L ι).localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ))
      (NumberField.geometricFrobenius (realCyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) q.asIdeal Q)).charpoly =
      ((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).polynomial q).map ι := by
  let : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let S := commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN
  let g := NumberField.geometricFrobenius (realCyclotomicField N)
    (AlgebraicClosure (realCyclotomicField N)) q.asIdeal Q
  have hgood : q ∉ S.bad := by
    simpa only [S, commonEulerCompatibleSystem_bad_eq_common] using hq
  have hℓS : (S.residueCharacteristic w : 𝓞 (realCyclotomicField N)) ∉
      q.asIdeal := by
    simpa only [S, commonEulerCompatibleSystem_residueCharacteristic] using hℓ
  have hlow := S.frobenius_charpoly w q hgood q.asIdeal rfl hℓS Q
  have hlocal := commonEulerCompletionAction_local_charpoly
    N m 𝒞 R ξ w L ι hι g
  calc
    _ = ((commonEulerCompletionAction N m 𝒞 R ξ w g).charpoly).map
        (algebraMap (w.adicCompletion (cyclotomicField N)) L) := hlocal
    _ = ((S.polynomial q).map
        (algebraMap (cyclotomicField N)
          (w.adicCompletion (cyclotomicField N)))).map
        (algebraMap (w.adicCompletion (cyclotomicField N)) L) := by
      exact congrArg (Polynomial.map
        (algebraMap (w.adicCompletion (cyclotomicField N)) L))
        (by simpa only [S, commonEulerCompatibleSystem_action] using hlow)
    _ = (S.polynomial q).map ι := by
      rw [Polynomial.map_map, hι]

/-- The preceding comparison for the one selected Euler family and its one
selected quotient. The same `R` occurs in the local descent and in the
compatible system's construction. -/
theorem chosenEulerLocalDescent_frobenius_charpoly
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [ContinuousSMul ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [FiniteDimensional ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ_[(NumberField.primeBelow (cyclotomicField N) w)]
      (w.adicCompletion (cyclotomicField N)) L]
    (ι : cyclotomicField N →+* L)
    (hι : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ (chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).bad)
    (hℓ : ((chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).residueCharacteristic
      w : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hm hmN
    let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hm hmN
    (((R.placeDescent N m 𝒞 (NumberField.primeBelow (cyclotomicField N) w)
      L ι).localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ))
      (NumberField.geometricFrobenius (realCyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) q.asIdeal Q)).charpoly =
      ((chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).polynomial q).map ι := by
  let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hm hmN
  let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hm hmN
  have hq' : q ∉ commonEulerBadPrimes N ξ := by
    simpa only [chosenCommonEulerCompatibleSystem_eq_common,
      commonEulerCompatibleSystem_bad_eq_common] using hq
  have hℓ' : (NumberField.primeBelow (cyclotomicField N) w :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal := by
    simpa only [chosenCommonEulerCompatibleSystem_eq_common,
      commonEulerCompatibleSystem_residueCharacteristic] using hℓ
  simpa only [chosenCommonEulerCompatibleSystem_eq_common] using
    (commonEulerLocalDescent_frobenius_charpoly N m 𝒞 R ξ
      hN h5 hm hmN w L ι hι q hq' hℓ' Q)

/-- A single number-field enlargement of the chosen Euler system retains the
same local Frobenius comparison. This is the polynomial input in the signature
of `CohomologicalRealization.exists_sphericalEigenform_of_mapped_localComparison`
when `i` is its local eigenform coefficient embedding. -/
theorem chosenEulerLocalDescent_frobenius_charpoly_extended
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [ContinuousSMul ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [FiniteDimensional ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ_[(NumberField.primeBelow (cyclotomicField N) w)]
      (w.adicCompletion (cyclotomicField N)) L]
    (ι : cyclotomicField N →+* L)
    (hι : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    (A : Type*) [Field A] [NumberField A] [Algebra (cyclotomicField N) A]
    (i : A →+* L) (hi : i.comp (algebraMap (cyclotomicField N) A) = ι)
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ (chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).bad)
    (hℓ : ((chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).residueCharacteristic
      w : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hm hmN
    let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hm hmN
    (((R.placeDescent N m 𝒞 (NumberField.primeBelow (cyclotomicField N) w)
      L ι).localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ))
      (NumberField.geometricFrobenius (realCyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) q.asIdeal Q)).charpoly =
      (((chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).extendCoefficients
        (L := A)).polynomial q).map i := by
  have h := chosenEulerLocalDescent_frobenius_charpoly N m ξ
    hN h5 hm hmN w L ι hι q hq hℓ Q
  simpa only [NumberFieldCompatibleSystem.extendCoefficients_polynomial,
    Polynomial.map_map, hi] using h


end HilbertModularity.Hypergeometric
