/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.IntegralRationalTateComparison
public import HilbertModularity.Geometry.GroupScheme.PrimePlusCanonicalNativeCoefficients
public import HilbertModularity.Hypergeometric.PrimePlusNativeChecklist

/-! # The selected native Tate comparison with its full RM coefficient map -/

public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic

private theorem primePlusLocalTateRepresentation_eq_generic
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    primePlusLocalTateRepresentation p hp ξ =
      localCoefficientTateRep (realCyclotomicField p)
        (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) p 0
        (primePlusPrimePowerRealMultiplication p hp) := by
  exact (rfl)

private theorem primePlusFiberRealMultiplication_eq_family
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    primePlusFiberRealMultiplication p hp ξ =
      (fiberEndomorphismMap (realCyclotomicField p) (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).comp
          (primePlusRealMultiplication p hp) := by
  exact (rfl)

/-- Apply the standard scalar-localization comparison to the *same*
selected plus family and its fixed integral RM action. The remaining
coefficient equality is supplied below by the canonical integer map. -/
theorem exists_primePlusNativeActionEquiv_of_coefficients
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (hRM : ∀ a : 𝓞 (realCyclotomicField (p ^ (0 + 1))),
      algebraMap (realCyclotomicField (p ^ (0 + 1)))
        (RealPrimePowerCompletion p 0) (a : realCyclotomicField (p ^ (0 + 1))) =
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)
        (algebraMap (𝓞 (realCyclotomicField p))
          (AdicCompletion (Ideal.span {realPrimeGenerator p})
            (𝓞 (realCyclotomicField p)))
          (Eq.mp (congrArg (fun F : IntermediateField ℚ Qbar => 𝓞 F)
            (primePlusPrimePowerField_eq p)) a)))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) (z : ℚ_[p])) :
    letI := primePlusIntegralTateModule p hp ξ
    letI : Algebra (RealPrimePowerCompletion p 0)
        (RealPrimePowerCompletion p 0) :=
      (AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
    Nonempty (((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange
      (RealPrimePowerCompletion p 0)).Equiv
      ((primePlusIntegralTateRepresentation p hp ξ).baseChange
        (RealPrimePowerCompletion p 0))) := by
  have hB : primePlusFiber p hp ξ =
      fiber (realCyclotomicField p) (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) := (rfl)
  have hφB : Eq.mp (congrArg
      (fun T : CommGrp (Over (Spec (CommRingCat.of (realCyclotomicField p)))) =>
        𝓞 (realCyclotomicField p) →+* End T) hB)
      (primePlusFiberRealMultiplication p hp ξ) =
      (fiberEndomorphismMap (realCyclotomicField p) (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).comp
          (primePlusRealMultiplication p hp) := by
    exact primePlusFiberRealMultiplication_eq_family p hp ξ
  have h := exists_integralRationalTateComparison
    p hp (realCyclotomicField p) (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    (primePlusPrimePowerRealMultiplication p hp)
    (primePlusRealMultiplication p hp)
    (primePlusPrimePowerField_eq p)
    (primePlusPrimePowerRealMultiplication_eq p hp)
    (primePlusFiber p hp ξ) hB
    (primePlusFiberRealMultiplication p hp ξ) hφB
    (RealPrimePowerCompletion p 0)
    (AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)) hRM hcoeff
  rw [primePlusLocalTateRepresentation_eq_generic p hp ξ]
  unfold primePlusIntegralTateRepresentation primePlusIntegralTateModule
  exact h


/-- The canonical native Tate comparison on the same selected plus Jacobian.
Both the full RM coefficient map and its rational p-adic restriction are
proved for the selected maps; only generic Tate rationalization is admitted. -/
def primePlusCanonicalNativeTateComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    letI := primePlusCanonicalNativeAlgebra p hp
    PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0)
      (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom := by
  letI := primePlusCanonicalNativeAlgebra p hp
  letI := primePlusCanonicalNative_isFractionRing p hp
  exact {
    localMap := AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)
    actionEquiv := Classical.choice
      (exists_primePlusNativeActionEquiv_of_coefficients p hp ξ
        (primePlusCanonicalNativeAlgebra_fullRM p hp)
        (primePlusCanonicalNativeAlgebra_padic p hp))
    integerCoefficients := primePlusCanonicalNativeAlgebra_padic p hp
    integralEmbedding := primePlusCanonicalNativeAlgebra_eq p hp }

/-- The canonical comparison uses the identity local coefficient map. -/
theorem primePlusCanonicalNativeTateComparison_localMap
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    letI := primePlusCanonicalNativeAlgebra p hp
    (primePlusCanonicalNativeTateComparison p hp ξ).localMap =
      AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0) := by
  exact (rfl)

end HilbertModularity.Hypergeometric
