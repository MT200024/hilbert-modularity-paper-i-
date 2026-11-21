/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicTorsion
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficients
public import HilbertModularity.NumberTheory.AdicCompletionIntegersComparison

/-! # Integral and rational Tate realizations with fixed RM coefficients -/

public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic

/-- The standard rationalization comparison for the same integral RM action.
The full RM diagram fixes the homomorphism O_F→E, as in [DarmonFibres,
printed p.5, From hypergeometric abelian varieties to rigid representations].
The finite-module completion theorem is [mathlib_5ed296525643,
Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean,
AdicCompletion.ofTensorProductEquivOfFiniteNoetherian]. Rational Tate
functoriality is [MilneAV, Chapter I, §10, Proposition 10.5 and the following
functoriality discussion, p.45; rationalization definition, p.46]. The comparison
is the resulting scalar-localization identity on the inverse-limit Tate module;
it does not require freeness or an abelian-variety existence assertion for the
group scheme in its signature. Only scalar rationalization and equivariance
are admitted. The selected family and canonical diagrams are constructed separately. -/
theorem exists_integralRationalTateComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (K : Type*) [Field K] {S : Scheme}
    (A : CommGrp (Over S))
    (x : Spec (CommRingCat.of K) ⟶ S)
    (φ₀ : 𝓞 (realCyclotomicField (p ^ (0 + 1))) →+* End A)
    (φ : 𝓞 (realCyclotomicField p) →+* End A)
    (hF : realCyclotomicField (p ^ (0 + 1)) = realCyclotomicField p)
    (hφ : Eq.mp (congrArg
      (fun F : IntermediateField ℚ Qbar => 𝓞 F →+* End A) hF) φ₀ = φ)
    (B : CommGrp (Over (Spec (CommRingCat.of K))))
    (hB : B = fiber K A x)
    (φB : 𝓞 (realCyclotomicField p) →+* End B)
    (hφB : Eq.mp (congrArg
      (fun T : CommGrp (Over (Spec (CommRingCat.of K))) =>
        𝓞 (realCyclotomicField p) →+* End T) hB) φB =
        (fiberEndomorphismMap K A x).comp φ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (τ : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] E)
    (hRM : ∀ a : 𝓞 (realCyclotomicField (p ^ (0 + 1))),
      τ (algebraMap (realCyclotomicField (p ^ (0 + 1)))
        (RealPrimePowerCompletion p 0) (a : realCyclotomicField (p ^ (0 + 1)))) =
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (algebraMap (𝓞 (realCyclotomicField p))
          (AdicCompletion (Ideal.span {realPrimeGenerator p})
            (𝓞 (realCyclotomicField p)))
          (Eq.mp (congrArg (fun F : IntermediateField ℚ Qbar => 𝓞 F) hF) a)))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] E (z : ℚ_[p])) :
    letI : Module (RealPrimePowerCompletion p 0)
        (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p 0 φ₀).toRingHom
    letI := realPrimeIntegralTateModule K B p (by omega) φB
    letI : Algebra (RealPrimePowerCompletion p 0) E := τ.toAlgebra
    Nonempty ((((localCoefficientTateRep K A x p 0 φ₀).ρ).baseChange E).Equiv
      ((realPrimeIntegralTateRepresentation K B p (by omega) φB).baseChange E)) := by
  sorry

end HilbertModularity.Hypergeometric
