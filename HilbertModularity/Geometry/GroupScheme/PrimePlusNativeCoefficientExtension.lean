/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusNativeChecklist
public import HilbertModularity.RepresentationTheory.ScalarExtension

/-! # Extending the same native Tate comparison to larger coefficient fields -/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

/-- A native Tate comparison extends along a coefficient embedding when the
completed integer diagram commutes. The larger coefficient field need not
be the fraction field of the original integer ring. -/
def PrimePlusNativeTateComparison.extendCoefficients
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {K L : Type*} [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) K]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) L]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[K])
    (C : PrimePlusNativeTateComparison p hp ξ K β)
    (f : K →ₐ[ℚ_[p]] L)
    (hcoeff : ∀ a : AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p)),
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) L a =
        f (algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) K a))
    (γ : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[L])
    (hγ : (inferInstance : Algebra (AdicCompletion
        (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p))) L) =
      ((𝒪[L]).subtype.comp γ).toAlgebra) :
    PrimePlusNativeTateComparison p hp ξ L γ := by
  letI := primePlusIntegralTateModule p hp ξ
  letI : Algebra K L := f.toAlgebra
  letI : Algebra (RealPrimePowerCompletion p 0) K := C.localMap.toAlgebra
  letI : Algebra (RealPrimePowerCompletion p 0) L := (f.comp C.localMap).toAlgebra
  letI : IsScalarTower (RealPrimePowerCompletion p 0) K L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) K L :=
    IsScalarTower.of_algebraMap_eq hcoeff
  refine {
    localMap := f.comp C.localMap
    actionEquiv := ?_
    integerCoefficients := ?_
    integralEmbedding := hγ }
  · exact (Representation.baseChangeTowerEquiv (L := K) (M := L)
      (primePlusLocalTateRepresentation p hp ξ).ρ).symm.trans
      ((C.actionEquiv.baseChange L).trans
        (Representation.baseChangeTowerEquiv (L := K) (M := L)
          (primePlusIntegralTateRepresentation p hp ξ)))
  · intro z
    rw [hcoeff, C.integerCoefficients, f.commutes]

/-- Scalar extension uses the composed local coefficient map. -/
theorem PrimePlusNativeTateComparison.extendCoefficients_localMap
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {K L : Type*} [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) K]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) L]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[K])
    (C : PrimePlusNativeTateComparison p hp ξ K β)
    (f : K →ₐ[ℚ_[p]] L)
    (hcoeff : ∀ a : AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p)),
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) L a =
        f (algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) K a))
    (γ : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[L])
    (hγ : (inferInstance : Algebra (AdicCompletion
        (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p))) L) =
      ((𝒪[L]).subtype.comp γ).toAlgebra) :
    (PrimePlusNativeTateComparison.extendCoefficients p hp ξ β C f hcoeff γ hγ).localMap =
      f.comp C.localMap := by
  exact (rfl)

/-- The native comparison gives the selected integral-basis coordinates
at its own specified local coefficient map. -/
def PrimePlusNativeTateComparison.coordinateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (C : PrimePlusNativeTateComparison p hp ξ E β) :
    letI : Algebra (RealPrimePowerCompletion p 0) E := C.localMap.toAlgebra
    ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange E).Equiv
      (primePlusTateFieldCoordinateAction p hp ξ β) := by
  letI := primePlusIntegralTateModule p hp ξ
  letI : Algebra (RealPrimePowerCompletion p 0) E := C.localMap.toAlgebra
  exact C.actionEquiv.trans
    (primePlusTateFieldCoordinateEquiv p hp ξ β C.integralEmbedding).symm

end HilbertModularity.Hypergeometric
