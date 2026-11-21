/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeFiberDeterminant
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricDeterminant

/-! # Comparing the two completed Tate actions of the selected plus Jacobian

The selected fibre has an exact cyclotomic determinant over its native local
RM field. A Galois equivariant identification with the scalar extension of
its integral RM Tate lattice transports that determinant to the lattice used
in the Skinner--Wiles checklist. The representation comparison is retained
as an explicit input; equality of determinants is proved from it.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField TensorProduct ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic

/-- An operator-level comparison of the native completed Tate factor with
the extension of the *same* selected Jacobian's integral RM Tate lattice
transports its exact cyclotomic determinant. The coefficient equality states
the normalization of the two maps from `ℤ_[p]`; it is not a determinant
assumption. See [TripathiGoswamiRevised, proof of Lemma `det-rigidity`]. -/
theorem primePlusIntegralTate_det_of_nativeComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type*) [Field E]
    [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (τ : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] E)
    (e : letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (RealPrimePowerCompletion p 0) E := τ.toAlgebra
      ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange E).Equiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange E))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] E (z : ℚ_[p]))
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p)) :
    letI := primePlusIntegralTateModule p hp ξ
    LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
              (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))) := by
  let := primePlusIntegralTateModule p hp ξ
  let : Algebra (RealPrimePowerCompletion p 0) E := τ.toAlgebra
  let z : ℤ_[p] := Field.cyclotomicCharacter (realCyclotomicField p) p g
  calc
    LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        LinearMap.det ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange E g) :=
      e.det_eq g
    _ = algebraMap (RealPrimePowerCompletion p 0) E
          (LinearMap.det ((primePlusLocalTateRepresentation p hp ξ).ρ g)) := by
      exact LinearMap.det_baseChange _
    _ = algebraMap ℚ_[p] E (z : ℚ_[p]) := by
      rw [primePlusLocalTateRepresentation_det p hp ξ g]
      exact (IsScalarTower.algebraMap_apply ℚ_[p]
        (RealPrimePowerCompletion p 0) E _).symm
    _ = _ := (hcoeff z).symm

end HilbertModularity.Hypergeometric
