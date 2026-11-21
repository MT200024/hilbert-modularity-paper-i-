/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationQuotient

/-! # Cohomology of one common real Euler quotient

The geometric quotient is chosen before `ℓ` or the coefficient field. Every
specialized cohomology group in this module is taken from an actual fibre of
that same scheme. The rank-two eigensummand and its comparison with the fixed
`χ₀` projector on the exponent-`m` Euler curve are separate assertions.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HilbertModularity.Cyclotomic
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)

/-- The fibre of the single real-field quotient at a rational punctured-line
parameter. -/
def smoothProperRealEulerQuotientFibre
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) : Scheme :=
  pullback 𝒬.projection
    (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ)

/-- Its structural map over the real coefficient field. -/
def smoothProperRealEulerQuotientFibreStructureMap
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    smoothProperRealEulerQuotientFibre N m 𝒞 𝒬 ξ ⟶
      Spec (CommRingCat.of (realCyclotomicField N)) :=
  pullback.snd _ _

/-- The geometric fibre used for degree-one étale cohomology. -/
abbrev geometricSmoothProperRealEulerQuotientFibre
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) : Scheme :=
  pullback
    (GroupScheme.fieldPoint (realCyclotomicField N)
      (AlgebraicClosure (realCyclotomicField N))).hom
    (smoothProperRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ)

/-- Degree-one cohomology of the actual quotient fibre after extension to a
chosen `ℓ`-adic coefficient field. This is the full cohomology, before taking
the real cyclotomic eigensummand from [GPRV, Theorem 9.2]. -/
abbrev GeometricRealEulerQuotientCohomology
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] : Type _ :=
  L ⊗[ℚ_[ℓ]]
    (geometricSmoothProperRealEulerQuotientFibre N m 𝒞 𝒬 ξ).RationalEllAdicCohomology ℓ 1

/-- The Galois action on the full cohomology of one actual quotient fibre. -/
def geometricRealEulerQuotientGaloisRepresentation
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    Representation L
      (AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
        AlgebraicClosure (realCyclotomicField N))
      (GeometricRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L) :=
  Representation.baseChange L
    (Representation.baseChange ℚ_[ℓ]
      (Scheme.ellAdicCohomologyGaloisRepresentation
        (realCyclotomicField N)
        (smoothProperRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ) ℓ 1))

end HilbertModularity.Hypergeometric
