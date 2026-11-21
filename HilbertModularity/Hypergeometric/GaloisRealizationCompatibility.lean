/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientTrace

/-! # Frobenius traces of the common real Euler quotient

The quotient in [GPRV, Theorem 9.2 and Proposition 9.5] is chosen before a
coefficient place. At a good prime, traces of its labelled cohomology at two
places are images of the same algebraic Euler trace. This is the trace part of
compatibility; the characteristic polynomial and its determinant are separate
properties.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open scoped NumberField

namespace HilbertModularity.Hypergeometric

universe u

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)

/-- The geometric-Frobenius trace on the actual labelled quotient cohomology
at a coefficient place. The place comes from one common quotient realization. -/
def CommonRealEulerQuotientRealization.componentGeometricFrobeniusTrace
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] : L := by
  let D := R.atPlace ℓ L ι
  letI : Module.Finite L
      ((D.action ξ).component N m 𝒞 R.quotient ξ ℓ L ι) :=
    Module.Finite.equiv (D.componentComparison ξ).symm
  exact LinearMap.trace L _
    ((D.action ξ).componentGaloisEndomorphism N m 𝒞 R.quotient ξ ℓ L ι
      ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
        (absoluteGeometricFrobenius N P Q)))

/-- At every eligible good prime, the quotient trace is the image of the
single algebraic normalized Euler trace. The residue characteristic may be
two when the odd level is prime to it. -/
theorem CommonRealEulerQuotientRealization.componentGeometricFrobeniusTrace_eq
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    R.componentGeometricFrobeniusTrace N m 𝒞 ξ ℓ L ι P Q =
      ι (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  exact (R.atPlace ℓ L ι).geometricFrobenius_trace_eq_normalizedEulerTrace
    N m 𝒞 R.quotient ξ ℓ L ι hN h5 hm hmN P hP hℓ Q hξ

/-- Two coefficient places of the same geometric quotient have the same
algebraic Frobenius trace, viewed through their respective embeddings. This
is a precise trace compatibility assertion, without identifying the two
different local coefficient fields. -/
theorem CommonRealEulerQuotientRealization.componentGeometricFrobeniusTraces_compatible
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ℓ₁ ℓ₂ : ℕ) [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (L₁ : Type u) [NontriviallyNormedField L₁] [CompleteSpace L₁]
    [Algebra ℚ_[ℓ₁] L₁] [ContinuousSMul ℚ_[ℓ₁] L₁]
    [FiniteDimensional ℚ_[ℓ₁] L₁]
    (L₂ : Type u) [NontriviallyNormedField L₂] [CompleteSpace L₂]
    [Algebra ℚ_[ℓ₂] L₂] [ContinuousSMul ℚ_[ℓ₂] L₂]
    [FiniteDimensional ℚ_[ℓ₂] L₂]
    (ι₁ : cyclotomicField N →+* L₁)
    (ι₂ : cyclotomicField N →+* L₂)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ₁ : (ℓ₁ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ₂ : (ℓ₂ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    (R.componentGeometricFrobeniusTrace N m 𝒞 ξ ℓ₁ L₁ ι₁ P Q =
      ι₁ (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le))) ∧
    (R.componentGeometricFrobeniusTrace N m 𝒞 ξ ℓ₂ L₂ ι₂ P Q =
      ι₂ (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le))) := by
  exact ⟨R.componentGeometricFrobeniusTrace_eq N m 𝒞 hN h5 hm hmN
      ξ ℓ₁ L₁ ι₁ P hP hℓ₁ Q hξ,
    R.componentGeometricFrobeniusTrace_eq N m 𝒞 hN h5 hm hmN
      ξ ℓ₂ L₂ ι₂ P hP hℓ₂ Q hξ⟩

end HilbertModularity.Hypergeometric
