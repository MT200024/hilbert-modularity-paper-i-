/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ProperFrobeniusComparison

/-! # A common good-prime trace for the proper Euler realizations

The proper exponent-`m` Euler curve is chosen before the coefficient place. At
a good prime of the cyclotomic field, its fixed-`χ₀` Frobenius trace is one
algebraic scalar. The two specializations below may use different coefficient
places and different chosen real descents: their restrictions to the
cyclotomic Galois group nevertheless have that same trace scalar. This is the
trace part of compatibility at primes of the cyclotomic field. It makes no
claim about determinants or Frobenius at primes of the real field inert in
the cyclotomic extension.
-/

public noncomputable section

open AlgebraicGeometry
open HilbertModularity.Cyclotomic
open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

universe u v

/-- At a good cyclotomic prime, two coefficient-place realizations of the
same proper Euler family have traces obtained from one cyclotomic scalar.
The scalar is McCarthy's normalized finite value under the fixed inclusion
into `Qbar`. The proper-cohomology trace input is
[GPRV, Theorem 7.4]; the finite-sum normalization is the direct calculation
of [TripathiGoswamiRevised, equation (2.4)]. In particular, eligible
residue characteristic two is included when `N` is odd. -/
theorem ProperEulerRealDescent.goodPrime_trace_compatible_over_cyclotomicField
    (N m ℓ₁ ℓ₂ : ℕ) [NeZero N] [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (L₁ : Type u) [NontriviallyNormedField L₁] [CompleteSpace L₁]
    [Algebra ℚ_[ℓ₁] L₁] [ContinuousSMul ℚ_[ℓ₁] L₁]
    [FiniteDimensional ℚ_[ℓ₁] L₁]
    (L₂ : Type v) [NontriviallyNormedField L₂] [CompleteSpace L₂]
    [Algebra ℚ_[ℓ₂] L₂] [ContinuousSMul ℚ_[ℓ₂] L₂]
    [FiniteDimensional ℚ_[ℓ₂] L₂]
    (ι₁ : cyclotomicField N →+* L₁) (ι₂ : cyclotomicField N →+* L₂)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D₁ : ProperEulerRealDescent N m ℓ₁ L₁ ι₁ 𝒞)
    (D₂ : ProperEulerRealDescent N m ℓ₂ L₂ ι₂ 𝒞)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ₁ : (ℓ₁ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ₂ : (ℓ₂ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ))
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1) :
    letI : Module.Finite L₁
        (D₁.localSystem.toFunctor.obj
          (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
      D₁.localSystem.finite _
    letI : Module.Finite L₂
        (D₂.localSystem.toFunctor.obj
          (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
      D₂.localSystem.finite _
    ∃ a : cyclotomicField N,
      LinearMap.trace L₁ _
        (D₁.localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ)
          ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
            (absoluteGeometricFrobenius N P Q))) = ι₁ a ∧
      LinearMap.trace L₂ _
        (D₂.localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ)
          ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
            (absoluteGeometricFrobenius N P Q))) = ι₂ a ∧
      (cyclotomicField N).val a =
        mccarthyValue N P hP m θ (realEulerParameter N ξ) hξ := by
  have : Module.Finite L₁
      (D₁.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
    D₁.localSystem.finite _
  have : Module.Finite L₂
      (D₂.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
    D₂.localSystem.finite _
  refine ⟨normalizedCyclotomicEulerTrace N P.asIdeal hP m
      (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le), ?_, ?_, ?_⟩
  · exact D₁.geometricFrobenius_trace_eq_normalizedEulerTrace N m ℓ₁ L₁ ι₁
      hN h5 hm hmN 𝒞 P hP hℓ₁ Q ξ hξ
  · exact D₂.geometricFrobenius_trace_eq_normalizedEulerTrace N m ℓ₂ L₂ ι₂
      hN h5 hm hmN 𝒞 P hP hℓ₂ Q ξ hξ
  · exact normalizedCyclotomicEulerTrace_val_mccarthyValue N P hP m hm hmN
      θ hθ (realEulerParameter N ξ) hξ

end HilbertModularity.Hypergeometric
