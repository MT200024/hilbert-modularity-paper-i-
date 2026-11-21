/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisDescent

/-! # Arithmetic specializations of the chosen Euler descent

The generic real-field descent is one local system. Its arithmetic fibres
therefore inherit rank and continuity from that same family. These are
properties of the chosen cohomological realization, with no Frobenius
formula built into the definitions. See [GPRV, Theorem 9.2 and Proposition 9.5]
and [TripathiGoswamiRevised, Definition 2.3].
-/

public noncomputable section

open AlgebraicGeometry
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

universe u

variable (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
  [FiniteDimensional ℚ_[ℓ] L]
  (ι : cyclotomicField N →+* L)
  (𝒞 : SmoothProperEulerFamily N m)

/-- The coefficient embedding on the real subfield is the restriction of the
one fixed cyclotomic coefficient embedding. -/
def realEulerCoefficientEmbedding : realCyclotomicField N →+* L :=
  ι.comp (realEulerCoefficientInclusion N)

omit [CompleteSpace L] in
/-- The coefficient label of the exponent-`m` Euler curve is the image of
`ζ_N^m + ζ_N^{-m}` under the *fixed* embedding `ι`. This is the one exponent
transport in [TripathiGoswamiRevised, Definition 2.3]. -/
theorem realEulerCoefficientEmbedding_tau :
    realEulerCoefficientEmbedding N L ι (tau N m) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m) := by
  change ι (realEulerCoefficientInclusion N (tau N m)) = _
  rw [realEulerCoefficientInclusion_tau]

/-- The actual arithmetic fibre of the one chosen descended local system. -/
abbrev ProperEulerRealDescent.SpecializationCarrier
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) : Type _ :=
  D.localSystem.toFunctor.obj
    (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))

/-- Specialize the *generic* descended family, retaining its actual Galois
action on the cohomological fibre. -/
def ProperEulerRealDescent.specialization
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Representation L
      (AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
        AlgebraicClosure (realCyclotomicField N))
      (D.SpecializationCarrier N m ℓ L ι 𝒞 ξ) :=
  D.localSystem.arithmeticRepresentation (ProjectiveLine.puncturedPoint _ ξ)

omit [CompleteSpace L] [ContinuousSMul ℚ_[ℓ] L] [FiniteDimensional ℚ_[ℓ] L] in
/-- Every specialization of the selected family has cohomological rank two. -/
theorem ProperEulerRealDescent.specialization_finrank
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Module.finrank L (D.SpecializationCarrier N m ℓ L ι 𝒞 ξ) = 2 :=
  D.rank_two ξ

omit [CompleteSpace L] [ContinuousSMul ℚ_[ℓ] L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The action on each arithmetic fibre is continuous in the profinite
absolute Galois topology. -/
theorem ProperEulerRealDescent.specialization_continuous
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (v : D.SpecializationCarrier N m ℓ L ι 𝒞 ξ) :
    Continuous (fun g => D.specialization N m ℓ L ι 𝒞 ξ g v) :=
  D.localSystem.continuous_arithmeticRepresentation
    (ProjectiveLine.puncturedPoint _ ξ) v

end HilbertModularity.Hypergeometric
