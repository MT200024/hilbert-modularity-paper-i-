/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveEulerSpecialization
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientTrace

/-! # The worked Euler cohomology traces at the oriented primes

The direct complex evaluations determine the algebraic Euler scalar whose
images at every coefficient place are the actual chosen quotient's geometric
Frobenius traces. The same scalar, full prime and coefficient label are used
on both sides of each equality.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

attribute [local instance] Ideal.Quotient.field
local instance eulerCohomologyFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance eulerCohomologyElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance eulerCohomologyFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- At the selected level-five fibre and oriented prime above eleven, the
actual labelled Euler quotient trace and direct complex value are images of
one algebraic scalar. -/
theorem primeFive_orientedEulerCohomologyTrace_11
    (𝒞 : SmoothProperEulerFamily 5 1)
    (𝒬 : SmoothProperRealEulerQuotient 5 1 𝒞)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField 5 →+* L)
    (R : RealEulerQuotientPlace 5 1 𝒞 𝒬 ℓ L ι)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) :
    let hgood := primeFive_realEulerParameter_goodUnit 11 P e (by decide) (by decide)
    let a := normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
      (P.specialization (realEulerParameter 5 primeFiveParameter)
        hgood.valuation_eq_one.le)
    letI : Module.Finite L ((R.action primeFiveParameter).component
      5 1 𝒞 𝒬 primeFiveParameter ℓ L ι) :=
      Module.Finite.equiv (R.componentComparison primeFiveParameter).symm
    LinearMap.trace L _
      ((R.action primeFiveParameter).componentGaloisEndomorphism
        5 1 𝒞 𝒬 primeFiveParameter ℓ L ι
          ((realEulerClosureGaloisHom 5).comp (restrictCyclotomicGalois 5)
            (absoluteGeometricFrobenius 5 P Q))) = ι a ∧
      primeFiveComplexEmbedding a = ((Real.sqrt 5 : ℂ) - 1) / 2 := by
  dsimp only
  constructor
  · exact RealEulerQuotientPlace.geometricFrobenius_trace_eq_normalizedEulerTrace
      5 1 𝒞 𝒬 primeFiveParameter ℓ L ι
      (by decide) (by decide) (by decide) (by decide) R P hP hℓ Q
      (primeFive_realEulerParameter_goodUnit 11 P e (by decide) (by decide))
  · exact primeFive_orientedEulerValue_at_specialization_11 P hP e he θ hθ

/-- The same selected quotient trace at forty-one and its direct complex
value arise from one normalized algebraic Euler scalar. -/
theorem primeFive_orientedEulerCohomologyTrace_41
    (𝒞 : SmoothProperEulerFamily 5 1)
    (𝒬 : SmoothProperRealEulerQuotient 5 1 𝒞)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField 5 →+* L)
    (R : RealEulerQuotientPlace 5 1 𝒞 𝒬 ℓ L ι)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) :
    let hgood := primeFive_realEulerParameter_goodUnit 41 P e (by decide) (by decide)
    let a := normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
      (P.specialization (realEulerParameter 5 primeFiveParameter)
        hgood.valuation_eq_one.le)
    letI : Module.Finite L ((R.action primeFiveParameter).component
      5 1 𝒞 𝒬 primeFiveParameter ℓ L ι) :=
      Module.Finite.equiv (R.componentComparison primeFiveParameter).symm
    LinearMap.trace L _
      ((R.action primeFiveParameter).componentGaloisEndomorphism
        5 1 𝒞 𝒬 primeFiveParameter ℓ L ι
          ((realEulerClosureGaloisHom 5).comp (restrictCyclotomicGalois 5)
            (absoluteGeometricFrobenius 5 P Q))) = ι a ∧
      primeFiveComplexEmbedding a = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 := by
  dsimp only
  constructor
  · exact RealEulerQuotientPlace.geometricFrobenius_trace_eq_normalizedEulerTrace
      5 1 𝒞 𝒬 primeFiveParameter ℓ L ι
      (by decide) (by decide) (by decide) (by decide) R P hP hℓ Q
      (primeFive_realEulerParameter_goodUnit 41 P e (by decide) (by decide))
  · exact primeFive_orientedEulerValue_at_specialization_41 P hP e he θ hθ

/-- The chosen descended effective local system itself has the actual Euler
scalar as its trace at the oriented eleven-prime Frobenius. -/
theorem primeFive_effectiveFrobeniusTrace_11
    (𝒞 : SmoothProperEulerFamily 5 1)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[5] L] [ContinuousSMul ℚ_[5] L]
    [FiniteDimensional ℚ_[5] L]
    (ι : cyclotomicField 5 →+* L)
    (D : ProperEulerRealDescent 5 1 5 L ι 𝒞)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    let hgood := primeFive_realEulerParameter_goodUnit 11 P e (by decide) (by decide)
    letI : Module.Finite L
      (D.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _
          (ProjectiveLine.puncturedPoint _ primeFiveParameter))) :=
      D.localSystem.finite _
    LinearMap.trace L _
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ primeFiveParameter)
        ((realEulerClosureGaloisHom 5).comp (restrictCyclotomicGalois 5)
          (absoluteGeometricFrobenius 5 P Q))) =
      ι (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
        (P.specialization (realEulerParameter 5 primeFiveParameter)
          hgood.valuation_eq_one.le)) := by
  exact ProperEulerRealDescent.geometricFrobenius_trace_eq_normalizedEulerTrace
    5 1 5 L ι (by decide) (by decide) (by decide) (by decide)
    𝒞 D P hP hP Q primeFiveParameter
    (primeFive_realEulerParameter_goodUnit 11 P e (by decide) (by decide))

/-- The analogous chosen descended effective trace at the oriented prime
above forty-one. -/
theorem primeFive_effectiveFrobeniusTrace_41
    (𝒞 : SmoothProperEulerFamily 5 1)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[5] L] [ContinuousSMul ℚ_[5] L]
    [FiniteDimensional ℚ_[5] L]
    (ι : cyclotomicField 5 →+* L)
    (D : ProperEulerRealDescent 5 1 5 L ι 𝒞)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    let hgood := primeFive_realEulerParameter_goodUnit 41 P e (by decide) (by decide)
    letI : Module.Finite L
      (D.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _
          (ProjectiveLine.puncturedPoint _ primeFiveParameter))) :=
      D.localSystem.finite _
    LinearMap.trace L _
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ primeFiveParameter)
        ((realEulerClosureGaloisHom 5).comp (restrictCyclotomicGalois 5)
          (absoluteGeometricFrobenius 5 P Q))) =
      ι (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
        (P.specialization (realEulerParameter 5 primeFiveParameter)
          hgood.valuation_eq_one.le)) := by
  exact ProperEulerRealDescent.geometricFrobenius_trace_eq_normalizedEulerTrace
    5 1 5 L ι (by decide) (by decide) (by decide) (by decide)
    𝒞 D P hP hP Q primeFiveParameter
    (primeFive_realEulerParameter_goodUnit 41 P e (by decide) (by decide))

end HilbertModularity.Examples
