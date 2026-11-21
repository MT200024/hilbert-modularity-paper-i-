/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveComparisonCharacterComplex
public import HilbertModularity.Examples.PrimeFiveEulerCohomology

/-! # One chosen comparison character at both worked primes

The single generic Euler/Darmon comparison character is retained while the
eleven and forty-one Frobenius traces are evaluated. Both local equations use
the same algebraic character and its same oriented complex coefficient field.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

attribute [local instance] Ideal.Quotient.field
local instance jointFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance jointElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance jointFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The real-field Galois Frobenius obtained from the chosen cyclotomic
prime, with the same geometric-Frobenius convention as the Euler trace. -/
def primeFiveRealFrobenius
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) :=
  ((realEulerClosureGaloisHom 5).comp (restrictCyclotomicGalois 5))
    (absoluteGeometricFrobenius 5 P Q)

/-- The oriented real Frobenius is the fixed closure transport of the
chosen cyclotomic geometric lift. -/
theorem primeFiveRealFrobenius_eq_closureTransport
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    primeFiveRealFrobenius P Q =
      realEulerClosureGaloisHom 5
        (restrictCyclotomicGalois 5 (absoluteGeometricFrobenius 5 P Q)) :=
  (rfl)

/-- The actual chosen Euler/Darmon comparison supplies ONE finite
algebraic character, its all-fibre arithmetic equivalence, and its p-adic
Frobenius equations at both oriented worked primes. The same character
field retains the oriented complex embedding. -/
theorem exists_primeFive_jointFrobeniusComparison
    (hN : Nat.Prime 5) (h5 : 5 ≤ 5) (hmPos : 0 < 1) (hmN : 1 < 5)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [ContinuousSMul ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [NormedAlgebra ℚ_[5] L] [FiniteDimensional ℚ_[5] L]
    [IsScalarTower ℚ_[5] ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [Algebra ℚ L]
    [IsScalarTower ℚ ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [IsScalarTower ℚ ℚ_[5] L]
    (ι : cyclotomicField 5 →+* L)
    (hcoeff : (algebraMap ((primeAboveConductor 5).adicCompletion
      (cyclotomicField 5)) L).comp
        (algebraMap (cyclotomicField 5)
          ((primeAboveConductor 5).adicCompletion (cyclotomicField 5))) = ι)
    (P₁₁ : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP₁₁ : (5 : 𝓞 (cyclotomicField 5)) ∉ P₁₁.asIdeal)
    (e₁₁ : (𝓞 (cyclotomicField 5) ⧸ P₁₁.asIdeal) ≃+* ZMod 11)
    (Q₁₁ : Ideal (𝓞 Qbar)) [Q₁₁.IsMaximal] [Q₁₁.LiesOver P₁₁.asIdeal]
    (P₄₁ : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP₄₁ : (5 : 𝓞 (cyclotomicField 5)) ∉ P₄₁.asIdeal)
    (e₄₁ : (𝓞 (cyclotomicField 5) ⧸ P₄₁.asIdeal) ≃+* ZMod 41)
    (Q₄₁ : Ideal (𝓞 Qbar)) [Q₄₁.IsMaximal] [Q₄₁.LiesOver P₄₁.asIdeal] :
    let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞 hN h5 hmPos hmN
    let D := R.placeDescent 5 1 𝒞 5 L ι
    let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
      5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
      (cyclotomicField 5) primeFive_normalClosure_le_cyclotomic
      (primeAboveConductor 5) L
    let g₁₁ := primeFiveRealFrobenius P₁₁ Q₁₁
    let g₄₁ := primeFiveRealFrobenius P₄₁ Q₄₁
    let hgood₁₁ := primeFive_realEulerParameter_goodUnit 11 P₁₁ e₁₁
      (by decide) (by decide)
    let hgood₄₁ := primeFive_realEulerParameter_goodUnit 41 P₄₁ e₄₁
      (by decide) (by decide)
    let a₁₁ := normalizedCyclotomicEulerTrace 5 P₁₁.asIdeal hP₁₁ 1
      (P₁₁.specialization (realEulerParameter 5 primeFiveParameter)
        hgood₁₁.valuation_eq_one.le)
    let a₄₁ := normalizedCyclotomicEulerTrace 5 P₄₁.asIdeal hP₄₁ 1
      (P₄₁.specialization (realEulerParameter 5 primeFiveParameter)
        hgood₄₁.valuation_eq_one.le)
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        letI : Algebra (cyclotomicField 5) L :=
          ((algebraMap ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L).comp
            (algebraMap (cyclotomicField 5)
              ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)))).toAlgebra
        let E' := RepresentationTheory.finiteCharacterCoefficientField
          (E₀ := cyclotomicField 5) ν
        letI : NumberField E' :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField 5) E',
          (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          ∃ c : E' →+* ℂ,
            c.comp (algebraMap (cyclotomicField 5) E') = primeFiveComplexEmbedding ∧
            (∀ ξ : ProjectiveLine.Parameter (realCyclotomicField 5),
              Nonempty (((Representation.ofCharacter
                ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
                  (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
                    ξ F_RM)).Equiv
                    (puncturedFiberArithmeticRepresentation
                      (realCyclotomicField 5) ξ D.localSystem))) ∧
            ι a₁₁ = (ν g₁₁ : L) *
              (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
                primeFiveParameter F_RM).character g₁₁ ∧
            ι a₄₁ = (ν g₄₁ : L) *
              (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
                primeFiveParameter F_RM).character g₄₁ := by
  let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
  let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞 hN h5 hmPos hmN
  let D := R.placeDescent 5 1 𝒞 5 L ι
  let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
    5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
    (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
    (cyclotomicField 5) primeFive_normalClosure_le_cyclotomic
    (primeAboveConductor 5) L
  let g₁₁ := primeFiveRealFrobenius P₁₁ Q₁₁
  let g₄₁ := primeFiveRealFrobenius P₄₁ Q₄₁
  let hgood₁₁ := primeFive_realEulerParameter_goodUnit 11 P₁₁ e₁₁
    (by decide) (by decide)
  let hgood₄₁ := primeFive_realEulerParameter_goodUnit 41 P₄₁ e₄₁
    (by decide) (by decide)
  let a₁₁ := normalizedCyclotomicEulerTrace 5 P₁₁.asIdeal hP₁₁ 1
    (P₁₁.specialization (realEulerParameter 5 primeFiveParameter)
      hgood₁₁.valuation_eq_one.le)
  let a₄₁ := normalizedCyclotomicEulerTrace 5 P₄₁.asIdeal hP₄₁ 1
    (P₄₁.specialization (realEulerParameter 5 primeFiveParameter)
      hgood₄₁.valuation_eq_one.le)
  obtain ⟨ν, hνc, hνfin, χ, hχ, c, hc, hall, htrace⟩ :=
    exists_primeFive_comparisonCharacter_complexRealization
      hN h5 hmPos hmN L ι hcoeff
  refine ⟨ν, hνc, hνfin, χ, hχ, c, hc, ?_, ?_, ?_⟩
  · intro ξ
    with_reducible exact hall ξ
  · have heff : (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter D.localSystem).character g₁₁ = ι a₁₁ := by
      exact primeFive_effectiveFrobeniusTrace_11 𝒞 L ι D P₁₁ hP₁₁ e₁₁ Q₁₁
    change ι a₁₁ = (ν g₁₁ : L) *
      (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter F_RM).character g₁₁
    exact heff.symm.trans (htrace g₁₁)
  · have heff : (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter D.localSystem).character g₄₁ = ι a₄₁ := by
      exact primeFive_effectiveFrobeniusTrace_41 𝒞 L ι D P₄₁ hP₄₁ e₄₁ Q₄₁
    change ι a₄₁ = (ν g₄₁ : L) *
      (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter F_RM).character g₄₁
    exact heff.symm.trans (htrace g₄₁)

end HilbertModularity.Examples
