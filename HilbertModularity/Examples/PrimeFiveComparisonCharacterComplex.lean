/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveCanonicalCoefficient
public import HilbertModularity.Examples.PrimeFiveCoefficientEmbedding

/-! # One algebraic comparison character with the oriented complex label

The finite character of the actual chosen Euler/Darmon comparison is kept in
its number field of values. A complex embedding of that field extends the
same fifth-cyclotomic embedding used for the worked McCarthy sums. This is
the coefficient-field part of the fixed-label comparison, before evaluating
the RM trace at a particular Frobenius.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

local instance comparisonComplexFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The actual finite algebraic comparison character in any chosen complex
coefficient realization. -/
def primeFiveComplexComparisonCharacter
    (E' : Type*) [Field E'] [NumberField E']
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField 5) E')
    (c : E' →+* ℂ) :
    HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* ℂˣ :=
  (Units.map c.toMonoidHom).comp χ.toMonoidHom

/-- Its finite range is inherited from the same algebraic character; no
new finite-order character is selected. -/
theorem primeFiveComplexComparisonCharacter_finite
    (E' : Type*) [Field E'] [NumberField E']
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField 5) E')
    (c : E' →+* ℂ) :
    (Set.range (primeFiveComplexComparisonCharacter E' χ c)).Finite := by
  simpa only [primeFiveComplexComparisonCharacter, MonoidHom.coe_comp,
    Set.range_comp] using χ.finite_range.image (Units.map c.toMonoidHom)

/-- Evaluation in the complex field is the image of the *same* algebraic
comparison-character value. -/
theorem primeFiveComplexComparisonCharacter_apply
    (E' : Type*) [Field E'] [NumberField E']
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField 5) E')
    (c : E' →+* ℂ)
    (g : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5)) :
    (primeFiveComplexComparisonCharacter E' χ c g : ℂ) = c (χ.toMonoidHom g : E') :=
  (rfl)

/-- The chosen finite p-adic comparison character is the image of one
algebraic character, and its coefficient field has an oriented complex
embedding extending the exact prime-five character convention. The original
all-fibre Euler–Darmon equivalence for that same character is retained. -/
theorem exists_primeFive_comparisonCharacter_complexRealization
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
          ((primeAboveConductor 5).adicCompletion (cyclotomicField 5))) = ι) :
    let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞 hN h5 hmPos hmN
    let D := R.placeDescent 5 1 𝒞 5 L ι
    let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
      5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
      (cyclotomicField 5) primeFive_normalClosure_le_cyclotomic
      (primeAboveConductor 5) L
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
              ∀ g,
                (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
                  primeFiveParameter D.localSystem).character g =
                  (ν g : L) *
                    (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
                      primeFiveParameter F_RM).character g := by
  let : (primeAboveConductor 5).asIdeal.LiesOver (Ideal.span {(5 : ℤ)}) :=
    primeAboveConductor_liesOver 5
  let E := cyclotomicField 5
  let w := primeAboveConductor 5
  let hE := primeFive_normalClosure_le_cyclotomic
  let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
  let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞 hN h5 hmPos hmN
  let D := R.placeDescent 5 1 𝒞 5 L ι
  let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
    5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
    (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN) E hE w L
  have hι := primeFive_coefficientEmbeddingAbovePrime_tau hN hmPos hmN L ι hcoeff
  obtain ⟨ν, hνc, hνfin, χ, hχ, _, hall⟩ :=
    exists_algebraic_character_comparing_chosenEuler_realization
      5 1 hN h5 hmPos hmN E hE w L ι hι primeFiveParameter
  let : Algebra E L :=
    ((algebraMap (w.adicCompletion E) L).comp (algebraMap E (w.adicCompletion E))).toAlgebra
  let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
  let : NumberField E' :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
  obtain ⟨c, hc⟩ := exists_primeFiveComplexEmbedding_extension E'
    (algebraMap E E')
  refine ⟨ν, hνc, hνfin, χ, hχ, c, hc, ?_, ?_⟩
  · intro ξ
    with_reducible exact hall ξ
  intro g
  obtain ⟨e⟩ := hall primeFiveParameter
  have ht := trace_of_characterTensorEquiv
    (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
      primeFiveParameter F_RM)
    (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
      primeFiveParameter D.localSystem)
    ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom) e g
  change (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
    primeFiveParameter D.localSystem).character g =
      (ν g : L) *
        (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
          primeFiveParameter F_RM).character g
  have hχg : ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom) g = ν g :=
    congrArg (fun f => f g) hχ
  rw [hχg] at ht
  exact ht

end HilbertModularity.Examples
