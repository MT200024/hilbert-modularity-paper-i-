/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveArithmeticTrace
public import HilbertModularity.Examples.PrimeFiveSelectedJacobian
public import HilbertModularity.Examples.PrimeFiveEulerCohomology
public import HilbertModularity.Hypergeometric.GaloisRealizationGenericMonodromy

/-! # Arithmetic trace of the chosen level-five comparison

The uniform finite comparison character constructed for the one chosen Euler
quotient and Darmon family is specialized to the actual parameter 125. Trace
of the existing representation equivalence gives the character-times-fixed-
RM-trace identity at every arithmetic Galois element, with the same label.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

local instance chosenComparisonFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance chosenComparisonElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance chosenComparisonFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- At the actual selected parameter, the one chosen Euler/Darmon
comparison gives a finite character and a trace equality at every Galois
element. The coefficient embedding is the original fixed first RM label. -/
theorem exists_primeFive_chosenArithmeticTraceComparison
    (hN : Nat.Prime 5) (h5 : 5 ≤ 5) (hmPos : 0 < 1) (hmN : 1 < 5)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField 5) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(5 : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[5] L] [FiniteDimensional ℚ_[5] L]
    [IsScalarTower ℚ_[5] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[5] L]
    (ι : cyclotomicField 5 →+* L)
    (hι : coefficientEmbeddingAbovePrime 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
      E ((IntermediateField.le_normalClosure (realCyclotomicField 5)).trans hE)
      w L (tau 5 1) = ι ((root 5) ^ 1 + (root 5)⁻¹ ^ 1)) :
    let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞
      hN h5 hmPos hmN
    let D := R.placeDescent 5 1 𝒞 5 L ι
    let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
      5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
      E hE w L
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ,
      Continuous ν ∧ (Set.range ν).Finite ∧
      ∀ g,
        (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
          primeFiveParameter D.localSystem).character g =
          (ν g : L) *
            (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
              primeFiveParameter F_RM).character g := by
  let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
  let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞
    hN h5 hmPos hmN
  let D := R.placeDescent 5 1 𝒞 5 L ι
  let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
    5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
    (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
    E hE w L
  obtain ⟨ν, hνc, hνfin, χ, hχ, _, hall⟩ :=
    exists_algebraic_character_comparing_chosenEuler_realization
      5 1 hN h5 hmPos hmN
      E hE w L ι hι primeFiveParameter
  refine ⟨ν, hνc, hνfin, ?_⟩
  intro g
  let : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
    (algebraMap E (w.adicCompletion E))).toAlgebra
  let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
  let : NumberField E' :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
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

/-- At eleven, the actual chosen Euler/Darmon comparison and the proper
Euler Frobenius theorem identify one algebraic scalar with the finite
character times the fixed labelled RM trace. Its positive complex value is
the direct finite-sum computation. -/
theorem exists_primeFive_chosenFrobeniusScalar_11
    (hN : Nat.Prime 5) (h5 : 5 ≤ 5) (hmPos : 0 < 1) (hmN : 1 < 5)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField 5) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(5 : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[5] L] [FiniteDimensional ℚ_[5] L]
    [IsScalarTower ℚ_[5] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[5] L]
    (ι : cyclotomicField 5 →+* L)
    (hι : coefficientEmbeddingAbovePrime 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
      E ((IntermediateField.le_normalClosure (realCyclotomicField 5)).trans hE)
      w L (tau 5 1) = ι ((root 5) ^ 1 + (root 5)⁻¹ ^ 1))
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) :
    let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞 hN h5 hmPos hmN
    let _D := R.placeDescent 5 1 𝒞 5 L ι
    let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
      5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN) E hE w L
    let hgood := primeFive_realEulerParameter_goodUnit 11 P e (by decide) (by decide)
    let a := normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
      (P.specialization (realEulerParameter 5 primeFiveParameter)
        hgood.valuation_eq_one.le)
    let g := ((realEulerClosureGaloisHom 5).comp (restrictCyclotomicGalois 5)
      (absoluteGeometricFrobenius 5 P Q))
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ,
      (Set.range ν).Finite ∧
        ι a = (ν g : L) *
          (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
            primeFiveParameter F_RM).character g ∧
        primeFiveComplexEmbedding a = ((Real.sqrt 5 : ℂ) - 1) / 2 := by
  let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
  let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞 hN h5 hmPos hmN
  let D := R.placeDescent 5 1 𝒞 5 L ι
  let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
    5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
    (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN) E hE w L
  let hgood := primeFive_realEulerParameter_goodUnit 11 P e (by decide) (by decide)
  let a := normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
    (P.specialization (realEulerParameter 5 primeFiveParameter)
      hgood.valuation_eq_one.le)
  let g := ((realEulerClosureGaloisHom 5).comp (restrictCyclotomicGalois 5)
    (absoluteGeometricFrobenius 5 P Q))
  obtain ⟨ν, _, hfin, htrace⟩ :=
    exists_primeFive_chosenArithmeticTraceComparison hN h5 hmPos hmN
      E hE w L ι hι
  refine ⟨ν, hfin, ?_, ?_⟩
  · have heff : (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter D.localSystem).character g = ι a := by
      exact primeFive_effectiveFrobeniusTrace_11 𝒞 L ι D P hP e Q
    change ι a = (ν g : L) *
      (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter F_RM).character g
    exact heff.symm.trans (htrace g)
  · exact primeFive_orientedEulerValue_at_specialization_11 P hP e he θ hθ


/-- At forty-one, the actual chosen Euler/Darmon comparison and the proper
Euler Frobenius theorem identify one algebraic scalar with the finite
character times the fixed labelled RM trace. Its positive complex value is
the direct finite-sum computation. -/
theorem exists_primeFive_chosenFrobeniusScalar_41
    (hN : Nat.Prime 5) (h5 : 5 ≤ 5) (hmPos : 0 < 1) (hmN : 1 < 5)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField 5) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(5 : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[5] L] [FiniteDimensional ℚ_[5] L]
    [IsScalarTower ℚ_[5] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[5] L]
    (ι : cyclotomicField 5 →+* L)
    (hι : coefficientEmbeddingAbovePrime 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
      E ((IntermediateField.le_normalClosure (realCyclotomicField 5)).trans hE)
      w L (tau 5 1) = ι ((root 5) ^ 1 + (root 5)⁻¹ ^ 1))
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) :
    let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞 hN h5 hmPos hmN
    let _D := R.placeDescent 5 1 𝒞 5 L ι
    let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
      5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN) E hE w L
    let hgood := primeFive_realEulerParameter_goodUnit 41 P e (by decide) (by decide)
    let a := normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
      (P.specialization (realEulerParameter 5 primeFiveParameter)
        hgood.valuation_eq_one.le)
    let g := ((realEulerClosureGaloisHom 5).comp (restrictCyclotomicGalois 5)
      (absoluteGeometricFrobenius 5 P Q))
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ,
      (Set.range ν).Finite ∧
        ι a = (ν g : L) *
          (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
            primeFiveParameter F_RM).character g ∧
        primeFiveComplexEmbedding a = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 := by
  let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
  let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞 hN h5 hmPos hmN
  let D := R.placeDescent 5 1 𝒞 5 L ι
  let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
    5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
    (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN) E hE w L
  let hgood := primeFive_realEulerParameter_goodUnit 41 P e (by decide) (by decide)
  let a := normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
    (P.specialization (realEulerParameter 5 primeFiveParameter)
      hgood.valuation_eq_one.le)
  let g := ((realEulerClosureGaloisHom 5).comp (restrictCyclotomicGalois 5)
    (absoluteGeometricFrobenius 5 P Q))
  obtain ⟨ν, _, hfin, htrace⟩ :=
    exists_primeFive_chosenArithmeticTraceComparison hN h5 hmPos hmN
      E hE w L ι hι
  refine ⟨ν, hfin, ?_, ?_⟩
  · have heff : (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter D.localSystem).character g = ι a := by
      exact primeFive_effectiveFrobeniusTrace_41 𝒞 L ι D P hP e Q
    change ι a = (ν g : L) *
      (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter F_RM).character g
    exact heff.symm.trans (htrace g)
  · exact primeFive_orientedEulerValue_at_specialization_41 P hP e he θ hθ

end HilbertModularity.Examples
