/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedAlgebraicEvaluation
public import HilbertModularity.Examples.PrimeFiveOrientedSelectedFiber

/-! # One chosen comparison character at both selected model primes -/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

attribute [local instance] Ideal.Quotient.field
local instance jointSelectedFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance jointSelectedElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance jointSelectedFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The specified residue equivalence gives equal full and real residue
cardinalities at the contracted prime; goodness away from five descends. -/
theorem primeFive_orientedPrime_realResidueData
    (n : ℕ) [NeZero n]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod n)
    (hreal : Nat.card (𝓞 (realCyclotomicField 5) ⧸
      (primeFiveRealPrimeBelow P).asIdeal) = n) :
    P.asIdeal.LiesOver (primeFiveRealPrimeBelow P).asIdeal ∧
      (5 : 𝓞 (realCyclotomicField 5)) ∉ (primeFiveRealPrimeBelow P).asIdeal ∧
      Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) =
        Nat.card (𝓞 (realCyclotomicField 5) ⧸
          (primeFiveRealPrimeBelow P).asIdeal) := by
  let q := primeFiveRealPrimeBelow P
  have hover : P.asIdeal.LiesOver q.asIdeal := by
    constructor
    dsimp only [q]
    exact primeFiveRealPrimeBelow_asIdeal P
  have h5q : (5 : 𝓞 (realCyclotomicField 5)) ∉ q.asIdeal := by
    intro hm
    have hmP : (5 : 𝓞 (cyclotomicField 5)) ∈ P.asIdeal := by
      simpa only [map_ofNat] using
        (Ideal.mem_of_liesOver P.asIdeal q.asIdeal
          (5 : 𝓞 (realCyclotomicField 5))).mp hm
    exact hP hmP
  have hfull : Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) = n := by
    let : Fintype (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) := Fintype.ofFinite _
    simpa [Nat.card_eq_fintype_card, ZMod.card] using Fintype.card_congr e.toEquiv
  exact ⟨hover, h5q, hfull.trans hreal.symm⟩

/-- A value one in the oriented complex realization forces value one for
the same finite algebraic character in the chosen local coefficient field. -/
theorem padicComparisonValue_eq_one_of_complex
    (L : Type*) [Field L] [Algebra (cyclotomicField 5) L]
    (E' : IntermediateField (cyclotomicField 5) L) [NumberField E']
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField 5) E')
    (ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ)
    (hχ : (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν)
    (c : E' →+* ℂ)
    (g : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5))
    (hcomplex : primeFiveComplexComparisonCharacter E' χ c g = 1) :
    ν g = 1 := by
  have hχcomplex : c (χ.toMonoidHom g : E') = 1 := by
    have h := congrArg (fun u : ℂˣ => (u : ℂ)) hcomplex
    simpa only [primeFiveComplexComparisonCharacter_apply, Units.val_one] using h
  have hχone : (χ.toMonoidHom g : E') = 1 := by
    apply c.injective
    simpa only [map_one] using hχcomplex
  have hp := congrArg (fun f : HilbertModularForms.AbsoluteGalois
      (realCyclotomicField 5) →* Lˣ => f g) hχ
  change Units.map E'.subtype.toMonoidHom (χ.toMonoidHom g) = ν g at hp
  have hu : χ.toMonoidHom g = 1 := Units.ext hχone
  rw [hu] at hp
  simpa only [map_one] using hp.symm

/-- For any two selected oriented primes and their actual good Jacobian
models, the one chosen arithmetic comparison character retains its
all-fibre Euler–Darmon equivalence and has value one at both Frobenius
elements. -/
theorem exists_primeFive_jointSelectedCharacterValues
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [ContinuousSMul ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [NormedAlgebra ℚ_[5] L] [FiniteDimensional ℚ_[5] L]
    [IsScalarTower ℚ_[5] ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [Algebra ℚ L]
    [IsScalarTower ℚ ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [IsScalarTower ℚ ℚ_[5] L]
    (coeff : cyclotomicField 5 →+* L)
    (hcoeff : (algebraMap ((primeAboveConductor 5).adicCompletion
      (cyclotomicField 5)) L).comp
        (algebraMap (cyclotomicField 5)
          ((primeAboveConductor 5).adicCompletion (cyclotomicField 5))) = coeff)
    (P₁₁ : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP₁₁ : (5 : 𝓞 (cyclotomicField 5)) ∉ P₁₁.asIdeal)
    (e₁₁ : (𝓞 (cyclotomicField 5) ⧸ P₁₁.asIdeal) ≃+* ZMod 11)
    (he₁₁ : e₁₁ (Ideal.Quotient.mk P₁₁.asIdeal (rootInteger 5)) = 4)
    (hcard₁₁ : Nat.card (𝓞 (realCyclotomicField 5) ⧸
      (primeFiveRealPrimeBelow P₁₁).asIdeal) = 11)
    (W₁₁ : PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P₁₁))
    (P₄₁ : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP₄₁ : (5 : 𝓞 (cyclotomicField 5)) ∉ P₄₁.asIdeal)
    (e₄₁ : (𝓞 (cyclotomicField 5) ⧸ P₄₁.asIdeal) ≃+* ZMod 41)
    (he₄₁ : e₄₁ (Ideal.Quotient.mk P₄₁.asIdeal (rootInteger 5)) = 10)
    (hcard₄₁ : Nat.card (𝓞 (realCyclotomicField 5) ⧸
      (primeFiveRealPrimeBelow P₄₁).asIdeal) = 41)
    (W₄₁ : PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P₄₁))
    (θ₁₁ : AddChar (ZMod 11) ℂ) (hθ₁₁ : θ₁₁ ≠ 1)
    (θ₄₁ : AddChar (ZMod 41) ℂ) (hθ₄₁ : θ₄₁ ≠ 1) :
    let 𝒞 := chosenSmoothProperEulerFamily 5 1 (by decide) (by decide)
      (by decide) (by decide)
    let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞
      (by decide) (by decide) (by decide) (by decide)
    let D := R.placeDescent 5 1 𝒞 5 L coeff
    let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
      5 (by decide : 3 ≤ 5) 5 1
      (eulerExponent_coprime_of_prime 5 1
        (by decide) (by decide) (by decide))
      (cyclotomicField 5) primeFive_normalClosure_le_cyclotomic
      (primeAboveConductor 5) L
    let g₁₁ := primeFiveRealFrobenius P₁₁ (absolutePrime 5 P₁₁)
    let g₄₁ := primeFiveRealFrobenius P₄₁ (absolutePrime 5 P₄₁)
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
            primeFiveComplexComparisonCharacter E' χ c g₁₁ = 1 ∧
            primeFiveComplexComparisonCharacter E' χ c g₄₁ = 1 := by
  let q₁₁ := primeFiveRealPrimeBelow P₁₁
  let q₄₁ := primeFiveRealPrimeBelow P₄₁
  let Q₁₁ := absolutePrime 5 P₁₁
  let Q₄₁ := absolutePrime 5 P₄₁
  let : P₁₁.asIdeal.LiesOver q₁₁.asIdeal :=
    (primeFive_orientedPrime_realResidueData 11 P₁₁ hP₁₁ e₁₁ hcard₁₁).1
  let : P₄₁.asIdeal.LiesOver q₄₁.asIdeal :=
    (primeFive_orientedPrime_realResidueData 41 P₄₁ hP₄₁ e₄₁ hcard₄₁).1
  have h5q₁₁ : (5 : 𝓞 (realCyclotomicField 5)) ∉ q₁₁.asIdeal :=
    (primeFive_orientedPrime_realResidueData 11 P₁₁ hP₁₁ e₁₁ hcard₁₁).2.1
  have h5q₄₁ : (5 : 𝓞 (realCyclotomicField 5)) ∉ q₄₁.asIdeal :=
    (primeFive_orientedPrime_realResidueData 41 P₄₁ hP₄₁ e₄₁ hcard₄₁).2.1
  have hdegree₁₁ : Nat.card (𝓞 (cyclotomicField 5) ⧸ P₁₁.asIdeal) =
      Nat.card (𝓞 (realCyclotomicField 5) ⧸ q₁₁.asIdeal) :=
    (primeFive_orientedPrime_realResidueData 11 P₁₁ hP₁₁ e₁₁ hcard₁₁).2.2
  have hdegree₄₁ : Nat.card (𝓞 (cyclotomicField 5) ⧸ P₄₁.asIdeal) =
      Nat.card (𝓞 (realCyclotomicField 5) ⧸ q₄₁.asIdeal) :=
    (primeFive_orientedPrime_realResidueData 41 P₄₁ hP₄₁ e₄₁ hcard₄₁).2.2
  let : Fintype (𝓞 (realCyclotomicField 5) ⧸ q₁₁.asIdeal) := Fintype.ofFinite _
  let : Fintype (𝓞 (realCyclotomicField 5) ⧸ q₄₁.asIdeal) := Fintype.ofFinite _
  have hk₁₁ : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ q₁₁.asIdeal) = 11 := by
    simpa only [Nat.card_eq_fintype_card] using hcard₁₁
  have hk₄₁ : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ q₄₁.asIdeal) = 41 := by
    simpa only [Nat.card_eq_fintype_card] using hcard₄₁
  let g₁₁ := primeFiveRealFrobenius P₁₁ Q₁₁
  let g₄₁ := primeFiveRealFrobenius P₄₁ Q₄₁
  let 𝒞 := chosenSmoothProperEulerFamily 5 1 (by decide) (by decide)
    (by decide) (by decide)
  let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞
    (by decide) (by decide) (by decide) (by decide)
  let D := R.placeDescent 5 1 𝒞 5 L coeff
  let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
    5 (by decide : 3 ≤ 5) 5 1
    (eulerExponent_coprime_of_prime 5 1
      (by decide) (by decide) (by decide))
    (cyclotomicField 5) primeFive_normalClosure_le_cyclotomic
    (primeAboveConductor 5) L
  let σ : realCyclotomicField 5 →ₐ[ℚ] L := by
    with_reducible
      exact coefficientEmbeddingAbovePrime 5 1
        (eulerExponent_coprime_of_prime 5 1
          (by decide) (by decide) (by decide))
        (cyclotomicField 5)
        ((IntermediateField.le_normalClosure (realCyclotomicField 5)).trans
          primeFive_normalClosure_le_cyclotomic)
        (primeAboveConductor 5) L
  have hcomparison := by
    with_reducible
      exact exists_primeFive_jointFrobeniusComparison
        (by decide : Nat.Prime 5) (by decide : 5 ≤ 5)
        (by decide : 0 < 1) (by decide : 1 < 5)
        L coeff hcoeff P₁₁ hP₁₁ e₁₁ Q₁₁ P₄₁ hP₄₁ e₄₁ Q₄₁
  obtain ⟨ν, hνc, hνfin, χ, hχ, c, hc, hall, htrace₁₁, htrace₄₁⟩ := hcomparison
  let : Algebra (cyclotomicField 5) L :=
    ((algebraMap ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L).comp
      (algebraMap (cyclotomicField 5)
        ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)))).toAlgebra
  let E' := RepresentationTheory.finiteCharacterCoefficientField
    (E₀ := cyclotomicField 5) ν
  let : NumberField E' :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
  have hι : E'.subtype.comp (algebraMap (cyclotomicField 5) E') = coeff := by
    calc
      E'.subtype.comp (algebraMap (cyclotomicField 5) E') =
          (algebraMap (cyclotomicField 5) L) := by
            ext x
            rfl
      _ = coeff := hcoeff
  let : (primeAboveConductor 5).asIdeal.LiesOver (Ideal.span {(5 : ℤ)}) :=
    primeAboveConductor_liesOver 5
  let hL : ∀ a : realCyclotomicField 5,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits :=
    splits_minpoly_above_coefficientPrime 5
      (cyclotomicField 5) (primeAboveConductor 5) L
      primeFive_normalClosure_le_cyclotomic
  have hnative₁₁ := by
    with_reducible
      exact darmonPrimeCohomological_character_eq_native
        5 (by decide : 5 ≤ 5) 1
        (eulerExponent_coprime_of_prime 5 1
          (by decide) (by decide) (by decide))
        primeFiveParameter (cyclotomicField 5)
        primeFive_normalClosure_le_cyclotomic (primeAboveConductor 5) L g₁₁
  have hnative₄₁ := by
    with_reducible
      exact darmonPrimeCohomological_character_eq_native
        5 (by decide : 5 ≤ 5) 1
        (eulerExponent_coprime_of_prime 5 1
          (by decide) (by decide) (by decide))
        primeFiveParameter (cyclotomicField 5)
        primeFive_normalClosure_le_cyclotomic (primeAboveConductor 5) L g₄₁
  have hnative₁₁' :
      (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter F_RM).character g₁₁ =
      ((endomorphismLabelledTate (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
        5 (realCyclotomicField 5) L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) σ).toRepresentation.dual).character g₁₁ := by
    conv_lhs =>
      change (F_RM.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint (realCyclotomicField 5)
          primeFiveParameter)).character g₁₁
    with_reducible exact hnative₁₁
  have hpadic₁₁ : coeff (normalizedCyclotomicEulerTrace 5
      P₁₁.asIdeal hP₁₁ 1 (e₁₁.symm 125)) =
      (ν g₁₁ : L) *
        ((endomorphismLabelledTate (realCyclotomicField 5)
          (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
          5 (realCyclotomicField 5) L hL
          (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
            primeFiveParameter) σ).toRepresentation.dual).character g₁₁ := by
    have hs := primeFive_realEulerParameter_specialization 11 P₁₁ e₁₁
      (by decide) (by decide)
    rw [hs] at htrace₁₁
    rw [hnative₁₁'] at htrace₁₁
    with_reducible exact htrace₁₁
  have hnative₄₁' :
      (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
        primeFiveParameter F_RM).character g₄₁ =
      ((endomorphismLabelledTate (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
        5 (realCyclotomicField 5) L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) σ).toRepresentation.dual).character g₄₁ := by
    conv_lhs =>
      change (F_RM.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint (realCyclotomicField 5)
          primeFiveParameter)).character g₄₁
    with_reducible exact hnative₄₁
  have hpadic₄₁ : coeff (normalizedCyclotomicEulerTrace 5
      P₄₁.asIdeal hP₄₁ 1 (e₄₁.symm 125)) =
      (ν g₄₁ : L) *
        ((endomorphismLabelledTate (realCyclotomicField 5)
          (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
          5 (realCyclotomicField 5) L hL
          (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
            primeFiveParameter) σ).toRepresentation.dual).character g₄₁ := by
    have hs := primeFive_realEulerParameter_specialization 41 P₄₁ e₄₁
      (by decide) (by decide)
    rw [hs] at htrace₄₁
    rw [hnative₄₁'] at htrace₄₁
    with_reducible exact htrace₄₁
  have hselected₁₁ := by
    with_reducible
      exact primeFive_selectedAlgebraicEvaluation11
        L hL coeff E' hι c hc χ ν hχ σ q₁₁ W₁₁ hk₁₁
        P₁₁ hP₁₁ e₁₁ he₁₁ Q₁₁ hdegree₁₁ h5q₁₁
        θ₁₁ hθ₁₁ hpadic₁₁
  have hselected₄₁ := by
    with_reducible
      exact primeFive_selectedAlgebraicEvaluation41
        L hL coeff E' hι c hc χ ν hχ σ q₄₁ W₄₁ hk₄₁
        P₄₁ hP₄₁ e₄₁ he₄₁ Q₄₁ hdegree₄₁ h5q₄₁
        θ₄₁ hθ₄₁ hpadic₄₁
  obtain ⟨_, _, _, hvalue₁₁⟩ := hselected₁₁
  obtain ⟨_, _, _, hvalue₄₁⟩ := hselected₄₁
  refine ⟨ν, hνc, hνfin, χ, hχ, c, hc, ?_, hvalue₁₁, hvalue₄₁⟩
  intro ξ
  with_reducible exact hall ξ

/-- The selected (p=5,m=1,\xi=125) model admits actual oriented
degree-one primes at eleven and forty-one. One finite character retains
the chosen Euler–Darmon equivalence at every nonsingular fibre and evaluates
to one at both primes. The selected good Jacobians and reduced fifth-root
orientations are produced in the proof. -/
theorem exists_primeFive_selectedExampleComparisonCharacter
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [ContinuousSMul ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [NormedAlgebra ℚ_[5] L] [FiniteDimensional ℚ_[5] L]
    [IsScalarTower ℚ_[5] ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [Algebra ℚ L]
    [IsScalarTower ℚ ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [IsScalarTower ℚ ℚ_[5] L]
    (coeff : cyclotomicField 5 →+* L)
    (hcoeff : (algebraMap ((primeAboveConductor 5).adicCompletion
      (cyclotomicField 5)) L).comp
        (algebraMap (cyclotomicField 5)
          ((primeAboveConductor 5).adicCompletion (cyclotomicField 5))) = coeff)
    (θ₁₁ : AddChar (ZMod 11) ℂ) (hθ₁₁ : θ₁₁ ≠ 1)
    (θ₄₁ : AddChar (ZMod 41) ℂ) (hθ₄₁ : θ₄₁ ≠ 1) :
    let 𝒞 := chosenSmoothProperEulerFamily 5 1 (by decide) (by decide)
      (by decide) (by decide)
    let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞
      (by decide) (by decide) (by decide) (by decide)
    let D := R.placeDescent 5 1 𝒞 5 L coeff
    let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
      5 (by decide : 3 ≤ 5) 5 1
      (eulerExponent_coprime_of_prime 5 1
        (by decide) (by decide) (by decide))
      (cyclotomicField 5) primeFive_normalClosure_le_cyclotomic
      (primeAboveConductor 5) L
    ∃ P₁₁ : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      ∃ (_ : (5 : 𝓞 (cyclotomicField 5)) ∉ P₁₁.asIdeal),
        ∃ e₁₁ : (𝓞 (cyclotomicField 5) ⧸ P₁₁.asIdeal) ≃+* ZMod 11,
          e₁₁ (Ideal.Quotient.mk P₁₁.asIdeal (rootInteger 5)) = 4 ∧
          Nat.card (𝓞 (realCyclotomicField 5) ⧸
            (primeFiveRealPrimeBelow P₁₁).asIdeal) = 11 ∧
          Nonempty (PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P₁₁)) ∧
          ∃ P₄₁ : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
            ∃ (_ : (5 : 𝓞 (cyclotomicField 5)) ∉ P₄₁.asIdeal),
              ∃ e₄₁ : (𝓞 (cyclotomicField 5) ⧸ P₄₁.asIdeal) ≃+* ZMod 41,
                e₄₁ (Ideal.Quotient.mk P₄₁.asIdeal (rootInteger 5)) = 10 ∧
                Nat.card (𝓞 (realCyclotomicField 5) ⧸
                  (primeFiveRealPrimeBelow P₄₁).asIdeal) = 41 ∧
                Nonempty (PrimeFiveSelectedSpecialJacobian (primeFiveRealPrimeBelow P₄₁)) ∧
                ∃ ν : HilbertModularForms.AbsoluteGalois
                    (realCyclotomicField 5) →* Lˣ,
                  Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
                    letI : Algebra (cyclotomicField 5) L :=
                      ((algebraMap ((primeAboveConductor 5).adicCompletion
                        (cyclotomicField 5)) L).comp
                          (algebraMap (cyclotomicField 5)
                            ((primeAboveConductor 5).adicCompletion
                              (cyclotomicField 5)))).toAlgebra
                    let E' := RepresentationTheory.finiteCharacterCoefficientField
                      (E₀ := cyclotomicField 5) ν
                    letI : NumberField E' :=
                      RepresentationTheory.numberField_finiteCharacterCoefficientField
                        ν hνfin
                    ∃ χ : FiniteAlgebraicGaloisCharacter
                        (realCyclotomicField 5) E',
                      (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
                      (∀ ξ : ProjectiveLine.Parameter (realCyclotomicField 5),
                        Nonempty (((Representation.ofCharacter
                          ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
                            (puncturedFiberArithmeticRepresentation
                              (realCyclotomicField 5) ξ F_RM)).Equiv
                              (puncturedFiberArithmeticRepresentation
                                (realCyclotomicField 5) ξ D.localSystem))) ∧
                      ν (primeFiveRealFrobenius P₁₁ (absolutePrime 5 P₁₁)) = 1 ∧
                      ν (primeFiveRealFrobenius P₄₁ (absolutePrime 5 P₄₁)) = 1 := by
  obtain ⟨P₁₁, hP₁₁, hcard₁₁, ⟨e₁₁, he₁₁⟩, hW₁₁⟩ :=
    exists_primeFive_orientedSelectedSpecialFiber_11
  obtain ⟨P₄₁, hP₄₁, hcard₄₁, ⟨e₄₁, he₄₁⟩, hW₄₁⟩ :=
    exists_primeFive_orientedSelectedSpecialFiber_41
  let W₁₁ := hW₁₁.some
  let W₄₁ := hW₄₁.some
  have hselected := by
    with_reducible
      exact exists_primeFive_jointSelectedCharacterValues
        L coeff hcoeff P₁₁ hP₁₁ e₁₁ he₁₁ hcard₁₁ W₁₁
        P₄₁ hP₄₁ e₄₁ he₄₁ hcard₄₁ W₄₁ θ₁₁ hθ₁₁ θ₄₁ hθ₄₁
  obtain ⟨ν, hνc, hνfin, χ, hχ, c, hc, hall,
    hcomplex₁₁, hcomplex₄₁⟩ := hselected
  let : Algebra (cyclotomicField 5) L :=
    ((algebraMap ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L).comp
      (algebraMap (cyclotomicField 5)
        ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)))).toAlgebra
  let E' := RepresentationTheory.finiteCharacterCoefficientField
    (E₀ := cyclotomicField 5) ν
  let : NumberField E' :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
  have hν₁₁ : ν (primeFiveRealFrobenius P₁₁ (absolutePrime 5 P₁₁)) = 1 := by
    with_reducible
      exact padicComparisonValue_eq_one_of_complex L E' χ ν hχ c
        (primeFiveRealFrobenius P₁₁ (absolutePrime 5 P₁₁)) hcomplex₁₁
  have hν₄₁ : ν (primeFiveRealFrobenius P₄₁ (absolutePrime 5 P₄₁)) = 1 := by
    with_reducible
      exact padicComparisonValue_eq_one_of_complex L E' χ ν hχ c
        (primeFiveRealFrobenius P₄₁ (absolutePrime 5 P₄₁)) hcomplex₄₁
  refine ⟨P₁₁, hP₁₁, e₁₁, he₁₁, hcard₁₁, hW₁₁,
    P₄₁, hP₄₁, e₄₁, he₄₁, hcard₄₁, hW₄₁,
    ν, hνc, hνfin, χ, hχ, ?_, hν₁₁, hν₄₁⟩
  intro ξ
  with_reducible exact hall ξ

end HilbertModularity.Examples
