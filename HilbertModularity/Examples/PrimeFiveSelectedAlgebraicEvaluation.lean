/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveNativeFrobeniusTransport
public import HilbertModularity.Examples.PrimeFiveAlgebraicLabelSelection
public import HilbertModularity.Examples.PrimeFiveRMEmbeddingOrder
public import HilbertModularity.Hypergeometric.DarmonPrimeNativeTrace

/-! # Algebraic evaluation of the worked comparison character

The actual selected Jacobian's native factors, the oriented finite Euler
values and the one chosen Euler/Darmon comparison are assembled in the
same algebraic coefficient field.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain Polynomial
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

attribute [local instance] Ideal.Quotient.field
local instance selectedEvaluationFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance selectedEvaluationElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance selectedEvaluationFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩
local notation "K₅" => realCyclotomicField 5
local notation "J₅" => primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter

/-- The oriented eleven-prime polynomial and the chosen cohomological
comparison select the actual native RM label and value one for the same
algebraic comparison character. -/
theorem primeFive_selectedAlgebraicEvaluation11
    (L : Type) [NontriviallyNormedField L] [NormedAlgebra ℚ_[5] L]
    [Algebra (cyclotomicField 5) L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (coeff : cyclotomicField 5 →+* L)
    (E' : IntermediateField (cyclotomicField 5) L) [NumberField E']
    (hcoeff : E'.subtype.comp (algebraMap (cyclotomicField 5) E') = coeff)
    (c : E' →+* ℂ)
    (hc : c.comp (algebraMap (cyclotomicField 5) E') = primeFiveComplexEmbedding)
    (χ : FiniteAlgebraicGaloisCharacter K₅ E')
    (ν : HilbertModularForms.AbsoluteGalois K₅ →* Lˣ)
    (hχ : (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν)
    (σ : K₅ →ₐ[ℚ] L)
    (q : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian q)
    [Fintype (𝓞 K₅ ⧸ q.asIdeal)]
    (hk : Fintype.card (𝓞 K₅ ⧸ q.asIdeal) = 11)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P.asIdeal.LiesOver q.asIdeal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4)
    (QbarPrime : Ideal (𝓞 Qbar))
    [QbarPrime.IsMaximal] [QbarPrime.LiesOver P.asIdeal]
    (hcard : Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) =
      Nat.card (𝓞 K₅ ⧸ q.asIdeal))
    (h5q : (5 : 𝓞 K₅) ∉ q.asIdeal)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1)
    (hpadic : coeff (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
        (e.symm 125)) =
      (ν (primeFiveRealFrobenius P QbarPrime) : L) *
        ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
          (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
            primeFiveParameter) σ).toRepresentation.dual).character
              (primeFiveRealFrobenius P QbarPrime)) :
    ∃ t : E',
      E'.subtype t =
        ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
          (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
            primeFiveParameter) σ).toRepresentation.dual).character
              (primeFiveRealFrobenius P QbarPrime) ∧
      c t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧
      primeFiveComplexComparisonCharacter E' χ c
        (primeFiveRealFrobenius P QbarPrime) = 1 := by
  let : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hlabels : ∃ labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L), labels 0 = σ := by
    with_reducible
      exact exists_primeFiveRMEmbeddingOrder L hL σ
  obtain ⟨labels, hlabel⟩ := hlabels
  let g := primeFiveRealFrobenius P QbarPrime
  let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 0)).toRepresentation.dual
  let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 1)).toRepresentation.dual
  let a := ρ₀.character g
  let b := ρ₁.character g
  have hpoly : (1 - C a * X + 11 * X ^ 2) *
      (1 - C b * X + 11 * X ^ 2) = primeFiveNumericalPolynomial11 L := by
    with_reducible
      exact primeFive_orientedRMCharacterPolynomial11 L hL labels q W hk P
        QbarPrime hcard h5q
  have hσ : a =
      ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) σ).toRepresentation.dual).character g := by
    with_reducible
      exact congrArg (fun τ : K₅ →ₐ[ℚ] L =>
        ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
          (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
            primeFiveParameter) τ).toRepresentation.dual).character g) hlabel
  have hpadic' : coeff (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
      (e.symm 125)) = (ν g : L) * a := by
    calc
      coeff (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1 (e.symm 125)) =
          (ν g : L) *
            ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
              (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
                primeFiveParameter) σ).toRepresentation.dual).character g := hpadic
      _ = (ν g : L) * a := by rw [←hσ]
  have hpolyLit : (1 - C a * X + 11 * X ^ 2) *
      (1 - C b * X + 11 * X ^ 2) =
        (1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 : L[X]) :=
    hpoly.trans (primeFiveNumericalPolynomial11_formula L)
  have hselect : ∃ t : E', E'.subtype t = a ∧
      c t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧
      primeFiveComplexComparisonCharacter E' χ c g = 1 := by
    with_reducible
      exact primeFive_algebraicSelector_of_padicFactorization_11
        L E' coeff hcoeff c hc χ ν hχ g P.asIdeal hP e he θ hθ a b
        hpolyLit hpadic'
  obtain ⟨t, ht, htrace, hvalue⟩ := hselect
  exact ⟨t, ht.trans hσ, htrace, hvalue⟩


/-- The oriented forty-one-prime polynomial and the chosen cohomological
comparison select the actual native RM label and value one for the same
algebraic comparison character. -/
theorem primeFive_selectedAlgebraicEvaluation41
    (L : Type) [NontriviallyNormedField L] [NormedAlgebra ℚ_[5] L]
    [Algebra (cyclotomicField 5) L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (coeff : cyclotomicField 5 →+* L)
    (E' : IntermediateField (cyclotomicField 5) L) [NumberField E']
    (hcoeff : E'.subtype.comp (algebraMap (cyclotomicField 5) E') = coeff)
    (c : E' →+* ℂ)
    (hc : c.comp (algebraMap (cyclotomicField 5) E') = primeFiveComplexEmbedding)
    (χ : FiniteAlgebraicGaloisCharacter K₅ E')
    (ν : HilbertModularForms.AbsoluteGalois K₅ →* Lˣ)
    (hχ : (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν)
    (σ : K₅ →ₐ[ℚ] L)
    (q : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian q)
    [Fintype (𝓞 K₅ ⧸ q.asIdeal)]
    (hk : Fintype.card (𝓞 K₅ ⧸ q.asIdeal) = 41)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P.asIdeal.LiesOver q.asIdeal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10)
    (QbarPrime : Ideal (𝓞 Qbar))
    [QbarPrime.IsMaximal] [QbarPrime.LiesOver P.asIdeal]
    (hcard : Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) =
      Nat.card (𝓞 K₅ ⧸ q.asIdeal))
    (h5q : (5 : 𝓞 K₅) ∉ q.asIdeal)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1)
    (hpadic : coeff (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
        (e.symm 125)) =
      (ν (primeFiveRealFrobenius P QbarPrime) : L) *
        ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
          (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
            primeFiveParameter) σ).toRepresentation.dual).character
              (primeFiveRealFrobenius P QbarPrime)) :
    ∃ t : E',
      E'.subtype t =
        ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
          (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
            primeFiveParameter) σ).toRepresentation.dual).character
              (primeFiveRealFrobenius P QbarPrime) ∧
      c t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧
      primeFiveComplexComparisonCharacter E' χ c
        (primeFiveRealFrobenius P QbarPrime) = 1 := by
  let : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hlabels : ∃ labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L), labels 0 = σ := by
    with_reducible
      exact exists_primeFiveRMEmbeddingOrder L hL σ
  obtain ⟨labels, hlabel⟩ := hlabels
  let g := primeFiveRealFrobenius P QbarPrime
  let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 0)).toRepresentation.dual
  let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 1)).toRepresentation.dual
  let a := ρ₀.character g
  let b := ρ₁.character g
  have hpoly : (1 - C a * X + 41 * X ^ 2) *
      (1 - C b * X + 41 * X ^ 2) = primeFiveNumericalPolynomial41 L := by
    with_reducible
      exact primeFive_orientedRMCharacterPolynomial41 L hL labels q W hk P
        QbarPrime hcard h5q
  have hσ : a =
      ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) σ).toRepresentation.dual).character g := by
    with_reducible
      exact congrArg (fun τ : K₅ →ₐ[ℚ] L =>
        ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
          (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
            primeFiveParameter) τ).toRepresentation.dual).character g) hlabel
  have hpadic' : coeff (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
      (e.symm 125)) = (ν g : L) * a := by
    calc
      coeff (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1 (e.symm 125)) =
          (ν g : L) *
            ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
              (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
                primeFiveParameter) σ).toRepresentation.dual).character g := hpadic
      _ = (ν g : L) * a := by rw [←hσ]
  have hpolyLit : (1 - C a * X + 41 * X ^ 2) *
      (1 - C b * X + 41 * X ^ 2) =
        (1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 : L[X]) :=
    hpoly.trans (primeFiveNumericalPolynomial41_formula L)
  have hselect : ∃ t : E', E'.subtype t = a ∧
      c t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧
      primeFiveComplexComparisonCharacter E' χ c g = 1 := by
    with_reducible
      exact primeFive_algebraicSelector_of_padicFactorization_41
        L E' coeff hcoeff c hc χ ν hχ g P.asIdeal hP e he θ hθ a b
        hpolyLit hpadic'
  obtain ⟨t, ht, htrace, hvalue⟩ := hselect
  exact ⟨t, ht.trans hσ, htrace, hvalue⟩


end HilbertModularity.Examples
