/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedRMNumericFactors
public import HilbertModularity.Examples.PrimeFiveRMQuadraticCharacter

/-! # Selected RM polynomials using intrinsic character traces -/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain Polynomial
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

local instance selectedCharacterFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local notation "K₅" => realCyclotomicField 5
local notation "J₅" => primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter

/-- At eleven, the two *actual* native RM representation characters,
without any chosen matrix bases, factor the counted polynomial. -/
theorem primeFiveSelectedRM_characterPolynomial11
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L))
    (P : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 K₅ ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 K₅ ⧸ P.asIdeal) = 11)
    (Q : Ideal (𝓞 (AlgebraicClosure K₅)))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 K₅) ∉ P.asIdeal) :
    let g := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) P.asIdeal Q
    let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 0)).toRepresentation.dual
    let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 1)).toRepresentation.dual
    (1 - C (ρ₀.character g) * X + 11 * X ^ 2) *
      (1 - C (ρ₁.character g) * X + 11 * X ^ 2) =
        primeFiveNumericalPolynomial11 L := by
  let g := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) P.asIdeal Q
  let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 0)).toRepresentation.dual
  let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 1)).toRepresentation.dual
  let b₀ := (exists_primePlusNativeDualFactorBasis 5
    selectedRMProductFiveLowerBound primeFiveParameter 5 L hL (labels 0)).some
  let b₁ := (exists_primePlusNativeDualFactorBasis 5
    selectedRMProductFiveLowerBound primeFiveParameter 5 L hL (labels 1)).some
  have hpoly := by
    with_reducible
      exact primeFiveSelectedRM_numericFactors11 L hL labels P W hk Q h5P b₀ b₁
  have hc : (1 - C (ρ₀.character g) * X + C (11 : L) * X ^ 2) *
      (1 - C (ρ₁.character g) * X + C (11 : L) * X ^ 2) =
        primeFiveNumericalPolynomial11 L := by
    with_reducible
      exact characterFactors_of_quadraticProduct ρ₀ ρ₁ g 11
        (primeFiveNumericalPolynomial11 L) b₀ b₁ hpoly
  simpa only [map_ofNat] using hc


/-- At forty-one, the two *actual* native RM representation characters,
without any chosen matrix bases, factor the counted polynomial. -/
theorem primeFiveSelectedRM_characterPolynomial41
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L))
    (P : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 K₅ ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 K₅ ⧸ P.asIdeal) = 41)
    (Q : Ideal (𝓞 (AlgebraicClosure K₅)))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 K₅) ∉ P.asIdeal) :
    let g := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) P.asIdeal Q
    let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 0)).toRepresentation.dual
    let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 1)).toRepresentation.dual
    (1 - C (ρ₀.character g) * X + 41 * X ^ 2) *
      (1 - C (ρ₁.character g) * X + 41 * X ^ 2) =
        primeFiveNumericalPolynomial41 L := by
  let g := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) P.asIdeal Q
  let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 0)).toRepresentation.dual
  let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 1)).toRepresentation.dual
  let b₀ := (exists_primePlusNativeDualFactorBasis 5
    selectedRMProductFiveLowerBound primeFiveParameter 5 L hL (labels 0)).some
  let b₁ := (exists_primePlusNativeDualFactorBasis 5
    selectedRMProductFiveLowerBound primeFiveParameter 5 L hL (labels 1)).some
  have hpoly := by
    with_reducible
      exact primeFiveSelectedRM_numericFactors41 L hL labels P W hk Q h5P b₀ b₁
  have hc : (1 - C (ρ₀.character g) * X + C (41 : L) * X ^ 2) *
      (1 - C (ρ₁.character g) * X + C (41 : L) * X ^ 2) =
        primeFiveNumericalPolynomial41 L := by
    with_reducible
      exact characterFactors_of_quadraticProduct ρ₀ ρ₁ g 41
        (primeFiveNumericalPolynomial41 L) b₀ b₁ hpoly
  simpa only [map_ofNat] using hc


end HilbertModularity.Examples
