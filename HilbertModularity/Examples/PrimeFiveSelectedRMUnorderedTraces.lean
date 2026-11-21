/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveNativeFrobeniusTransport
public import HilbertModularity.Examples.PrimeFiveAlgebraicRoots

/-! # The actual selected RM trace pairs at both worked primes -/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain Polynomial
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

local instance unorderedSelectedFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local notation "K₅" => realCyclotomicField 5
local notation "J₅" => primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter

/-- The two native factors of the selected Jacobian at the actual eleven and
forty-one primes have exactly the manuscript's unordered conjugate traces.
The element `s` is the image of the fixed fifth-cyclotomic real trace
parameter; its oriented complex image is `(√5−1)/2`. -/
theorem primeFive_selectedRM_unorderedTracePairs
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[5] L]
    [Algebra ℚ L] [Algebra (cyclotomicField 5) L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L))
    (q₁₁ : HeightOneSpectrum (𝓞 K₅))
    (W₁₁ : PrimeFiveSelectedSpecialJacobian q₁₁)
    [Fintype (𝓞 K₅ ⧸ q₁₁.asIdeal)]
    (hk₁₁ : Fintype.card (𝓞 K₅ ⧸ q₁₁.asIdeal) = 11)
    (P₁₁ : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P₁₁.asIdeal.LiesOver q₁₁.asIdeal]
    (Q₁₁ : Ideal (𝓞 Qbar)) [Q₁₁.IsMaximal] [Q₁₁.LiesOver P₁₁.asIdeal]
    (hcard₁₁ : Nat.card (𝓞 (cyclotomicField 5) ⧸ P₁₁.asIdeal) =
      Nat.card (𝓞 K₅ ⧸ q₁₁.asIdeal))
    (h5q₁₁ : (5 : 𝓞 K₅) ∉ q₁₁.asIdeal)
    (q₄₁ : HeightOneSpectrum (𝓞 K₅))
    (W₄₁ : PrimeFiveSelectedSpecialJacobian q₄₁)
    [Fintype (𝓞 K₅ ⧸ q₄₁.asIdeal)]
    (hk₄₁ : Fintype.card (𝓞 K₅ ⧸ q₄₁.asIdeal) = 41)
    (P₄₁ : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P₄₁.asIdeal.LiesOver q₄₁.asIdeal]
    (Q₄₁ : Ideal (𝓞 Qbar)) [Q₄₁.IsMaximal] [Q₄₁.LiesOver P₄₁.asIdeal]
    (hcard₄₁ : Nat.card (𝓞 (cyclotomicField 5) ⧸ P₄₁.asIdeal) =
      Nat.card (𝓞 K₅ ⧸ q₄₁.asIdeal))
    (h5q₄₁ : (5 : 𝓞 K₅) ∉ q₄₁.asIdeal) :
    let s : L := algebraMap (cyclotomicField 5) L
      (realEulerCoefficientInclusion 5 (tau 5 1))
    let g₁₁ := primeFiveRealFrobenius P₁₁ Q₁₁
    let g₄₁ := primeFiveRealFrobenius P₄₁ Q₄₁
    let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 0)).toRepresentation.dual
    let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 1)).toRepresentation.dual
    ((ρ₀.character g₁₁ = s ∧ ρ₁.character g₁₁ = -1 - s) ∨
      (ρ₀.character g₁₁ = -1 - s ∧ ρ₁.character g₁₁ = s)) ∧
    ((ρ₀.character g₄₁ = -3 - 5 * s ∧ ρ₁.character g₄₁ = 2 + 5 * s) ∨
      (ρ₀.character g₄₁ = 2 + 5 * s ∧ ρ₁.character g₄₁ = -3 - 5 * s)) := by
  let : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  let s : L := algebraMap (cyclotomicField 5) L
    (realEulerCoefficientInclusion 5 (tau 5 1))
  let g₁₁ := primeFiveRealFrobenius P₁₁ Q₁₁
  let g₄₁ := primeFiveRealFrobenius P₄₁ Q₄₁
  let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 0)).toRepresentation.dual
  let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 1)).toRepresentation.dual
  have hs : s ^ 2 + s = 1 := by
    have h := congrArg (algebraMap (cyclotomicField 5) L)
      primeFive_fullTau_quadratic
    simpa only [s, map_add, map_pow, map_one] using h
  have hpoly₁₁ : (1 - C (ρ₀.character g₁₁) * X + 11 * X ^ 2) *
      (1 - C (ρ₁.character g₁₁) * X + 11 * X ^ 2) =
        primeFiveNumericalPolynomial11 L := by
    with_reducible
      exact primeFive_orientedRMCharacterPolynomial11 L hL labels
        q₁₁ W₁₁ hk₁₁ P₁₁ Q₁₁ hcard₁₁ h5q₁₁
  have hpoly₄₁ : (1 - C (ρ₀.character g₄₁) * X + 41 * X ^ 2) *
      (1 - C (ρ₁.character g₄₁) * X + 41 * X ^ 2) =
        primeFiveNumericalPolynomial41 L := by
    with_reducible
      exact primeFive_orientedRMCharacterPolynomial41 L hL labels
        q₄₁ W₄₁ hk₄₁ P₄₁ Q₄₁ hcard₄₁ h5q₄₁
  have hpolyLit₁₁ : (1 - C (ρ₀.character g₁₁) * X + 11 * X ^ 2) *
      (1 - C (ρ₁.character g₁₁) * X + 11 * X ^ 2) =
        (1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 : L[X]) :=
    hpoly₁₁.trans (primeFiveNumericalPolynomial11_formula L)
  have hpolyLit₄₁ : (1 - C (ρ₀.character g₄₁) * X + 41 * X ^ 2) *
      (1 - C (ρ₁.character g₄₁) * X + 41 * X ^ 2) =
        (1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 : L[X]) :=
    hpoly₄₁.trans (primeFiveNumericalPolynomial41_formula L)
  exact ⟨unorderedTracePair11_of_quadraticParameter
      s (ρ₀.character g₁₁) (ρ₁.character g₁₁) hs hpolyLit₁₁,
    unorderedTracePair41_of_quadraticParameter
      s (ρ₀.character g₄₁) (ρ₁.character g₄₁) hs hpolyLit₄₁⟩

end HilbertModularity.Examples
