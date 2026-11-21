/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusRaynaudComplementCharacterQuotient

/-! # The actual complementary deep-cusp ordinary character -/

public noncomputable section

open AlgebraicGeometry HilbertModularity.Cyclotomic HilbertModularity.Hyperelliptic
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusDecompositionRationalModule
  primePlusDecompositionScalarTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

/-- At the rational complementary `p³` cusp, the selected plus Jacobian's
label-one ordinary quotient has the actual quadratic lower character. The
stable model and Darmon–Mestre Tate equivalence are both constructed on the
same selected family. -/
theorem exists_primePlusCubicDifferenceNormalizedDataLowerQuadratic
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A)) :
    ∃ d : PrimePlusNormalizedOrdinaryData p hp
        (darmonRationalParameter p ξ₀) 1 (Nat.coprime_one_left _),
      d.lowerCharacter = primePlusComplementQuadraticCharacter p hp := by
  let ξ := darmonRationalParameter p ξ₀
  let η := ProjectiveLine.complementParameter (realCyclotomicField p) ξ
  have hη : darmonRationalParameter p
      (ProjectiveLine.complementParameter ℚ ξ₀) = η :=
    darmonRationalParameter_complement p ξ₀
  let H : PrimePlusScaledStableModelData p hp η := by
    rw [← hη]
    exact PrimePlusScaledStableModelData.of_cubicDifference p hp ξ₀
      hξ hB hAB hdeep
  obtain ⟨e⟩ := nonempty_primePlusComplementNativeTateComparison p hp ξ
  exact exists_primePlusComplementNormalizedDataLowerQuadratic p hp ξ H e

/-- One fixed normalized ordinary basis at the actual complementary cusp. -/
noncomputable def primePlusRaynaudCubicDifferenceOrdinaryData
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A)) :
    PrimePlusNormalizedOrdinaryData p hp
      (darmonRationalParameter p ξ₀) 1 (Nat.coprime_one_left _) :=
  Classical.choose <|
    exists_primePlusCubicDifferenceNormalizedDataLowerQuadratic p hp ξ₀
      hξ hB hAB hdeep

/-- The lower character of that fixed basis is the exact
Darmon–Mestre quadratic twist. -/
theorem primePlusRaynaudCubicDifferenceOrdinaryData_lowerCharacter
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A)) :
    (primePlusRaynaudCubicDifferenceOrdinaryData p hp ξ₀
      hξ hB hAB hdeep).lowerCharacter =
        primePlusComplementQuadraticCharacter p hp :=
  Classical.choose_spec <|
    exists_primePlusCubicDifferenceNormalizedDataLowerQuadratic p hp ξ₀
      hξ hB hAB hdeep

end HilbertModularity.Hypergeometric
