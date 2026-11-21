/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusRaynaudComplementQuotient
public import HilbertModularity.Hypergeometric.PrimePlusRaynaudLocalOrdinary
public import HilbertModularity.Geometry.GroupScheme.PrimePlusComplementDeepCusp

/-! # The specified quadratic quotient at the complementary cusp -/

public noncomputable section

open AlgebraicGeometry HilbertModularity.Cyclotomic HilbertModularity.Hyperelliptic
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusDecompositionRationalModule
  primePlusDecompositionScalarTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- The stable model at `1 - ξ` and the finite quadratic Tate comparison
supply a normalized basis on the original selected fibre. Its lower character
is the actual Darmon–Mestre quadratic character. -/
theorem exists_primePlusComplementNormalizedDataLowerQuadratic
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (H : PrimePlusScaledStableModelData p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ))
    (e : (((Representation.ofCharacter (primePlusComplementQuadraticCharacter p hp)).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ).Equiv
      (primePlusDecompositionRepresentation p hp ξ).ρ)) :
    ∃ d : PrimePlusNormalizedOrdinaryData p hp ξ 1
        (Nat.coprime_one_left _),
      d.lowerCharacter = primePlusComplementQuadraticCharacter p hp := by
  obtain ⟨W, hW⟩ := exists_primePlusBaseOrdinaryQuotient_of_complementTwist
    p hp ξ H (primePlusComplementQuadraticCharacter p hp)
    (primePlusComplementQuadraticCharacter_continuous p hp)
    (primePlusComplementQuadraticCharacter_isOfFinOrder p hp) e
  exact exists_primePlusLabelOneNormalizedData_with_character p hp ξ
    (primePlusComplementQuadraticCharacter p hp) W hW

end HilbertModularity.Hypergeometric
