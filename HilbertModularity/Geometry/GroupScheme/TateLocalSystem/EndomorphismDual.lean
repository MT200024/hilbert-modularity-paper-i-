/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientDualTopology
public import HilbertModularity.Geometry.TateModule.RealMultiplicationPairing

/-! # Endomorphism-labelled arithmetic cohomological fibres -/

public noncomputable section

open CategoryTheory
open scoped NumberField

namespace AlgebraicGeometry.GroupScheme

/-- Arithmetic specialization of the cohomological local system, expressed using
endomorphisms of the same group-scheme fibre. -/
def endomorphismLabelledCohomologicalArithmeticEquiv
    (K : Type) [Field K] [CharZero K] {S : Scheme}
    (A : CommGrp (Over S)) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ n : ℕ, IsFinite (ℓ ^ n • 𝟙 A).hom.hom.hom.left]
    [∀ n : ℕ, Etale (ℓ ^ n • 𝟙 A).hom.hom.hom.left]
    [Surjective (ℓ • 𝟙 A).hom.hom.hom.left]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (F : Type) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (x : Spec (CommRingCat.of K) ⟶ S) (σ : F →ₐ[ℚ] L) :
    ((labelledCohomologicalTateEtaleLocalSystem K A ℓ L F φ hL σ).arithmeticRepresentation x).Equiv
      ((endomorphismLabelledTate K (fiber K A x) ℓ F L hL
        ((fiberEndomorphismMap K A x).comp φ) σ).toRepresentation.dual) := by
  unfold endomorphismLabelledTate
  exact labelledCohomologicalTateEtaleLocalSystemArithmeticEquiv K A ℓ L F φ hL x σ

end AlgebraicGeometry.GroupScheme
