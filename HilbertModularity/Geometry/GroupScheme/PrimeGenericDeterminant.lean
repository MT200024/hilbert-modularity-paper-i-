/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusRMComparison
public import HilbertModularity.Geometry.TateModule.RealMultiplicationPairing

/-! # The generic determinant of the selected plus Jacobian

The full generic endomorphism calculation and the polarized Tate pairing apply
to the same selected Jacobian and the same integral action. Consequently every
rank-two labelled generic factor has cyclotomic determinant, without identifying
its label with a separately chosen Darmon--Mestre correspondence.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ℓ : ℕ) [Fact ℓ.Prime]
  (L : Type) [NormedField L] [NormedAlgebra ℚ_[ℓ] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[ℓ] L]
  (hL : ∀ x : realCyclotomicField p,
    ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (σ : realCyclotomicField p →ₐ[ℚ] L)

/-- The native generic factor of the selected plus Jacobian, with its original
integral action and the specified coefficient embedding. -/
@[expose] def primePlusGenericTateFactor :=
  endomorphismLabelledTate (RatFunc (realCyclotomicField p))
    (fiber (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)))
    ℓ (realCyclotomicField p) L hL
    ((primePlusGenericEndMap p hp).comp (primePlusRealMultiplication p hp)) σ

attribute [irreducible] primePlusGenericTateFactor

/-- Fullness is established at the generic point; no claim about the full
endomorphism rings of rational specializations enters this application. -/
theorem primePlusGenericTateFactor_hasPairing
    (hreal : NumberField.IsTotallyReal (realCyclotomicField p)) :
    ∃ B : (primePlusGenericTateFactor p hp ℓ L hL σ).toSubmodule →ₗ[L]
        Module.Dual L (primePlusGenericTateFactor p hp ℓ L hL σ).toSubmodule,
      (∀ v, B v v = 0) ∧
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      ∀ g v w,
        B ((primePlusGenericTateFactor p hp ℓ L hL σ).toRepresentation g v)
          ((primePlusGenericTateFactor p hp ℓ L hL σ).toRepresentation g w) =
        (Field.cyclotomicCharacterWithCoefficients
          (RatFunc (realCyclotomicField p)) ℓ L g : L) * B v w := by
  let : Smooth (primePlusFamily p hp).X.hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℚ (realCyclotomicField p)) _
  unfold primePlusGenericTateFactor
  with_reducible
    exact exists_labelledTatePairing_of_full_realMultiplication _ _ ℓ
      (realCyclotomicField p) L hL _ hreal (primePlusGenericRMAction_bijective p hp) σ

end HilbertModularity.Hypergeometric
