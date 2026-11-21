/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeFiberDeterminant
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricResidual

/-! # Covariant labelled Frobenius determinants

The determinant assertion in [TripathiGoswamiRevised,
Lemma `labelled-RM-compat`] concerns the covariant Tate factor. The existing
relative pairing proves its determinant is exactly cyclotomic, so the ratio
is one at every permissible geometric Frobenius.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- The relative pairing computes the determinant of the selected Jacobian's
actual labelled Tate factor, at every auxiliary prime and coefficient label. -/
theorem primePlusFiber_labelled_det
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L)
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p)) :
    (LinearMap.det (A := L)
      (M := (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toSubmodule))
      ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toRepresentation g) =
      (Field.cyclotomicCharacterWithCoefficients (realCyclotomicField p) ℓ L g : L) := by
  have h := primePlusFiberTateFactor_det p hp ℓ L hL σ
    (realCyclotomicField p) (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) g
  unfold primePlusFiberTateFactor endomorphismLabelledTate at h
  unfold endomorphismLabelledTate primePlusFiberRealMultiplication primePlusFiber parameterFiber
  with_reducible exact h

/-- The covariant determinant divided by the ordinary cyclotomic character
is exactly one. This implies the final compatibility assertion of
[TripathiGoswamiRevised, Lemma `labelled-RM-compat`] for the selected fibre. -/
theorem primePlusFiber_labelled_det_div_cyclotomic
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L)
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p)) :
    (LinearMap.det (A := L)
      (M := (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toSubmodule))
      ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toRepresentation g) /
      (Field.cyclotomicCharacterWithCoefficients (realCyclotomicField p) ℓ L g : L) = 1 := by
  rw [primePlusFiber_labelled_det p hp ξ ℓ L hL σ g]
  exact div_self (Units.ne_zero _)

end HilbertModularity.Hypergeometric
