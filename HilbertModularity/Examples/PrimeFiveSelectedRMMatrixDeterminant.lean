/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedRMDeterminant

/-! # Native RM dual Frobenius determinant in a chosen basis

The basis is fixed before the selected conductor and parameter are inserted.
This is the matrix form of the proved exact pairing determinant.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

/-- In every basis of an actual plus-family native dual factor, the matrix
determinant at geometric Frobenius is the residue cardinality. -/
theorem primePlusLabelledDual_matrix_det_geometricFrobenius
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L)
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (b : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate (realCyclotomicField p)
        (primePlusFiber p hp ξ) ℓ (realCyclotomicField p) L hL
        (primePlusFiberRealMultiplication p hp ξ) σ).toSubmodule)) :
    (LinearMap.toMatrix b b
      ((endomorphismLabelledTate (realCyclotomicField p)
        (primePlusFiber p hp ξ) ℓ (realCyclotomicField p) L hL
        (primePlusFiberRealMultiplication p hp ξ) σ).toRepresentation.dual
        (NumberField.geometricFrobenius (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q))).det =
      (Nat.card (𝓞 (realCyclotomicField p) ⧸ P.asIdeal) : L) := by
  simpa only [LinearMap.det_toMatrix] using
    (primePlusLabelledDual_det_geometricFrobenius
      p hp ξ ℓ L hL σ P Q hℓP)

end HilbertModularity.Examples
