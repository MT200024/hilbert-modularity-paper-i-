/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveRMDualDeterminant
public import HilbertModularity.Geometry.GroupScheme.PrimeLabelledDeterminant

/-! # Determinants of actual selected RM dual factors

The relative RM pairing gives the cyclotomic determinant on each actual
covariant factor. Duality evaluates it as the residue cardinality at
geometric Frobenius, with the original real-multiplication label.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open HilbertModularity.Cyclotomic Hypergeometric GroupScheme

/-- Every labelled cohomological factor of the actual plus Jacobian has
determinant equal to the residue cardinality at geometric Frobenius. -/
theorem primePlusLabelledDual_det_geometricFrobenius
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
    (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal) :
    LinearMap.det
      ((endomorphismLabelledTate (realCyclotomicField p)
        (primePlusFiber p hp ξ) ℓ (realCyclotomicField p) L hL
        (primePlusFiberRealMultiplication p hp ξ) σ).toRepresentation.dual
        (NumberField.geometricFrobenius (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q)) =
      (Nat.card (𝓞 (realCyclotomicField p) ⧸ P.asIdeal) : L) := by
  let V := (endomorphismLabelledTate (realCyclotomicField p)
    (primePlusFiber p hp ξ) ℓ (realCyclotomicField p) L hL
    (primePlusFiberRealMultiplication p hp ξ) σ).toSubmodule
  let : FiniteDimensional L V := by infer_instance
  let ρ := (endomorphismLabelledTate (realCyclotomicField p)
    (primePlusFiber p hp ξ) ℓ (realCyclotomicField p) L hL
    (primePlusFiberRealMultiplication p hp ξ) σ).toRepresentation
  have hdet : ∀ g, LinearMap.det (A := L) (M := V) (ρ g) =
      (Field.cyclotomicCharacterWithCoefficients
        (realCyclotomicField p) ℓ L g : L) := by
    intro g
    exact primePlusFiber_labelled_det p hp ξ ℓ L hL σ g
  with_reducible
    exact dualFrobenius_det_of_cyclotomic (V := V)
      (realCyclotomicField p) ℓ L ρ hdet
      P.asIdeal Q hℓP

end HilbertModularity.Examples
