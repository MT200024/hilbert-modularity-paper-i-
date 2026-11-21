/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.CoefficientDual
public import HilbertModularity.NumberTheory.AbsoluteFrobenius

/-! # Determinant of a labelled cohomological Frobenius factor

A covariant labelled Tate factor with exact cyclotomic determinant has
determinant equal to the residue cardinality on the cohomological dual at
geometric Frobenius. This is the convention used by the worked polynomial.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open GroupScheme

attribute [local instance] Ideal.Quotient.field

/-- Geometric Frobenius on a cohomological dual has determinant q whenever
the original covariant representation has cyclotomic determinant. -/
theorem dualFrobenius_det_of_cyclotomic
    (K : Type*) [Field K] [NumberField K]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type*) [NormedField L] [NormedAlgebra ℚ_[ℓ] L]
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) V)
    (hdet : ∀ g, LinearMap.det (ρ g) =
      (Field.cyclotomicCharacterWithCoefficients K ℓ L g : L))
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P]
    (hℓP : (ℓ : 𝓞 K) ∉ P) :
    LinearMap.det (ρ.dual
      (NumberField.geometricFrobenius K (AlgebraicClosure K) P Q)) =
        (Nat.card (𝓞 K ⧸ P) : L) := by
  let g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    NumberField.geometricFrobenius K (AlgebraicClosure K) P Q
  change LinearMap.det ((ρ g⁻¹).dualMap) = _
  rw [LinearMap.det_dualMap, hdet]
  have hc := Field.cyclotomicCharacterWithCoefficients_geometricFrobenius_apply
    K ℓ L P Q hℓP
  simp only [map_inv, Units.val_inv_eq_inv_val]
  dsimp only [g]
  rw [hc, inv_inv]

/-- The dual of an exact-cyclotomic labelled factor has determinant q at
geometric Galois Frobenius. The covariant determinant is a genuine input from
the selected abelian variety's RM pairing. -/
theorem labelledDualTateFactor_det_geometricFrobenius
    (K : Type*) [Field K] [NumberField K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type*) [Field F] [NumberField F]
    (L : Type*) [NormedField L] [NormedAlgebra ℚ_[ℓ] L] [Algebra ℚ L]
    (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
    (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
      φ a = pointsMap K (AlgebraicClosure K) f)
    (σ : F →ₐ[ℚ] L)
    [Module.Finite L (labelledTateSummand K A ℓ F L hL φ σ)]
    (hdet : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      LinearMap.det (A := L)
        (M := (labelledTateSubrepresentation K A ℓ F L hL φ hφ σ).toSubmodule)
        ((labelledTateSubrepresentation K A ℓ F L hL φ hφ σ).toRepresentation g) =
          (Field.cyclotomicCharacterWithCoefficients K ℓ L g : L))
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P]
    (hℓP : (ℓ : 𝓞 K) ∉ P) :
    LinearMap.det (labelledDualTateFactor K A ℓ F L hL φ hφ σ
      (NumberField.geometricFrobenius K (AlgebraicClosure K) P Q)) =
        (Nat.card (𝓞 K ⧸ P) : L) := by
  let : FiniteDimensional L
      (labelledTateSubrepresentation K A ℓ F L hL φ hφ σ).toSubmodule := by
    change Module.Finite L (labelledTateSummand K A ℓ F L hL φ σ)
    infer_instance
  exact dualFrobenius_det_of_cyclotomic K ℓ L
    (V := (labelledTateSubrepresentation K A ℓ F L hL φ hφ σ).toSubmodule)
    (labelledTateSubrepresentation K A ℓ F L hL φ hφ σ).toRepresentation
    hdet P Q hℓP

end HilbertModularity.Examples
