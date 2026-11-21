/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveRMEmbeddingOrder
public import HilbertModularity.Geometry.TateModule.CoefficientDual

/-! # The dual Tate polynomial and the actual RM projectors

The project's coefficient projectors split the full dual Tate representation
of one abelian variety. With an explicit ordering of the two embeddings, the
full Frobenius polynomial is the product of those actual dual factors.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open GroupScheme

/-- The full scalar-extended dual Tate polynomial is the product of the
two actual coefficient-idempotent factors. The order is the supplied
embedding order, and no factor trace or determinant is assumed here. -/
theorem labelledDualTate_charpolyRev_two
    (K : Type*) [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type*) [Field F] [NumberField F]
    (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
    (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
      φ a = pointsMap K (AlgebraicClosure K) f)
    [FiniteDimensional L (L ⊗[ℚ_[ℓ]] rationalTate K A ℓ)]
    (labels : Fin 2 ≃ (F →ₐ[ℚ] L))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (b : Module.Basis (Fin 4) L
      (Module.Dual L (L ⊗[ℚ_[ℓ]] rationalTate K A ℓ)))
    (b₀ : Module.Basis (Fin 2) L
      (Module.Dual L (labelledTateSummand K A ℓ F L hL φ (labels 0))))
    (b₁ : Module.Basis (Fin 2) L
      (Module.Dual L (labelledTateSummand K A ℓ F L hL φ (labels 1)))) :
    (LinearMap.toMatrix b b (((tateRepresentation K A ℓ).baseChange L).dual g)).charpolyRev =
      (LinearMap.toMatrix b₀ b₀
        (labelledDualTateFactor K A ℓ F L hL φ hφ (labels 0) g)).charpolyRev *
        (LinearMap.toMatrix b₁ b₁
          (labelledDualTateFactor K A ℓ F L hL φ hφ (labels 1) g)).charpolyRev := by
  exact charpolyRev_of_two_factorRepresentation
    (fun σ => Module.Dual L (labelledTateSummand K A ℓ F L hL φ σ))
    ((tateRepresentation K A ℓ).baseChange L).dual
    (fun σ => labelledDualTateFactor K A ℓ F L hL φ hφ σ)
    (labelledDualTateDecompositionEquiv K A ℓ F L hL φ hφ)
    labels g b b₀ b₁

end HilbertModularity.Examples
