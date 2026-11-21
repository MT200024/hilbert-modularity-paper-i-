/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficientTensor

/-! # Native completed Tate rank at every coefficient label

Every global multiplication-field embedding extends uniquely through the
actual ramified completion tensor isomorphism. Consequently every actual
labelled Tate summand, and every fibre of the same labelled family, has the
native completed-coefficient rank. This is the rank comparison in
[TripathiGoswami, coefficient-label lemma].
-/

@[expose] public noncomputable section
open CategoryTheory Algebra.TensorProduct HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj NumberField TensorProduct
namespace AlgebraicGeometry.GroupScheme
universe u
variable (p k : ℕ) [Fact p.Prime]
  (L : Type u) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]

/-- Every global coefficient label extends through the actual coefficient completion. -/
def localTateCoefficientExtension (σ : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] L) :
    RealPrimePowerCompletion p k →ₐ[ℚ_[p]] L :=
  (coefficientTensorEmbedding ℚ ℚ_[p] _ L σ).comp
    (realPrimePowerCompletionTensorEquiv p k).symm.toAlgHom

/-- Restricting the extension recovers the original global coefficient label. -/
@[simp] theorem localTateCoefficientLabel_extension
    (σ : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] L) :
    localTateCoefficientLabel p k L (localTateCoefficientExtension p k L σ) = σ := by
  apply AlgHom.ext
  intro f
  have h : (realPrimePowerCompletionTensorEquiv p k).symm
      (algebraMap _ (RealPrimePowerCompletion p k) f) = (1 : ℚ_[p]) ⊗ₜ[ℚ] f := by
    apply (realPrimePowerCompletionTensorEquiv p k).injective
    simp
  change coefficientTensorEmbedding ℚ ℚ_[p] _ L σ
    ((realPrimePowerCompletionTensorEquiv p k).symm
      (algebraMap _ (RealPrimePowerCompletion p k) f)) = σ f
  rw [h, coefficientTensorEmbedding_tmul, map_one, one_mul]

/-- A local coefficient embedding is uniquely determined by its global multiplication label. -/
@[simp] theorem localTateCoefficientExtension_label (τ : RealPrimePowerCompletion p k →ₐ[ℚ_[p]] L) :
    localTateCoefficientExtension p k L (localTateCoefficientLabel p k L τ) = τ := by
  apply AlgHom.ext
  intro c
  change coefficientTensorEmbedding ℚ ℚ_[p] _ L (localTateCoefficientLabel p k L τ)
      ((realPrimePowerCompletionTensorEquiv p k).symm c) = τ c
  rw [localTateCoefficientLabel_tensor]
  simp

/-- Local completion embeddings and global multiplication labels describe the same actual coefficients. -/
def localTateCoefficientEmbeddingEquiv :
    (RealPrimePowerCompletion p k →ₐ[ℚ_[p]] L) ≃
      (realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] L) where
  toFun := localTateCoefficientLabel p k L
  invFun := localTateCoefficientExtension p k L
  left_inv := localTateCoefficientExtension_label p k L
  right_inv := localTateCoefficientLabel_extension p k L

variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S)
  (φ : 𝓞 (realCyclotomicField (p ^ (k + 1))) →+* End A)
  (hL : ∀ a : realCyclotomicField (p ^ (k + 1)),
    ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

/-- Every actual global embedding-labelled Tate summand has the native completed-coefficient rank. -/
theorem finrank_labelledTateSummand_eq_localCoefficientTateRep_of_embedding
    (σ : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] L) :
    Module.finrank L (labelledTateSummand K (fiber K A x).X p
      (realCyclotomicField (p ^ (k + 1))) L hL
      (fiberPointsAction K (AlgebraicClosure K) A x _ φ) σ) =
        Module.finrank (RealPrimePowerCompletion p k) (localCoefficientTateRep K A x p k φ) := by
  rw [← localTateCoefficientLabel_extension p k L σ]
  exact finrank_labelledTateSummand_eq_localCoefficientTateRep p k L
      (localTateCoefficientExtension p k L σ) K A x φ hL

variable [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The actual arithmetic fibre at every global label has the native completed-coefficient rank. -/
theorem finrank_labelledTateLocalSystem_eq_localCoefficientTateRep_of_embedding
    (σ : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] L) :
    Module.finrank L ((labelledTateLocalSystem K A p L _ φ hL σ).obj
      (Scheme.etaleFiberPoint K S x)) =
        Module.finrank (RealPrimePowerCompletion p k) (localCoefficientTateRep K A x p k φ) := by
  rw [← localTateCoefficientLabel_extension p k L σ]
  exact finrank_labelledTateLocalSystem_eq_localCoefficientTateRep p k L
      (localTateCoefficientExtension p k L σ) K A x φ hL

end AlgebraicGeometry.GroupScheme
