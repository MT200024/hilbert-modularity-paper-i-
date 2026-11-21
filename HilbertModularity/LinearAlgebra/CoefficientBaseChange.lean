/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.CoefficientDecomposition

/-! # Transporting coefficient labels along splitting fields

An extension of splitting fields induces a bijection of coefficient embeddings.
Tensor extension carries each primitive coefficient idempotent to the idempotent
with the transported label. This makes the coefficient-labelled decomposition
of [TripathiGoswami] independent of an enlargement of its splitting field.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Classical

namespace Algebra.TensorProduct

variable (F K L L' : Type*) [Field F] [Field K] [Field L] [Field L']
  [Algebra F K] [Algebra F L] [Algebra F L']
  [FiniteDimensional F K] [Algebra.IsSeparable F K]
  (α : L →ₐ[F] L')
  (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
  (hL' : ∀ x : K, ((minpoly F x).map (algebraMap F L')).Splits)

include hL in
/-- Every coefficient embedding into an enlarged splitting field comes from a unique old label. -/
theorem embedding_comp_bijective :
    Function.Bijective (fun σ : K →ₐ[F] L => α.comp σ) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro σ τ h
    ext x
    exact α.injective (AlgHom.congr_fun h x)
  · have hs : ∀ x : K, ((minpoly F x).map (algebraMap F L')).Splits := by
      intro x
      have hm : α.toRingHom.comp (algebraMap F L) = algebraMap F L' := by
        ext r
        exact α.commutes r
      simpa only [Polynomial.map_map, hm] using (hL x).map α.toRingHom
    rw [AlgHom.card_of_splits F K L hL, AlgHom.card_of_splits F K L' hs]

/-- The canonical bijection of embedding labels under extension of splitting fields. -/
def embeddingBaseChangeEquiv : (K →ₐ[F] L) ≃ (K →ₐ[F] L') :=
  Equiv.ofBijective (fun σ => α.comp σ) (embedding_comp_bijective F K L L' α hL)

@[simp]
theorem embeddingBaseChangeEquiv_apply (σ : K →ₐ[F] L) :
    embeddingBaseChangeEquiv F K L L' α hL σ = α.comp σ := rfl

omit [Algebra.IsSeparable F K] [FiniteDimensional F K] in
/-- Evaluation of coefficient tensors commutes with extension of the splitting field. -/
theorem embeddingEvaluation_map (z : L ⊗[F] K) (σ : K →ₐ[F] L) :
    embeddingEvaluation F K L' (Algebra.TensorProduct.map α (AlgHom.id F K) z) (α.comp σ) =
      α (embeddingEvaluation F K L z σ) := by
  induction z using TensorProduct.inductionOn with
  | tmul l x => simp [embeddingEvaluation_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Scalar extension transports the primitive coefficient idempotent with its embedding label. -/
theorem map_embeddingIdempotent (σ : K →ₐ[F] L) :
    Algebra.TensorProduct.map α (AlgHom.id F K) (embeddingIdempotent F K L hL σ) =
      embeddingIdempotent F K L' hL' (α.comp σ) := by
  apply (embeddingEquiv F K L' hL').injective
  ext τ
  obtain ⟨τ, rfl⟩ := (embedding_comp_bijective F K L L' α hL).surjective τ
  change embeddingEvaluation F K L'
    (Algebra.TensorProduct.map α (AlgHom.id F K) (embeddingIdempotent F K L hL σ)) (α.comp τ) = _
  rw [embeddingEvaluation_map]
  change α (embeddingEquiv F K L hL (embeddingIdempotent F K L hL σ) τ) = _
  rw [embeddingEquiv_embeddingIdempotent, embeddingEquiv_embeddingIdempotent]
  by_cases h : τ = σ
  · subst τ
    simp
  · have hc : α.comp τ ≠ α.comp σ := fun he => h ((embedding_comp_bijective F K L L' α hL).injective he)
    simp [h, hc]

section SemilinearMaps

variable {V W : Type*} [AddCommGroup V] [Module L V]
  [Module (L ⊗[F] K) V] [IsScalarTower L (L ⊗[F] K) V]
  [AddCommGroup W] [Module L' W]
  [Module (L' ⊗[F] K) W] [IsScalarTower L' (L' ⊗[F] K) W]
  (f : V →ₛₗ[α.toRingHom] W)
  (hf : ∀ (z : L ⊗[F] K) (v : V),
    f (z • v) = Algebra.TensorProduct.map α (AlgHom.id F K) z • f v)

/-- A compatible semilinear map preserves coefficient summands with transported labels. -/
def coefficientSummandSemilinearMap (σ : K →ₐ[F] L) :
    coefficientSummand F K L V hL σ →ₛₗ[α.toRingHom]
      coefficientSummand F K L' W hL' (α.comp σ) :=
  (f.comp (coefficientSummand F K L V hL σ).subtype).codRestrict _ (by
    intro v
    rw [mem_coefficientSummand_iff, ← map_embeddingIdempotent F K L L' α hL hL']
    change Algebra.TensorProduct.map α (AlgHom.id F K) (embeddingIdempotent F K L hL σ) • f v = f v
    rw [← hf, (mem_coefficientSummand_iff F K L V hL σ v).mp v.property])

@[simp]
theorem coefficientSummandSemilinearMap_apply (σ : K →ₐ[F] L)
    (v : coefficientSummand F K L V hL σ) :
    (coefficientSummandSemilinearMap F K L L' α hL hL' f hf σ v : W) = f v := rfl

include hf in
/-- Coefficient decomposition is natural under compatible semilinear scalar extension. -/
theorem coefficientDecomposition_semilinear (v : V) (σ : K →ₐ[F] L) :
    coefficientSummandSemilinearMap F K L L' α hL hL' f hf σ
      (coefficientDecomposition F K L V hL v σ) =
        coefficientDecomposition F K L' W hL' (f v) (α.comp σ) := by
  apply Subtype.ext
  change f (embeddingIdempotent F K L hL σ • v) =
    embeddingIdempotent F K L' hL' (α.comp σ) • f v
  rw [hf, map_embeddingIdempotent]

end SemilinearMaps

section CoefficientAutomorphism

variable (τ : K ≃ₐ[F] K)

omit [Algebra.IsSeparable F K] [FiniteDimensional F K] in
/-- A coefficient-field automorphism acts on evaluations by precomposing the embedding label. -/
theorem embeddingEvaluation_map_coefficient (z : L ⊗[F] K) (σ : K →ₐ[F] L) :
    embeddingEvaluation F K L (Algebra.TensorProduct.map (AlgHom.id F L) τ.toAlgHom z) σ =
      embeddingEvaluation F K L z (σ.comp τ.toAlgHom) := by
  induction z using TensorProduct.inductionOn with
  | tmul l x => simp [embeddingEvaluation_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- A coefficient-field automorphism permutes the primitive coefficient idempotents. -/
theorem map_embeddingIdempotent_coefficient (σ : K →ₐ[F] L) :
    Algebra.TensorProduct.map (AlgHom.id F L) τ.toAlgHom (embeddingIdempotent F K L hL σ) =
      embeddingIdempotent F K L hL (σ.comp τ.symm.toAlgHom) := by
  apply (embeddingEquiv F K L hL).injective
  ext ν
  change embeddingEvaluation F K L
    (Algebra.TensorProduct.map (AlgHom.id F L) τ.toAlgHom (embeddingIdempotent F K L hL σ)) ν = _
  rw [embeddingEvaluation_map_coefficient]
  change embeddingEquiv F K L hL (embeddingIdempotent F K L hL σ) (ν.comp τ.toAlgHom) = _
  rw [embeddingEquiv_embeddingIdempotent, embeddingEquiv_embeddingIdempotent]
  have hi : ν.comp τ.toAlgHom = σ ↔ ν = σ.comp τ.symm.toAlgHom := by
    constructor
    · intro h
      ext x
      simpa using AlgHom.congr_fun h (τ.symm x)
    · intro h
      subst ν
      ext x
      simp
  by_cases h : ν.comp τ.toAlgHom = σ
  · rw [h, hi.mp h]
    simp
  · simp [h, mt hi.mpr h]

end CoefficientAutomorphism

end Algebra.TensorProduct
