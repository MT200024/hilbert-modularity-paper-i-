/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.CoefficientDecomposition
public import HilbertModularity.RepresentationTheory.CoefficientDual

/-! # Coefficient-labelled dual Tate factors

The dual of a labelled geometric Tate factor is canonically the image of the
same coefficient idempotent acting by transpose on the full Tate dual. Thus
endomorphism dualization preserves its embedding label. The Galois action is
contragredient. This realizes the dual-factor construction in
[TripathiGoswami]; no etale-cohomology comparison is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
  (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
  (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    φ a = pointsMap K (AlgebraicClosure K) f)

/-- A coefficient projector is an equivariant endomorphism of the extended Tate representation. -/
def labelledTateProjectorIntertwiner (σ : F →ₐ[ℚ] L) :
    ((tateRepresentation K A p).baseChange L).IntertwiningMap
      ((tateRepresentation K A p).baseChange L) where
  toLinearMap := labelledTateProjection K A p F L hL φ σ
  isIntertwining' g := tensorTateAction_commute K A p F L φ hφ g (embeddingIdempotent ℚ F L hL σ)

/-- The same coefficient projector, transposed, cuts out a stable summand of the Tate dual. -/
def labelledDualTateSubrepresentation (σ : F →ₐ[ℚ] L) :
    Subrepresentation ((tateRepresentation K A p).baseChange L).dual :=
  (labelledTateProjectorIntertwiner K A p F L hL φ hφ σ).dual.range

/-- The cohomological convention takes the contragredient of the labelled covariant factor. -/
def labelledDualTateFactor (σ : F →ₐ[ℚ] L) :
    Representation L (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (Module.Dual L (labelledTateSummand K A p F L hL φ σ)) :=
  (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation.dual

/-- Projection by the same label on the full dual is the dual of the labelled Tate factor. -/
def labelledDualTateEquiv (σ : F →ₐ[ℚ] L) :
    (labelledDualTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation.Equiv
      (labelledDualTateFactor K A p F L hL φ hφ σ) :=
  (labelledTateProjectorIntertwiner K A p F L hL φ hφ σ).dualRangeEquiv
    ((completeOrthogonalIdempotents_labelledTateProjection K A p F L hL φ).idem σ)

@[simp]
theorem labelledDualTateEquiv_apply (σ : F →ₐ[ℚ] L)
    (f : labelledDualTateSubrepresentation K A p F L hL φ hφ σ)
    (v : labelledTateSummand K A p F L hL φ σ) :
    labelledDualTateEquiv K A p F L hL φ hφ σ f v =
      (f : Module.Dual L (L ⊗[ℚ_[p]] rationalTate K A p)) v := rfl

/-- Transposing coefficient endomorphisms preserves the label, without inversion of its value. -/
theorem dualTateAction_labelled (σ : F →ₐ[ℚ] L) (z : L ⊗[ℚ] F)
    (f : labelledDualTateSubrepresentation K A p F L hL φ hφ σ) :
    AlgHom.dualEndomorphism (tensorTateAction K A p F L φ) z f =
      embeddingEquiv ℚ F L hL z σ • (f : Module.Dual L (L ⊗[ℚ_[p]] rationalTate K A p)) := by
  obtain ⟨ψ, hψ⟩ := f.property
  change (labelledTateProjection K A p F L hL φ σ).dualMap ψ =
    (f : Module.Dual L (L ⊗[ℚ_[p]] rationalTate K A p)) at hψ
  rw [← hψ]
  apply LinearMap.ext
  intro v
  change ψ ((tensorTateAction K A p F L φ (embeddingIdempotent ℚ F L hL σ) *
    tensorTateAction K A p F L φ z) v) = _
  rw [← map_mul, mul_comm (embeddingIdempotent ℚ F L hL σ) z,
    mul_embeddingIdempotent, map_smul]
  exact ψ.map_smul _ _

/-- Transposed coefficient projectors remain a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_labelledDualTateProjection :
    CompleteOrthogonalIdempotents
      (fun σ => (labelledTateProjection K A p F L hL φ σ).dualMap) :=
  (completeOrthogonalIdempotents_embeddingIdempotent ℚ F L hL).map
    (AlgHom.dualEndomorphism (tensorTateAction K A p F L φ)).toRingHom

/-- The full geometric Tate dual decomposes equivariantly into duals of the same labelled factors. -/
def labelledDualTateDecompositionEquiv :
    ((tateRepresentation K A p).baseChange L).dual.Equiv
      (Representation.pi fun σ => labelledDualTateFactor K A p F L hL φ hφ σ) := by
  let e : ((tateRepresentation K A p).baseChange L).dual.Equiv
      (Representation.pi fun σ =>
        (labelledDualTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation) :=
    .mk (completeOrthogonalIdempotents_labelledDualTateProjection K A p F L hL φ).linearEquiv (by
      intro g
      apply LinearMap.ext
      intro f
      funext σ
      apply Subtype.ext
      exact LinearMap.congr_fun
        ((labelledTateProjectorIntertwiner K A p F L hL φ hφ σ).dual.isIntertwining' g) f)
  exact e.trans (Representation.Equiv.pi fun σ => labelledDualTateEquiv K A p F L hL φ hφ σ)

section Naturality

variable {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsCommMonObj B]
  (ψ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) B))
  (hψ : ∀ a, ∃ (f : B ⟶ B) (_ : IsMonHom f),
    ψ a = pointsMap K (AlgebraicClosure K) f)
  (f : A ⟶ B) [IsMonHom f]
  (h : ∀ (a : 𝓞 F) (x : Points K (AlgebraicClosure K) A),
    pointsMap K (AlgebraicClosure K) f (φ a x) = ψ a (pointsMap K (AlgebraicClosure K) f x))

/-- Geometric coefficient-compatible maps act contravariantly on the same labelled dual factors. -/
def labelledDualTateIntertwiningMap (σ : F →ₐ[ℚ] L) :
    (labelledDualTateFactor K B p F L hL ψ hψ σ).IntertwiningMap
      (labelledDualTateFactor K A p F L hL φ hφ σ) := by
  unfold labelledDualTateFactor
  exact (labelledTateIntertwiningMap K A p F L hL φ hφ ψ f h hψ σ).dual

@[simp]
theorem labelledDualTateIntertwiningMap_apply (σ : F →ₐ[ℚ] L)
    (ell : Module.Dual L (labelledTateSummand K B p F L hL ψ σ))
    (v : labelledTateSummand K A p F L hL φ σ) :
    labelledDualTateIntertwiningMap K A p F L hL φ hφ ψ hψ f h σ ell v =
      ell (labelledTateSummandMap K A p F L hL φ ψ f h σ v) := rfl

end Naturality

end AlgebraicGeometry.GroupScheme
