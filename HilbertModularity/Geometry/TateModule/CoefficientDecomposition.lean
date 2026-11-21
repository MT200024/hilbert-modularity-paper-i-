/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.CoefficientAction
public import HilbertModularity.RepresentationTheory.CoefficientDecomposition

/-! # Labelled summands of geometric Tate modules

The primitive idempotents of a split coefficient field act on the extended
geometric Tate module through its coefficient action. Their images are stable
under Galois and decompose the full representation. This constructs the labelled
factors of [TripathiGoswami, coefficient-label lemma] for any given geometric
integer coefficient action; it does not assert existence or rank of the Darmon
real multiplication action.
-/

@[expose] public noncomputable section

open CategoryTheory Algebra.TensorProduct Classical
open scoped CategoryTheory.MonObj TensorProduct NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
  (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))

/-- The coefficient idempotent for an embedding acts on the actual extended Tate module. -/
def labelledTateProjection (σ : F →ₐ[ℚ] L) :
    Module.End L (L ⊗[ℚ_[p]] rationalTate K A p) :=
  tensorTateAction K A p F L φ (embeddingIdempotent ℚ F L hL σ)

/-- The coefficient projections on the Tate module are complete and orthogonal. -/
theorem completeOrthogonalIdempotents_labelledTateProjection :
    CompleteOrthogonalIdempotents (labelledTateProjection K A p F L hL φ) :=
  (completeOrthogonalIdempotents_embeddingIdempotent ℚ F L hL).map
    (tensorTateAction K A p F L φ).toRingHom

/-- The underlying labelled Tate summand is the image of its coefficient projector. -/
def labelledTateSummand (σ : F →ₐ[ℚ] L) :
    Submodule L (L ⊗[ℚ_[p]] rationalTate K A p) :=
  LinearMap.range (labelledTateProjection K A p F L hL φ σ)

/-- The simultaneous coefficient projections decompose the extended Tate module. -/
def labelledTateDecomposition :
    (L ⊗[ℚ_[p]] rationalTate K A p) ≃ₗ[L]
      ((σ : F →ₐ[ℚ] L) → labelledTateSummand K A p F L hL φ σ) :=
  (completeOrthogonalIdempotents_labelledTateProjection K A p F L hL φ).linearEquiv

/-- The labelled Tate summands form an internal direct sum. -/
theorem isInternal_labelledTateSummand :
    DirectSum.IsInternal (labelledTateSummand K A p F L hL φ) :=
  (completeOrthogonalIdempotents_labelledTateProjection K A p F L hL φ).isInternal

@[simp]
theorem labelledTateDecomposition_apply (v : L ⊗[ℚ_[p]] rationalTate K A p)
    (σ : F →ₐ[ℚ] L) :
    (labelledTateDecomposition K A p F L hL φ v σ : L ⊗[ℚ_[p]] rationalTate K A p) =
      labelledTateProjection K A p F L hL φ σ v := rfl

@[simp]
theorem labelledTateDecomposition_symm_apply
    (v : (σ : F →ₐ[ℚ] L) → labelledTateSummand K A p F L hL φ σ) :
    (labelledTateDecomposition K A p F L hL φ).symm v = ∑ σ, (v σ : L ⊗[ℚ_[p]] rationalTate K A p) := rfl

/-- The full coefficient algebra acts on a labelled Tate summand through its label. -/
theorem tensorTateAction_labelledTateSummand (σ : F →ₐ[ℚ] L)
    (z : L ⊗[ℚ] F) (v : labelledTateSummand K A p F L hL φ σ) :
    tensorTateAction K A p F L φ z v = (embeddingEquiv ℚ F L hL z σ) •
      (v : L ⊗[ℚ_[p]] rationalTate K A p) := by
  obtain ⟨w, hw⟩ := v.property
  change tensorTateAction K A p F L φ (embeddingIdempotent ℚ F L hL σ) w =
    (v : L ⊗[ℚ_[p]] rationalTate K A p) at hw
  rw [← hw]
  change (tensorTateAction K A p F L φ z *
    tensorTateAction K A p F L φ (embeddingIdempotent ℚ F L hL σ)) w = _
  rw [← map_mul, mul_embeddingIdempotent, map_smul]
  rfl

/-- An element of the coefficient number field acts by the selected embedding. -/
theorem numberField_labelledTateSummand (σ : F →ₐ[ℚ] L) (x : F)
    (v : labelledTateSummand K A p F L hL φ σ) :
    tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] x) v =
      σ x • (v : L ⊗[ℚ_[p]] rationalTate K A p) := by
  rw [tensorTateAction_labelledTateSummand, embeddingEquiv_tmul, one_mul]

variable (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
  φ a = pointsMap K (AlgebraicClosure K) f)

/-- Every labelled geometric Tate summand is stable under the absolute Galois action. -/
def labelledTateSubrepresentation (σ : F →ₐ[ℚ] L) :
    Subrepresentation ((tateRepresentation K A p).baseChange L) where
  toSubmodule := labelledTateSummand K A p F L hL φ σ
  apply_mem_toSubmodule g := by
    rintro v ⟨w, rfl⟩
    refine ⟨(tateRepresentation K A p).baseChange L g w, ?_⟩
    exact LinearMap.congr_fun
      (tensorTateAction_commute K A p F L φ hφ g (embeddingIdempotent ℚ F L hL σ)) w

/-- The labelled decomposition respects the Galois representation. -/
def labelledTateDecompositionEquiv :
    ((tateRepresentation K A p).baseChange L).Equiv
      (Representation.pi fun σ =>
        (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation) :=
  .mk (labelledTateDecomposition K A p F L hL φ) (by
    intro g
    apply LinearMap.ext
    intro v
    funext σ
    apply Subtype.ext
    exact LinearMap.congr_fun
      (tensorTateAction_commute K A p F L φ hφ g (embeddingIdempotent ℚ F L hL σ)) v)

section Naturality

variable {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsCommMonObj B]
  (ψ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) B))
  (f : A ⟶ B) [IsMonHom f]
  (h : ∀ (a : 𝓞 F) (x : Points K (AlgebraicClosure K) A),
    pointsMap K (AlgebraicClosure K) f (φ a x) = ψ a (pointsMap K (AlgebraicClosure K) f x))

/-- A coefficient-compatible geometric map preserves each labelled Tate summand. -/
def labelledTateSummandMap (σ : F →ₐ[ℚ] L) :
    labelledTateSummand K A p F L hL φ σ →ₗ[L] labelledTateSummand K B p F L hL ψ σ :=
  (((rationalTateMap K p f).baseChange L).comp
    (labelledTateSummand K A p F L hL φ σ).subtype).codRestrict _ (by
      rintro v
      obtain ⟨w, hw⟩ := v.property
      refine ⟨(rationalTateMap K p f).baseChange L w, ?_⟩
      change tensorTateAction K B p F L ψ (embeddingIdempotent ℚ F L hL σ)
        ((rationalTateMap K p f).baseChange L w) = _
      rw [← tensorTateAction_intertwines K A p F φ ψ f h L]
      change (rationalTateMap K p f).baseChange L
        (labelledTateProjection K A p F L hL φ σ w) = _
      rw [hw]
      rfl)

@[simp]
theorem labelledTateSummandMap_apply (σ : F →ₐ[ℚ] L)
    (v : labelledTateSummand K A p F L hL φ σ) :
    (labelledTateSummandMap K A p F L hL φ ψ f h σ v : L ⊗[ℚ_[p]] rationalTate K B p) =
      (rationalTateMap K p f).baseChange L v := rfl

include h in
/-- Coefficient-labelled decomposition is natural for coefficient-compatible geometric maps. -/
theorem labelledTateDecomposition_natural (v : L ⊗[ℚ_[p]] rationalTate K A p)
    (σ : F →ₐ[ℚ] L) :
    labelledTateSummandMap K A p F L hL φ ψ f h σ
      (labelledTateDecomposition K A p F L hL φ v σ) =
        labelledTateDecomposition K B p F L hL ψ ((rationalTateMap K p f).baseChange L v) σ := by
  apply Subtype.ext
  exact tensorTateAction_intertwines K A p F φ ψ f h L
    (embeddingIdempotent ℚ F L hL σ) v

/-- A coefficient-compatible geometric morphism intertwines the labelled Galois factors. -/
def labelledTateIntertwiningMap
    (hψ : ∀ a, ∃ (f : B ⟶ B) (_ : IsMonHom f),
      ψ a = pointsMap K (AlgebraicClosure K) f)
    (σ : F →ₐ[ℚ] L) :
    (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation.IntertwiningMap
      (labelledTateSubrepresentation K B p F L hL ψ hψ σ).toRepresentation where
  toLinearMap := labelledTateSummandMap K A p F L hL φ ψ f h σ
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun
      (((rationalTateIntertwiningMap K p f).baseChange L).isIntertwining' g) v

end Naturality

end AlgebraicGeometry.GroupScheme
