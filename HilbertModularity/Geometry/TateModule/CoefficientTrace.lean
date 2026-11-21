/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.CoefficientDecomposition
public import HilbertModularity.RepresentationTheory.Duality
public import HilbertModularity.LinearAlgebra.RankTwoTrace
public import HilbertModularity.LinearAlgebra.CoefficientBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Traces on labelled geometric Tate factors

The trace on a labelled factor is the trace of its coefficient projector times
the full Tate action. This proves the projector step of
[TripathiGoswamiRevised, Lemma `labelled-RM-compat`]. The geometric
specialization needed to apply [MilneAV, Chapter I, Proposition 10.20] to the
full-space endomorphism traces is a separate input.
-/

public section
noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NumberField

namespace Algebra.TensorProduct

/-- The coordinates of a labelled projector over one algebraic splitting field
give the same finite expansion after every coefficient embedding. In particular,
the coefficients are chosen before the auxiliary Tate prime. -/
theorem embeddingIdempotent_eq_sum_coordinates
    {F E L J : Type*} [Field F] [NumberField F] [Field E] [Field L]
    [Algebra ℚ E] [Algebra ℚ L] [Fintype J]
    (basis : Module.Basis J ℚ F)
    (hE : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ E)).Splits)
    (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] E) (j : E →ₐ[ℚ] L) :
    embeddingIdempotent ℚ F L hL (j.comp σ) =
      ∑ k, j ((basis.baseChange E).repr (embeddingIdempotent ℚ F E hE σ) k) •
        ((1 : L) ⊗ₜ[ℚ] basis k) := by
  have h := congrArg (Algebra.TensorProduct.map j (AlgHom.id ℚ F))
    ((basis.baseChange E).sum_repr (embeddingIdempotent ℚ F E hE σ))
  rw [map_embeddingIdempotent ℚ F E L j hE hL σ] at h
  simpa only [map_sum, Module.Basis.baseChange_apply, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply] using h.symm

end Algebra.TensorProduct

namespace Subrepresentation

/-- An invariant projector computes the trace on its image. -/
theorem trace_eq_projected {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {ρ : Representation k G V} (S : Subrepresentation ρ)
    (e : Module.End k V) (he : IsIdempotentElem e)
    (hrange : S.toSubmodule = LinearMap.range e) (g : G) :
    LinearMap.trace k S.toSubmodule (S.toRepresentation g) =
      LinearMap.trace k V (e * ρ g) := by
  let r : V →ₗ[k] S.toSubmodule := e.codRestrict S.toSubmodule (by
    intro v
    rw [hrange]
    exact LinearMap.mem_range_self e v)
  let i : S.toSubmodule →ₗ[k] V := S.toSubmodule.subtype
  have hrestrict : (r.comp (ρ g)).comp i = S.toRepresentation g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hv : ρ g v ∈ LinearMap.range e := by
      rw [← hrange]
      exact S.apply_mem_toSubmodule g v.property
    exact (LinearMap.IsIdempotentElem.mem_range_iff he).mp hv
  rw [← hrestrict, ← LinearMap.trace_comp_comm' (r.comp (ρ g)) i]
  rfl

end Subrepresentation

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
  [FiniteDimensional L (L ⊗[ℚ_[p]] rationalTate K A p)]

/-- Trace on the actual labelled Tate factor equals the projected trace on the
full Tate module. No choice of basis or Frobenius lift enters this identity. -/
theorem trace_labelledTateSubrepresentation (σ : F →ₐ[ℚ] L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    LinearMap.trace L _
      ((labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation g) =
    LinearMap.trace L _
      (labelledTateProjection K A p F L hL φ σ *
        (tateRepresentation K A p).baseChange L g) := by
  exact Subrepresentation.trace_eq_projected
    (labelledTateSubrepresentation K A p F L hL φ hφ σ)
    (labelledTateProjection K A p F L hL φ σ)
    ((completeOrthogonalIdempotents_labelledTateProjection K A p F L hL φ).idem σ)
    rfl g

/-- The projector formula holds for every power of the same Galois element,
in particular for the first two Frobenius power traces used in Newton's identity. -/
theorem trace_pow_labelledTateSubrepresentation (σ : F →ₐ[ℚ] L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (n : ℕ) :
    LinearMap.trace L _
      (((labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation g) ^ n) =
    LinearMap.trace L _
      (labelledTateProjection K A p F L hL φ σ *
        ((tateRepresentation K A p).baseChange L g) ^ n) := by
  simpa only [map_pow] using
    trace_labelledTateSubrepresentation K A p F L hL φ hφ σ (g ^ n)

/-- A finite expansion of the coefficient idempotent expresses labelled power
traces as weighted full-space endomorphism traces. These are precisely the
traces to which the endomorphism theorem of [MilneAV, Chapter I, Proposition
10.20] applies after good-reduction specialization. -/
theorem trace_pow_labelledTateSubrepresentation_eq_sum
    (σ : F →ₐ[ℚ] L) {J : Type*} (s : Finset J) (b : J → L) (a : J → F)
    (he : embeddingIdempotent ℚ F L hL σ =
      ∑ j ∈ s, b j • ((1 : L) ⊗ₜ[ℚ] a j))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (n : ℕ) :
    LinearMap.trace L _
      (((labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation g) ^ n) =
    ∑ j ∈ s, b j * LinearMap.trace L _
      (tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] a j) *
        ((tateRepresentation K A p).baseChange L g) ^ n) := by
  rw [trace_pow_labelledTateSubrepresentation]
  simp only [labelledTateProjection, he, map_sum, map_smul, Finset.sum_mul,
    smul_mul_assoc, smul_eq_mul]

/-- The common algebraic weighted traces transport through a fixed coefficient
embedding. Only full-space traces are supplied here; the labelled traces are
derived from the actual coefficient projector. -/
theorem trace_pow_labelledTateSubrepresentation_eq_map
    (σ : F →ₐ[ℚ] L) {E J : Type*} [Field E] (j : E →+* L)
    (s : Finset J) (b : J → E) (a : J → F)
    (he : embeddingIdempotent ℚ F L hL σ =
      ∑ k ∈ s, j (b k) • ((1 : L) ⊗ₜ[ℚ] a k))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (n : ℕ)
    (t : J → E)
    (ht : ∀ k ∈ s, LinearMap.trace L _
      (tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] a k) *
        ((tateRepresentation K A p).baseChange L g) ^ n) = j (t k)) :
    LinearMap.trace L _
      (((labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation g) ^ n) =
      j (∑ k ∈ s, b k * t k) := by
  rw [trace_pow_labelledTateSubrepresentation_eq_sum K A p F L hL φ hφ σ
    s (fun k => j (b k)) a he g n, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ht k hk, map_mul]

/-- For a rank-two labelled Tate factor, the first two weighted algebraic
endomorphism traces determine its characteristic polynomial over the common
coefficient field. This proves the projector and Newton steps of
[TripathiGoswamiRevised, Lemma `labelled-RM-compat`], keeping good-reduction
specialization and the endomorphism trace theorem as explicit upstream inputs. -/
theorem charpoly_labelledTateSubrepresentation_eq_map
    [CharZero L] (σ : F →ₐ[ℚ] L) {E J : Type*} [Field E] [CharZero E] (j : E →+* L)
    (s : Finset J) (b : J → E) (a : J → F)
    (he : embeddingIdempotent ℚ F L hL σ =
      ∑ k ∈ s, j (b k) • ((1 : L) ⊗ₜ[ℚ] a k))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (basis : Module.Basis (Fin 2) L
      (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
    (t₁ t₂ : J → E)
    (ht₁ : ∀ k ∈ s, LinearMap.trace L _
      (tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] a k) *
        ((tateRepresentation K A p).baseChange L g) ^ 1) = j (t₁ k))
    (ht₂ : ∀ k ∈ s, LinearMap.trace L _
      (tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] a k) *
        ((tateRepresentation K A p).baseChange L g) ^ 2) = j (t₂ k)) :
    (LinearMap.toMatrix basis basis
      ((labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation g)).charpoly =
      (Polynomial.X ^ 2 - Polynomial.C (∑ k ∈ s, b k * t₁ k) * Polynomial.X +
        Polynomial.C (((∑ k ∈ s, b k * t₁ k) ^ 2 - ∑ k ∈ s, b k * t₂ k) / 2)).map j := by
  let f := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation g
  let M := LinearMap.toMatrix basis basis f
  have h₁ : M.trace = j (∑ k ∈ s, b k * t₁ k) := by
    rw [← LinearMap.trace_eq_matrix_trace]
    simpa only [pow_one] using trace_pow_labelledTateSubrepresentation_eq_map
      K A p F L hL φ hφ σ j s b a he g 1 t₁ ht₁
  have h₂ : (M ^ 2).trace = j (∑ k ∈ s, b k * t₂ k) := by
    dsimp only [M]
    rw [LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace]
    exact trace_pow_labelledTateSubrepresentation_eq_map
      K A p F L hL φ hφ σ j s b a he g 2 t₂ ht₂
  let d := ((∑ k ∈ s, b k * t₁ k) ^ 2 - ∑ k ∈ s, b k * t₂ k) / 2
  have hd : 2 * d = (∑ k ∈ s, b k * t₁ k) ^ 2 - ∑ k ∈ s, b k * t₂ k := by
    dsimp only [d]
    field_simp
  have hdet : M.det = j d := by
    have hn := HilbertModularity.two_mul_det_eq_sq_trace_sub_trace_sq M
    rw [h₁, h₂] at hn
    have hj := congrArg j hd
    simp only [map_mul, map_ofNat, map_sub, map_pow] at hj
    exact mul_left_cancel₀ (by norm_num : (2 : L) ≠ 0) (hn.trans hj.symm)
  change M.charpoly = _
  rw [Matrix.charpoly_fin_two, h₁, hdet]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, d]

/-- The labelled Tate polynomial descends to the fixed algebraic splitting
field once the first two full-space endomorphism traces do. The coefficient
projector expansion is constructed from a rational basis, not assumed.
This is the algebraic deduction in [TripathiGoswamiRevised,
Lemma `labelled-RM-compat`]; specialization supplies the two trace hypotheses. -/
theorem charpoly_labelledTateSubrepresentation_eq_map_of_basis
    [CharZero L] {E J : Type*} [Field E] [CharZero E] [Algebra ℚ E] [Fintype J]
    (coefficientBasis : Module.Basis J ℚ F)
    (hE : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ E)).Splits)
    (σ : F →ₐ[ℚ] E) (j : E →ₐ[ℚ] L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (basis : Module.Basis (Fin 2) L
      (labelledTateSubrepresentation K A p F L hL φ hφ (j.comp σ)).toSubmodule)
    (t₁ t₂ : J → E)
    (ht₁ : ∀ k, LinearMap.trace L _
      (tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] coefficientBasis k) *
        ((tateRepresentation K A p).baseChange L g) ^ 1) = j (t₁ k))
    (ht₂ : ∀ k, LinearMap.trace L _
      (tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] coefficientBasis k) *
        ((tateRepresentation K A p).baseChange L g) ^ 2) = j (t₂ k)) :
    (LinearMap.toMatrix basis basis
      ((labelledTateSubrepresentation K A p F L hL φ hφ (j.comp σ)).toRepresentation g)).charpoly =
      (Polynomial.X ^ 2 - Polynomial.C
        (∑ k, (coefficientBasis.baseChange E).repr (embeddingIdempotent ℚ F E hE σ) k *
          t₁ k) * Polynomial.X + Polynomial.C
        (((∑ k, (coefficientBasis.baseChange E).repr (embeddingIdempotent ℚ F E hE σ) k *
          t₁ k) ^ 2 - ∑ k,
          (coefficientBasis.baseChange E).repr (embeddingIdempotent ℚ F E hE σ) k *
          t₂ k) / 2)).map j.toRingHom := by
  classical
  apply charpoly_labelledTateSubrepresentation_eq_map K A p F L hL φ hφ
    (j.comp σ) j.toRingHom Finset.univ
    ((coefficientBasis.baseChange E).repr (embeddingIdempotent ℚ F E hE σ))
    coefficientBasis
  · simpa using embeddingIdempotent_eq_sum_coordinates coefficientBasis hE hL σ j
  · exact fun k _ => ht₁ k
  · exact fun k _ => ht₂ k

/-- For the actual cohomological dual, geometric Frobenius is the inverse of
arithmetic Frobenius on the covariant Tate module. The two inversions cancel,
so the common polynomial is unchanged and no Tate twist is introduced. -/
theorem charpoly_dual_labelledTateSubrepresentation_inv_eq_map_of_basis
    [CharZero L] {E J : Type*} [Field E] [CharZero E] [Algebra ℚ E] [Fintype J]
    (coefficientBasis : Module.Basis J ℚ F)
    (hE : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ E)).Splits)
    (σ : F →ₐ[ℚ] E) (j : E →ₐ[ℚ] L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (basis : Module.Basis (Fin 2) L
      (labelledTateSubrepresentation K A p F L hL φ hφ (j.comp σ)).toSubmodule)
    (t₁ t₂ : J → E)
    (ht₁ : ∀ k, LinearMap.trace L _
      (tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] coefficientBasis k) *
        ((tateRepresentation K A p).baseChange L g) ^ 1) = j (t₁ k))
    (ht₂ : ∀ k, LinearMap.trace L _
      (tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] coefficientBasis k) *
        ((tateRepresentation K A p).baseChange L g) ^ 2) = j (t₂ k)) :
    ((labelledTateSubrepresentation K A p F L hL φ hφ (j.comp σ)).toRepresentation.dual
      g⁻¹).charpoly =
      (Polynomial.X ^ 2 - Polynomial.C
        (∑ k, (coefficientBasis.baseChange E).repr (embeddingIdempotent ℚ F E hE σ) k *
          t₁ k) * Polynomial.X + Polynomial.C
        (((∑ k, (coefficientBasis.baseChange E).repr (embeddingIdempotent ℚ F E hE σ) k *
          t₁ k) ^ 2 - ∑ k,
          (coefficientBasis.baseChange E).repr (embeddingIdempotent ℚ F E hE σ) k *
          t₂ k) / 2)).map j.toRingHom := by
  let S := labelledTateSubrepresentation K A p F L hL φ hφ (j.comp σ)
  let : FiniteDimensional L S.toSubmodule := Module.Finite.of_basis basis
  let : Module.Free L S.toSubmodule := Module.Free.of_basis basis
  have hd := HilbertModularity.charpoly_dual_inv (K := L) (V := S.toSubmodule)
    S.toRepresentation g
  refine hd.trans ?_
  rw [← LinearMap.charpoly_toMatrix _ basis]
  exact charpoly_labelledTateSubrepresentation_eq_map_of_basis
    K A p F L hL φ hφ coefficientBasis hE σ j g basis t₁ t₂ ht₁ ht₂

end AlgebraicGeometry.GroupScheme
