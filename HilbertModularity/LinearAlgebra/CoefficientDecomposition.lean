/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Idempotents
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Algebra.DirectSum.Module

/-! # Splitting a separable coefficient algebra

Evaluation at the embeddings identifies a finite separable coefficient field,
after extension to a splitting field, with a product of copies of that field.
The coordinate functions give its orthogonal primitive idempotents. Scalars
are written on the left of the tensor product; tensor commutativity identifies
this convention with the coefficient-first convention.

The idempotents decompose every module over the coefficient algebra into an
internal direct sum. Each summand has the rank of a finite free coefficient
module, and coefficient-linear maps preserve the labels.

## References

The coefficient decomposition used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Classical

namespace Algebra.TensorProduct

variable (F K L : Type*) [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra F L]

/-- Evaluation of a coefficient tensor at every embedding into the scalar field. -/
def embeddingEvaluation : L ⊗[F] K →ₐ[L] ((K →ₐ[F] L) → L) :=
  liftEquivRight F L K _ (AlgHom.pi fun σ => σ)

@[simp]
theorem embeddingEvaluation_tmul (a : L) (x : K) (σ : K →ₐ[F] L) :
    embeddingEvaluation F K L (a ⊗ₜ[F] x) σ = a * σ x := by
  simp [embeddingEvaluation, liftEquivRight]

/-- Two distinct coefficient embeddings can be separated by a tensor taking values one and zero. -/
theorem exists_embeddingEvaluation_eq_one_zero (σ τ : K →ₐ[F] L) (h : σ ≠ τ) :
    ∃ z : L ⊗[F] K, embeddingEvaluation F K L z σ = 1 ∧
      embeddingEvaluation F K L z τ = 0 := by
  obtain ⟨x, hx⟩ : ∃ x : K, σ x ≠ τ x := by
    by_contra! h'
    exact h (AlgHom.ext h')
  refine ⟨(σ x - τ x)⁻¹ • ((1 : L) ⊗ₜ[F] x - τ x ⊗ₜ[F] (1 : K)), ?_, ?_⟩
  · simp [map_sub, map_smul, sub_ne_zero.mpr hx]
  · simp [map_sub, map_smul]

variable [FiniteDimensional F K]

/-- Interpolation gives a tensor whose evaluations form a single coordinate idempotent. -/
theorem exists_embeddingEvaluation_eq_single (σ : K →ₐ[F] L) :
    ∃ z : L ⊗[F] K, embeddingEvaluation F K L z = Pi.single σ 1 := by
  classical
  have h (τ : K →ₐ[F] L) : ∃ z : L ⊗[F] K,
      embeddingEvaluation F K L z σ = 1 ∧
      (τ ≠ σ → embeddingEvaluation F K L z τ = 0) := by
    by_cases he : τ = σ
    · exact ⟨1, by simp, fun hn => (hn he).elim⟩
    · obtain ⟨z, hz, hz'⟩ := exists_embeddingEvaluation_eq_one_zero F K L σ τ (Ne.symm he)
      exact ⟨z, hz, fun _ => hz'⟩
  choose z hz hz' using h
  refine ⟨∏ τ, z τ, ?_⟩
  ext τ
  simp only [map_prod, Finset.prod_apply]
  by_cases he : τ = σ
  · subst τ
    simp [hz]
  · rw [Pi.single_eq_of_ne he]
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (hz' τ he)

/-- Evaluation onto all embeddings is surjective, even before separability is imposed. -/
theorem embeddingEvaluation_surjective : Function.Surjective (embeddingEvaluation F K L) := by
  classical
  choose z hz using exists_embeddingEvaluation_eq_single F K L
  intro f
  refine ⟨∑ σ, f σ • z σ, ?_⟩
  simp only [map_sum, map_smul, hz]
  ext σ
  simp [Pi.single_apply]

variable [Algebra.IsSeparable F K]

/-- A separable coefficient field splits over any field containing all its conjugates. -/
def embeddingEquiv
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits) :
    L ⊗[F] K ≃ₐ[L] ((K →ₐ[F] L) → L) :=
  AlgEquiv.ofBijective (embeddingEvaluation F K L) ⟨by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (embeddingEvaluation F K L).toLinearMap) ?_).mpr
    · exact embeddingEvaluation_surjective F K L
    · rw [Module.finrank_baseChange, Module.finrank_pi]
      simpa using (AlgHom.card_of_splits F K L hL).symm,
    embeddingEvaluation_surjective F K L⟩

@[simp]
theorem embeddingEquiv_tmul
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    (a : L) (x : K) (σ : K →ₐ[F] L) :
    embeddingEquiv F K L hL (a ⊗ₜ[F] x) σ = a * σ x :=
  embeddingEvaluation_tmul F K L a x σ

/-- The coefficient idempotent selecting the embedding `σ`. -/
def embeddingIdempotent
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    (σ : K →ₐ[F] L) : L ⊗[F] K :=
  (embeddingEquiv F K L hL).symm (Pi.single σ 1)

@[simp]
theorem embeddingEquiv_embeddingIdempotent
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    (σ : K →ₐ[F] L) :
    embeddingEquiv F K L hL (embeddingIdempotent F K L hL σ) = Pi.single σ 1 :=
  (embeddingEquiv F K L hL).apply_symm_apply _

/-- Each coefficient projection is idempotent. -/
theorem embeddingIdempotent_mul_self
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    (σ : K →ₐ[F] L) :
    embeddingIdempotent F K L hL σ * embeddingIdempotent F K L hL σ =
      embeddingIdempotent F K L hL σ := by
  apply (embeddingEquiv F K L hL).injective
  ext τ
  simp [Pi.single_apply]

/-- Distinct coefficient projections are orthogonal. -/
theorem embeddingIdempotent_mul_of_ne
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    (σ τ : K →ₐ[F] L) (h : σ ≠ τ) :
    embeddingIdempotent F K L hL σ * embeddingIdempotent F K L hL τ = 0 := by
  apply (embeddingEquiv F K L hL).injective
  ext υ
  by_cases hs : υ = σ
  · subst υ
    simp [h]
  · simp [Pi.single_apply, hs]

/-- The coefficient projections sum to the identity. -/
theorem sum_embeddingIdempotent
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits) :
    ∑ σ, embeddingIdempotent F K L hL σ = 1 := by
  apply (embeddingEquiv F K L hL).injective
  ext τ
  simp [Pi.single_apply]

/-- A coefficient projection is nonzero. -/
theorem embeddingIdempotent_ne_zero
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    (σ : K →ₐ[F] L) : embeddingIdempotent F K L hL σ ≠ 0 := by
  intro h
  have := congrArg (fun z => embeddingEquiv F K L hL z σ) h
  simp at this

/-- On the labelled factor, the coefficient field acts through its label. -/
theorem tmul_mul_embeddingIdempotent
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    (σ : K →ₐ[F] L) (a : L) (x : K) :
    (a ⊗ₜ[F] x) * embeddingIdempotent F K L hL σ =
      (a * σ x) • embeddingIdempotent F K L hL σ := by
  apply (embeddingEquiv F K L hL).injective
  ext τ
  by_cases h : τ = σ
  · subst τ
    simp
  · simp [h]

/-- Multiplication by a labelled idempotent evaluates the coefficient at that label. -/
theorem mul_embeddingIdempotent
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    (σ : K →ₐ[F] L) (z : L ⊗[F] K) :
    z * embeddingIdempotent F K L hL σ =
      (embeddingEquiv F K L hL z σ) • embeddingIdempotent F K L hL σ := by
  apply (embeddingEquiv F K L hL).injective
  ext τ
  by_cases h : τ = σ
  · subst τ
    simp
  · simp [h]

/-- A coefficient idempotent has no proper nonzero idempotent below it. -/
theorem embeddingIdempotent_primitive
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    (σ : K →ₐ[F] L) (e : L ⊗[F] K) (he : e * e = e)
    (hle : e * embeddingIdempotent F K L hL σ = e) :
    e = 0 ∨ e = embeddingIdempotent F K L hL σ := by
  let E := embeddingEquiv F K L hL
  have heσ : E e σ * E e σ = E e σ := by
    simpa using congrArg (fun z => E z σ) he
  have hzero (τ : K →ₐ[F] L) (hτ : τ ≠ σ) : E e τ = 0 := by
    have h := congrArg (fun z => E z τ) hle
    simpa [E, Pi.single_apply, hτ, Ne.symm hτ] using h.symm
  have hscalar : E e σ = 0 ∨ E e σ = 1 := by
    have h : E e σ * (E e σ - 1) = 0 := by rw [mul_sub, mul_one, heσ, sub_self]
    exact (mul_eq_zero.mp h).imp_right sub_eq_zero.mp
  rcases hscalar with hσ | hσ
  · left
    apply E.injective
    ext τ
    by_cases hτ : τ = σ
    · subst τ
      simpa using hσ
    · simpa using hzero τ hτ
  · right
    apply E.injective
    ext τ
    by_cases hτ : τ = σ
    · subst τ
      simpa [E] using hσ
    · simpa [E, Pi.single_apply, hτ, Ne.symm hτ] using hzero τ hτ

/-- The labelled idempotents form a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_embeddingIdempotent
    (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits) :
    CompleteOrthogonalIdempotents (embeddingIdempotent F K L hL) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  exact ⟨fun σ τ h => embeddingIdempotent_mul_of_ne F K L hL σ τ h,
    sum_embeddingIdempotent F K L hL⟩

end Algebra.TensorProduct

namespace CompleteOrthogonalIdempotents

variable {R V ι : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
  [Fintype ι] {e : ι → Module.End R V} (he : CompleteOrthogonalIdempotents e)

include he in
/-- Orthogonal projections act on one another's ranges by the corresponding Kronecker delta. -/
theorem apply_mem_range (i j : ι) (v : LinearMap.range (e j)) :
    e i v = if i = j then (v : V) else 0 := by
  obtain ⟨w, hw⟩ := v.property
  by_cases h : i = j
  · subst j
    simpa using (LinearMap.IsIdempotentElem.mem_range_iff (he.idem i)).mp v.property
  · rw [ite_eq_right (by exact h), ← hw]
    have hmul : e i * e j = 0 := he.ortho h
    exact congrArg (fun f : Module.End R V => f w) hmul

/-- A complete orthogonal family of projections decomposes a module into its ranges. -/
def linearEquiv : V ≃ₗ[R] ((i : ι) → LinearMap.range (e i)) where
  toFun v i := ⟨e i v, ⟨v, rfl⟩⟩
  invFun v := ∑ i, (v i : V)
  left_inv v := by
    have h := congrArg (fun f : Module.End R V => f v) he.complete
    simpa using h
  right_inv v := by
    ext i
    simp only [map_sum]
    simp [he.apply_mem_range]
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

@[simp]
theorem linearEquiv_apply (v : V) (i : ι) :
    (he.linearEquiv v i : V) = e i v := rfl

@[simp]
theorem linearEquiv_symm_apply (v : (i : ι) → LinearMap.range (e i)) :
    he.linearEquiv.symm v = ∑ i, (v i : V) := rfl

include he in
/-- The ranges of complete orthogonal projections form an internal direct sum. -/
theorem isInternal : DirectSum.IsInternal (fun i => LinearMap.range (e i)) := by
  let E := (DirectSum.linearEquivFunOnFintype R ι (fun i => LinearMap.range (e i))).trans
    he.linearEquiv.symm
  have h : E.toLinearMap = DirectSum.coeLinearMap (fun i => LinearMap.range (e i)) := by
    apply DirectSum.linearMap_ext
    intro i
    ext v
    simp [E]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  change Function.Bijective (DirectSum.coeLinearMap (fun i => LinearMap.range (e i)))
  rw [← h]
  exact E.bijective

end CompleteOrthogonalIdempotents

namespace Algebra.TensorProduct

variable (F K L V : Type*) [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra F L] [FiniteDimensional F K] [Algebra.IsSeparable F K]
  [AddCommGroup V] [Module L V] [Module (L ⊗[F] K) V] [IsScalarTower L (L ⊗[F] K) V]
  (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)

/-- Projection onto the coefficient label `σ` through the coefficient-algebra action. -/
def coefficientProjection (σ : K →ₐ[F] L) : Module.End L V :=
  Algebra.lsmul L L V (embeddingIdempotent F K L hL σ)

@[simp]
theorem coefficientProjection_apply (σ : K →ₐ[F] L) (v : V) :
    coefficientProjection F K L V hL σ v = embeddingIdempotent F K L hL σ • v := rfl

/-- The coefficient-labelled summand is the image of its primitive idempotent. -/
def coefficientSummand (σ : K →ₐ[F] L) : Submodule L V :=
  LinearMap.range (coefficientProjection F K L V hL σ)

/-- Coefficient projections are a complete orthogonal family of linear endomorphisms. -/
theorem completeOrthogonalIdempotents_coefficientProjection :
    CompleteOrthogonalIdempotents (coefficientProjection F K L V hL) :=
  (completeOrthogonalIdempotents_embeddingIdempotent F K L hL).map
    (Algebra.lsmul L L V).toRingHom

/-- Membership in a coefficient summand is equivalent to being fixed by its projection. -/
theorem mem_coefficientSummand_iff (σ : K →ₐ[F] L) (v : V) :
    v ∈ coefficientSummand F K L V hL σ ↔ embeddingIdempotent F K L hL σ • v = v :=
  LinearMap.IsIdempotentElem.mem_range_iff
    ((completeOrthogonalIdempotents_coefficientProjection F K L V hL).idem σ)

/-- The coefficient field acts on a labelled summand through the corresponding embedding. -/
theorem tmul_smul_coefficientSummand (σ : K →ₐ[F] L) (a : L) (x : K)
    (v : coefficientSummand F K L V hL σ) :
    (a ⊗ₜ[F] x) • (v : V) = (a * σ x) • (v : V) := by
  obtain ⟨w, hw⟩ := v.property
  change embeddingIdempotent F K L hL σ • w = (v : V) at hw
  rw [← hw, ← mul_smul, tmul_mul_embeddingIdempotent, smul_assoc]

/-- The simultaneous coefficient projections identify a module with its labelled summands. -/
def coefficientDecomposition : V ≃ₗ[L] ((σ : K →ₐ[F] L) → coefficientSummand F K L V hL σ) :=
  (completeOrthogonalIdempotents_coefficientProjection F K L V hL).linearEquiv

@[simp]
theorem coefficientDecomposition_apply (v : V) (σ : K →ₐ[F] L) :
    (coefficientDecomposition F K L V hL v σ : V) = embeddingIdempotent F K L hL σ • v := rfl

@[simp]
theorem coefficientDecomposition_symm_apply
    (v : (σ : K →ₐ[F] L) → coefficientSummand F K L V hL σ) :
    (coefficientDecomposition F K L V hL).symm v = ∑ σ, (v σ : V) := rfl

/-- A coefficient basis gives a scalar-field basis of each labelled summand. -/
def coefficientSummandEquiv {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (L ⊗[F] K) V) (σ : K →ₐ[F] L) :
    coefficientSummand F K L V hL σ ≃ₗ[L] (ι → L) where
  toFun v i := embeddingEquiv F K L hL (b.equivFun v i) σ
  invFun a := ⟨b.equivFun.symm (fun i => a i • embeddingIdempotent F K L hL σ), by
    rw [mem_coefficientSummand_iff]
    apply b.equivFun.injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    ext i
    change embeddingIdempotent F K L hL σ * (a i • embeddingIdempotent F K L hL σ) =
      a i • embeddingIdempotent F K L hL σ
    rw [mul_smul_comm, embeddingIdempotent_mul_self]⟩
  left_inv v := by
    apply Subtype.ext
    apply b.equivFun.injective
    ext i
    simp only [LinearEquiv.apply_symm_apply]
    rw [← mul_embeddingIdempotent, mul_comm]
    have hv := (mem_coefficientSummand_iff F K L V hL σ v).mp v.property
    have h := congrArg (fun w => b.equivFun w i) hv
    simpa using h
  right_inv a := by
    ext i
    change embeddingEquiv F K L hL
      (b.equivFun (b.equivFun.symm (fun j => a j • embeddingIdempotent F K L hL σ)) i) σ = a i
    rw [LinearEquiv.apply_symm_apply]
    simp
  map_add' v w := by
    ext i
    simp
  map_smul' c v := by
    ext i
    change embeddingEquiv F K L hL ((b.equivFun.restrictScalars L) (c • (v : V)) i) σ =
      c * embeddingEquiv F K L hL ((b.equivFun.restrictScalars L) (v : V) i) σ
    rw [map_smul]
    simp

/-- Every coefficient summand has the rank of a given coefficient-algebra basis. -/
theorem finrank_coefficientSummand {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (L ⊗[F] K) V) (σ : K →ₐ[F] L) :
    Module.finrank L (coefficientSummand F K L V hL σ) = Fintype.card ι := by
  rw [(coefficientSummandEquiv F K L V hL b σ).finrank_eq, Module.finrank_pi]

/-- Finite freeness over the split coefficient algebra gives the same dimension at every label. -/
theorem finrank_coefficientSummand_eq [Module.Free (L ⊗[F] K) V]
    [Module.Finite (L ⊗[F] K) V] (σ : K →ₐ[F] L) :
    Module.finrank L (coefficientSummand F K L V hL σ) = Module.finrank (L ⊗[F] K) V := by
  have : Nontrivial (L ⊗[F] K) := Module.nontrivial_of_finrank_pos (R := L) (by
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos)
  let : StrongRankCondition (L ⊗[F] K) := commRing_strongRankCondition _
  let b := Module.Free.chooseBasis (L ⊗[F] K) V
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex (L ⊗[F] K) V)
  rw [finrank_coefficientSummand F K L V hL b σ, Module.finrank_eq_card_basis b]

/-- Coefficient-labelled summands form an internal direct sum of the original module. -/
theorem isInternal_coefficientSummand : DirectSum.IsInternal (coefficientSummand F K L V hL) :=
  (completeOrthogonalIdempotents_coefficientProjection F K L V hL).isInternal

variable {W : Type*} [AddCommGroup W] [Module L W]
  [Module (L ⊗[F] K) W] [IsScalarTower L (L ⊗[F] K) W]

/-- A coefficient-linear map preserves every labelled summand. -/
def coefficientSummandMap (f : V →ₗ[L ⊗[F] K] W) (σ : K →ₐ[F] L) :
    coefficientSummand F K L V hL σ →ₗ[L] coefficientSummand F K L W hL σ :=
  ((f.restrictScalars L).comp (coefficientSummand F K L V hL σ).subtype).codRestrict _ (by
    intro v
    rw [mem_coefficientSummand_iff]
    change embeddingIdempotent F K L hL σ • f (v : V) = f (v : V)
    rw [← f.map_smul, (mem_coefficientSummand_iff F K L V hL σ v).mp v.property])

@[simp]
theorem coefficientSummandMap_apply (f : V →ₗ[L ⊗[F] K] W) (σ : K →ₐ[F] L)
    (v : coefficientSummand F K L V hL σ) :
    (coefficientSummandMap F K L V hL f σ v : W) = f v := rfl

/-- Coefficient decomposition is natural for coefficient-linear maps, including specialization maps. -/
theorem coefficientDecomposition_natural (f : V →ₗ[L ⊗[F] K] W) (v : V) (σ : K →ₐ[F] L) :
    coefficientSummandMap F K L V hL f σ (coefficientDecomposition F K L V hL v σ) =
      coefficientDecomposition F K L W hL (f v) σ := by
  apply Subtype.ext
  exact f.map_smul (embeddingIdempotent F K L hL σ) v

end Algebra.TensorProduct
