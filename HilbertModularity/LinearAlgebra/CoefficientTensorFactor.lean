/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.CoefficientScalarExtension
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Labelled summands as coefficient tensors

An embedding-idempotent summand is the scalar extension of the original
coefficient module along that embedding. The comparison sends a pure tensor
to its actual idempotent projection, giving the coefficient-tensor realization
used in [TripathiGoswami, ramified scalar label].
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Algebra.TensorProduct

variable (k R F L V : Type*) [Field k] [Field R] [Field F] [Field L]
  [Algebra k R] [Algebra k F] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
  [AddCommGroup V] [Module R V] [Module (R ⊗[k] F) V]
  [IsScalarTower R (R ⊗[k] F) V] [Module k V] [IsScalarTower k R V]

/-- An embedding of the multiplication field evaluates the original coefficient tensor algebra. -/
def coefficientTensorEmbedding (σ : F →ₐ[k] L) : R ⊗[k] F →ₐ[R] L :=
  AlgHom.liftEquiv k R F L σ

/-- Evaluation of a pure coefficient tensor uses the same embedding. -/
@[simp] theorem coefficientTensorEmbedding_tmul (σ : F →ₐ[k] L) (r : R) (f : F) :
    coefficientTensorEmbedding k R F L σ (r ⊗ₜ[k] f) = algebraMap R L r * σ f := by
  change r • σ f = _
  exact Algebra.smul_def r (σ f)

variable [FiniteDimensional k F] [Algebra.IsSeparable k F]

/-- Evaluating extended coefficient coordinates agrees with the original tensor embedding. -/
theorem embeddingEquiv_cancelBaseChange
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) (l : L) (a : R ⊗[k] F) :
    embeddingEquiv k F L hL (cancelBaseChange k R L L F (l ⊗ₜ[R] a)) σ =
      l * coefficientTensorEmbedding k R F L σ a := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, Pi.add_apply, ha, hb, mul_add]
  | tmul r f =>
    rw [cancelBaseChange_tmul, embeddingEquiv_tmul, coefficientTensorEmbedding_tmul,
      Algebra.smul_def]
    ring

/-- Projection coordinates are evaluation of the original extended coefficient coordinates. -/
theorem coefficientScalarExtensionProjectionEquiv_project {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V)
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits) (σ : F →ₐ[k] L)
    (w : L ⊗[R] V) (i : ι) :
    coefficientScalarExtensionProjectionEquiv k R F L V b hL σ
      ⟨coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ) w,
        ⟨w, rfl⟩⟩ i =
      embeddingEquiv k F L hL (coefficientScalarExtensionEquiv k R F L V b w i) σ := by
  classical
  change embeddingEquiv k F L hL
    (coefficientScalarExtensionEquiv k R F L V b
      (coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ) w) i) σ = _
  rw [coefficientScalarExtensionEquiv_action, map_mul, embeddingEquiv_embeddingIdempotent]
  simp

/-- A coefficient basis identifies the embedding-idempotent summand with its genuine coefficient tensor. -/
def coefficientProjectionTensorEquiv {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V)
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits) (σ : F →ₐ[k] L) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    (L ⊗[R ⊗[k] F] V) ≃ₗ[L]
      LinearMap.range (coefficientScalarExtensionAction k R F L V
        (embeddingIdempotent k F L hL σ)) := by
  letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  exact (b.baseChange L).equivFun.trans
    (coefficientScalarExtensionProjectionEquiv k R F L V b hL σ).symm

/-- The comparison sends every pure tensor to its actual labelled projection. -/
@[simp] theorem coefficientProjectionTensorEquiv_tmul {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V)
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits) (σ : F →ₐ[k] L)
    (l : L) (v : V) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    (coefficientProjectionTensorEquiv k R F L V b hL σ (l ⊗ₜ[R ⊗[k] F] v) : L ⊗[R] V) =
      coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ)
        (l ⊗ₜ[R] v) := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  have h : coefficientProjectionTensorEquiv k R F L V b hL σ (l ⊗ₜ[R ⊗[k] F] v) =
      ⟨coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ)
        (l ⊗ₜ[R] v), ⟨l ⊗ₜ[R] v, rfl⟩⟩ := by
    apply (coefficientScalarExtensionProjectionEquiv k R F L V b hL σ).injective
    simp only [coefficientProjectionTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    funext i
    rw [coefficientScalarExtensionProjectionEquiv_project,
      coefficientScalarExtensionEquiv_tmul, embeddingEquiv_cancelBaseChange]
    change (b.baseChange L).repr (l ⊗ₜ[R ⊗[k] F] v) i = _
    rw [Module.Basis.baseChange_repr_tmul]
    change coefficientTensorEmbedding k R F L σ (b.repr v i) * l =
      l * coefficientTensorEmbedding k R F L σ (b.repr v i)
    exact mul_comm _ _
  exact congrArg Subtype.val h

/-- The tensor comparison is independent of the coefficient basis used to construct it. -/
theorem coefficientProjectionTensorEquiv_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι (R ⊗[k] F) V) (c : Module.Basis κ (R ⊗[k] F) V)
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits) (σ : F →ₐ[k] L) :
    coefficientProjectionTensorEquiv k R F L V b hL σ =
      coefficientProjectionTensorEquiv k R F L V c hL σ := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  apply LinearEquiv.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul l v =>
    apply Subtype.ext
    rw [coefficientProjectionTensorEquiv_tmul, coefficientProjectionTensorEquiv_tmul]
  | add w z hw hz => simp only [map_add, hw, hz]

/-- Forgetting the intermediate scalar extension gives the tensor along the chosen label. -/
def coefficientTensorQuotient (σ : F →ₐ[k] L) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    (L ⊗[R] V) →ₗ[L] (L ⊗[R ⊗[k] F] V) := by
  letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  letI : IsScalarTower R (R ⊗[k] F) L := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact ((coefficientTensorEmbedding k R F L σ).commutes r).symm)
  exact ((TensorProduct.mk (R ⊗[k] F) L V 1).restrictScalars R).liftBaseChange L

omit [Module k V] [IsScalarTower k R V] [FiniteDimensional k F] [Algebra.IsSeparable k F] in
/-- The quotient preserves pure tensors. -/
@[simp] theorem coefficientTensorQuotient_tmul (σ : F →ₐ[k] L) (l : L) (v : V) :
    let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    coefficientTensorQuotient k R F L V σ (l ⊗ₜ[R] v) = l ⊗ₜ[R ⊗[k] F] v := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  change l • ((1 : L) ⊗ₜ[R ⊗[k] F] v) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The quotient evaluates every extended coefficient at its label. -/
theorem coefficientTensorQuotient_action
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) (a : L ⊗[k] F) (w : L ⊗[R] V) :
    let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    coefficientTensorQuotient k R F L V σ
      (coefficientScalarExtensionAction k R F L V a w) =
      embeddingEquiv k F L hL a σ • coefficientTensorQuotient k R F L V σ w := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, Pi.add_apply, ha, hb, add_smul]
  | tmul c f =>
    induction w using TensorProduct.inductionOn with
    | add w z hw hz => simp only [map_add, hw, hz, smul_add]
    | tmul l v =>
      rw [coefficientScalarExtensionAction_tmul, coefficientTensorQuotient_tmul,
        coefficientTensorQuotient_tmul, embeddingEquiv_tmul,
        ← TensorProduct.smul_tmul]
      dsimp only
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      change (((coefficientTensorEmbedding k R F L σ) ((1 : R) ⊗ₜ[k] f)) * (c * l)) ⊗ₜ[R ⊗[k] F] v = _
      rw [coefficientTensorEmbedding_tmul, map_one, one_mul]
      congr 1
      ring

/-- Projecting before the quotient leaves the quotient unchanged. -/
@[simp] theorem coefficientTensorQuotient_project
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) (w : L ⊗[R] V) :
    let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    coefficientTensorQuotient k R F L V σ
      (coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ) w) =
      coefficientTensorQuotient k R F L V σ w := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  rw [coefficientTensorQuotient_action k R F L V hL]
  simp

omit [FiniteDimensional k F] [Algebra.IsSeparable k F] in
/-- Extending an original coefficient element agrees with its original action on a pure tensor. -/
theorem coefficientScalarExtensionAction_original (a : R ⊗[k] F) (l : L) (v : V) :
    coefficientScalarExtensionAction k R F L V
      (cancelBaseChange k R L L F ((1 : L) ⊗ₜ[R] a)) (l ⊗ₜ[R] v) =
      l ⊗ₜ[R] (a • v) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply,
      add_smul, ha, hb]
  | tmul r f =>
    rw [cancelBaseChange_tmul, coefficientScalarExtensionAction_tmul]
    rw [smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
    congr 1
    rw [← smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The projector turns the original coefficient action into evaluation at its label. -/
theorem coefficientProjection_original_smul
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) (a : R ⊗[k] F) (v : V) :
    coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ)
        ((1 : L) ⊗ₜ[R] (a • v)) =
      coefficientTensorEmbedding k R F L σ a •
        coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ)
          ((1 : L) ⊗ₜ[R] v) := by
  rw [← coefficientScalarExtensionAction_original k R F L V a 1 v]
  change (coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ) *
    coefficientScalarExtensionAction k R F L V
      (cancelBaseChange k R L L F ((1 : L) ⊗ₜ[R] a))) ((1 : L) ⊗ₜ[R] v) = _
  rw [← map_mul, mul_comm, mul_embeddingIdempotent,
    embeddingEquiv_cancelBaseChange, one_mul, map_smul, LinearMap.smul_apply]

/-- The universal coefficient tensor maps to the actual projector without a basis hypothesis. -/
def coefficientTensorProjection
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    (L ⊗[R ⊗[k] F] V) →ₗ[L] (L ⊗[R] V) := by
  letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  letI m : Module (R ⊗[k] F) (L ⊗[R] V) :=
    Module.compHom _ (coefficientTensorEmbedding k R F L σ).toRingHom
  letI ht : IsScalarTower (R ⊗[k] F) L (L ⊗[R] V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : V →ₗ[R ⊗[k] F] (L ⊗[R] V) :=
    { toFun := fun v => coefficientScalarExtensionAction k R F L V
        (embeddingIdempotent k F L hL σ) ((1 : L) ⊗ₜ[R] v)
      map_add' := fun v w => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun a v => coefficientProjection_original_smul k R F L V hL σ a v }
  let g := @LinearMap.liftBaseChange _ _ _ L _ _ _ _ _ _ m _ ht f
  exact g

/-- The universal map is the actual projector on every pure tensor. -/
@[simp] theorem coefficientTensorProjection_tmul
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) (l : L) (v : V) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    coefficientTensorProjection k R F L V hL σ (l ⊗ₜ[R ⊗[k] F] v) =
      coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ)
        (l ⊗ₜ[R] v) := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  change l • coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ)
      ((1 : L) ⊗ₜ[R] v) = _
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The universal projection is a section of the tensor quotient. -/
theorem coefficientTensorQuotient_projection
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    ∀ w : L ⊗[R ⊗[k] F] V,
      coefficientTensorQuotient k R F L V σ
        (coefficientTensorProjection k R F L V hL σ w) = w := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul l v => rw [coefficientTensorProjection_tmul, coefficientTensorQuotient_project,
      coefficientTensorQuotient_tmul]
  | add w z hw hz => simp only [map_add, hw, hz]

/-- Composing in the other order is the actual embedding-idempotent projector. -/
theorem coefficientTensorProjection_quotient
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) (w : L ⊗[R] V) :
    coefficientTensorProjection k R F L V hL σ (coefficientTensorQuotient k R F L V σ w) =
      coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ) w := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  induction w using TensorProduct.inductionOn with
  | tmul l v => rw [coefficientTensorQuotient_tmul, coefficientTensorProjection_tmul]
  | add w z hw hz => simp only [map_add, hw, hz]

/-- Every projected coefficient tensor lies in the actual labelled summand. -/
theorem coefficientTensorProjection_mem_range
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    ∀ w : L ⊗[R ⊗[k] F] V,
      coefficientTensorProjection k R F L V hL σ w ∈
        LinearMap.range (coefficientScalarExtensionAction k R F L V
          (embeddingIdempotent k F L hL σ)) := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  intro w
  refine ⟨coefficientTensorProjection k R F L V hL σ w, ?_⟩
  rw [← coefficientTensorProjection_quotient, coefficientTensorQuotient_projection]

/-- The actual labelled summand is the coefficient tensor, without a basis or freeness hypothesis. -/
def coefficientTensorSummandEquiv
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    (L ⊗[R ⊗[k] F] V) ≃ₗ[L]
      LinearMap.range (coefficientScalarExtensionAction k R F L V
        (embeddingIdempotent k F L hL σ)) := by
  letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  let p := coefficientTensorProjection k R F L V hL σ
  let q := coefficientTensorQuotient k R F L V σ
  refine { p.codRestrict _ (coefficientTensorProjection_mem_range k R F L V hL σ) with
    invFun := fun w => q w
    left_inv := coefficientTensorQuotient_projection k R F L V hL σ
    right_inv := ?_ }
  intro w
  apply Subtype.ext
  change p (q w) = (w : L ⊗[R] V)
  rw [coefficientTensorProjection_quotient]
  obtain ⟨v, hv⟩ := w.property
  rw [← hv]
  change (coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ) *
    coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ)) v = _
  rw [← map_mul, embeddingIdempotent_mul_self]

/-- The basis-free equivalence preserves the same literal projector formula. -/
@[simp] theorem coefficientTensorSummandEquiv_tmul
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
    (σ : F →ₐ[k] L) (l : L) (v : V) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    (coefficientTensorSummandEquiv k R F L V hL σ (l ⊗ₜ[R ⊗[k] F] v) : L ⊗[R] V) =
      coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ)
        (l ⊗ₜ[R] v) :=
  coefficientTensorProjection_tmul k R F L V hL σ l v

/-- The universal comparison agrees with the comparison constructed from any coefficient basis. -/
theorem coefficientTensorSummandEquiv_eq_basis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V)
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits) (σ : F →ₐ[k] L) :
    coefficientTensorSummandEquiv k R F L V hL σ =
      coefficientProjectionTensorEquiv k R F L V b hL σ := by
  let : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  apply LinearEquiv.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul l v =>
    apply Subtype.ext
    rw [coefficientTensorSummandEquiv_tmul, coefficientProjectionTensorEquiv_tmul]
  | add w z hw hz => simp only [map_add, hw, hz]

variable (W : Type*) [AddCommGroup W] [Module R W] [Module (R ⊗[k] F) W]
  [IsScalarTower R (R ⊗[k] F) W] [Module k W] [IsScalarTower k R W]

omit [FiniteDimensional k F] [Algebra.IsSeparable k F] in
/-- Every original coefficient-linear map commutes with the extended coefficient action. -/
theorem coefficientScalarExtensionAction_naturality (f : V →ₗ[R ⊗[k] F] W)
    (a : L ⊗[k] F) (w : L ⊗[R] V) :
    (f.restrictScalars R).baseChange L (coefficientScalarExtensionAction k R F L V a w) =
      coefficientScalarExtensionAction k R F L W a ((f.restrictScalars R).baseChange L w) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul l x =>
    induction w using TensorProduct.inductionOn with
    | add w z hw hz => simp only [map_add, hw, hz]
    | tmul c v =>
      rw [coefficientScalarExtensionAction_tmul, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul, coefficientScalarExtensionAction_tmul]
      change (l * c) ⊗ₜ[R] f (((1 : R) ⊗ₜ[k] x) • v) =
        (l * c) ⊗ₜ[R] (((1 : R) ⊗ₜ[k] x) • f v)
      rw [f.map_smul]

end Algebra.TensorProduct
