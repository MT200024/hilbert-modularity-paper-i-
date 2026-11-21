/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientRank
public import HilbertModularity.RepresentationTheory.CoefficientTensorFactor
public import HilbertModularity.RepresentationTheory.ScalarAction

/-! # Native coefficient tensors of the labelled Tate family

The actual embedding-idempotent Tate summand is the tensor of the native
rational Tate module along its coefficient label. This comparison requires no
coefficient basis and retains the scheme-induced coefficient and Galois actions,
as required by [TripathiGoswami, coefficient-label lemma].
-/

@[expose] public noncomputable section
open CategoryTheory Algebra.TensorProduct
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S) (p : ℕ) [Fact p.Prime]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)

/-- The native coefficient tensor action commutes with the original Galois action. -/
theorem fiberTensorTateAction_commute
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : ℚ_[p] ⊗[ℚ] F) :
    Commute (fiberTensorTateAction K A x p F φ a)
      (tateRepresentation K (fiber K A x).X p g) := by
  apply NumberField.RingOfIntegers.tensorExtension_commute
  intro b
  exact integerTateAction_commute K (fiber K A x).X p F
    (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
    (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ) g b

/-- The original Tate representation is linear over its actual coefficient tensor algebra. -/
def fiberCoefficientTateRepresentation :
    letI : Module (ℚ_[p] ⊗[ℚ] F) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
    Representation (ℚ_[p] ⊗[ℚ] F) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (rationalTate K (fiber K A x).X p) :=
  Representation.withScalarAction (tateRepresentation K (fiber K A x).X p)
    (fiberTensorTateAction K A x p F φ).toRingHom
    (fun g a => (fiberTensorTateAction_commute K A x p F φ g a).symm)

/-- Changing coefficient scalars leaves every native Galois operator unchanged. -/
@[simp] theorem fiberCoefficientTateRepresentation_apply
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : rationalTate K (fiber K A x).X p) :
    fiberCoefficientTateRepresentation K A x p F φ g v =
      tateRepresentation K (fiber K A x).X p g v := rfl

variable (L : Type u) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

set_option maxHeartbeats 1000000 in
/-- The actual labelled arithmetic Tate summand is its native coefficient tensor, without a basis. -/
def fiberCoefficientTensorTateEquiv (σ : F →ₐ[ℚ] L) :
    letI : Module (ℚ_[p] ⊗[ℚ] F) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] F) L := (coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
    (L ⊗[ℚ_[p] ⊗[ℚ] F] rationalTate K (fiber K A x).X p) ≃ₗ[L]
      labelledTateSummand K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ := by
  let W := rationalTate K (fiber K A x).X p
  letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
  letI : Algebra (ℚ_[p] ⊗[ℚ] F) L := (coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
  letI : IsScalarTower ℚ_[p] (ℚ_[p] ⊗[ℚ] F) W :=
    fiberTensorTateAction_scalarTower K A p F φ x
  refine (coefficientTensorSummandEquiv ℚ ℚ_[p] F L W hL σ).trans
    (LinearEquiv.ofEq _ _ ?_)
  change LinearMap.range (coefficientScalarExtensionAction ℚ ℚ_[p] F L W
      (embeddingIdempotent ℚ F L hL σ)) = _
  rw [fiberCoefficientScalarExtensionAction_eq K A p L F φ x]
  rfl

set_option maxHeartbeats 1000000 in
/-- The native comparison sends a pure coefficient tensor to its actual labelled Tate projection. -/
@[simp] theorem fiberCoefficientTensorTateEquiv_tmul (σ : F →ₐ[ℚ] L)
    (l : L) (v : rationalTate K (fiber K A x).X p) :
    letI : Module (ℚ_[p] ⊗[ℚ] F) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] F) L := (coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
    (fiberCoefficientTensorTateEquiv K A x p F φ L hL σ
        (l ⊗ₜ[ℚ_[p] ⊗[ℚ] F] v) : L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) =
      labelledTateProjection K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ (l ⊗ₜ[ℚ_[p]] v) := by
  let W := rationalTate K (fiber K A x).X p
  let : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
  let : Algebra (ℚ_[p] ⊗[ℚ] F) L := (coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
  let : IsScalarTower ℚ_[p] (ℚ_[p] ⊗[ℚ] F) W :=
    fiberTensorTateAction_scalarTower K A p F φ x
  change (coefficientTensorSummandEquiv ℚ ℚ_[p] F L W hL σ
    (l ⊗ₜ[ℚ_[p] ⊗[ℚ] F] v) : L ⊗[ℚ_[p]] W) = _
  rw [coefficientTensorSummandEquiv_tmul]
  rw [fiberCoefficientScalarExtensionAction_eq]
  rfl

set_option maxHeartbeats 1000000 in
/-- The native tensor comparison intertwines the actual arithmetic Galois representations. -/
def fiberCoefficientTensorTateRepresentationEquiv (σ : F →ₐ[ℚ] L) :
    letI : Module (ℚ_[p] ⊗[ℚ] F) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] F) L := (coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
    ((fiberCoefficientTateRepresentation K A x p F φ).baseChange L).Equiv
      (labelledTateSubrepresentation K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
        (fiberPointsAction_realized K (AlgebraicClosure K) A x (𝓞 F) φ) σ).toRepresentation := by
  letI : Module (ℚ_[p] ⊗[ℚ] F) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
  letI : Algebra (ℚ_[p] ⊗[ℚ] F) L := (coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
  refine .mk (fiberCoefficientTensorTateEquiv K A x p F φ L hL σ) ?_
  intro g
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  induction w using TensorProduct.inductionOn with
  | add w z hw hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hw hz
  | tmul l v =>
    change (fiberCoefficientTensorTateEquiv K A x p F φ L hL σ
        (((fiberCoefficientTateRepresentation K A x p F φ).baseChange L) g
          (l ⊗ₜ[ℚ_[p] ⊗[ℚ] F] v)) : L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) =
      (tateRepresentation K (fiber K A x).X p).baseChange L g
        (fiberCoefficientTensorTateEquiv K A x p F φ L hL σ
          (l ⊗ₜ[ℚ_[p] ⊗[ℚ] F] v) : L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p)
    rw [Representation.baseChange_tmul, fiberCoefficientTateRepresentation_apply,
      fiberCoefficientTensorTateEquiv_tmul, fiberCoefficientTensorTateEquiv_tmul]
    exact LinearMap.congr_fun
      (tensorTateAction_commute K (fiber K A x).X p F L
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
        (fiberPointsAction_realized K (AlgebraicClosure K) A x (𝓞 F) φ) g
        (embeddingIdempotent ℚ F L hL σ)) (l ⊗ₜ[ℚ_[p]] v)

variable [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

set_option maxHeartbeats 1000000 in
/-- The fibre of the same labelled family is equivariantly the actual native coefficient tensor. -/
def labelledTateLocalSystemCoefficientTensorEquiv (σ : F →ₐ[ℚ] L) :
    letI : Module (ℚ_[p] ⊗[ℚ] F) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] F) L := (coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
    (Scheme.arithmeticFiberRepresentation K S (labelledTateLocalSystem K A p L F φ hL σ) x).Equiv
      ((fiberCoefficientTateRepresentation K A x p F φ).baseChange L) := by
  letI : Module (ℚ_[p] ⊗[ℚ] F) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
  letI : Algebra (ℚ_[p] ⊗[ℚ] F) L := (coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
  exact (labelledTateLocalSystem_arithmeticEquiv K A p L x F φ hL σ).trans
    (fiberCoefficientTensorTateRepresentationEquiv K A x p F φ L hL σ).symm

/-- The actual labelled-family rank is the rank of its native coefficient tensor. -/
theorem finrank_labelledTateLocalSystem_eq_coefficientTensor (σ : F →ₐ[ℚ] L) :
    letI : Module (ℚ_[p] ⊗[ℚ] F) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] F) L := (coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
    Module.finrank L ((labelledTateLocalSystem K A p L F φ hL σ).obj
      (Scheme.etaleFiberPoint K S x)) =
        Module.finrank L (L ⊗[ℚ_[p] ⊗[ℚ] F] rationalTate K (fiber K A x).X p) :=
  (labelledTateLocalSystemCoefficientTensorEquiv K A x p F φ L hL σ).toLinearEquiv.finrank_eq

end AlgebraicGeometry.GroupScheme
