/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientTensorFactor
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficients

/-! # Completed coefficients and the native labelled Tate tensor

The canonical isomorphism from the rational coefficient tensor algebra to its
ramified completion identifies the actual labelled Tate tensor with scalar
extension of the native completed-coefficient Tate representation. This gives
the dimension comparison needed in [TripathiGoswami, coefficient-label lemma]
without exporting a basis of the chosen geometric family.
-/

@[expose] public noncomputable section
open CategoryTheory Algebra.TensorProduct HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj NumberField TensorProduct
namespace AlgebraicGeometry.GroupScheme
universe u
variable (p k : ℕ) [Fact p.Prime]
  (L : Type u) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  (τ : RealPrimePowerCompletion p k →ₐ[ℚ_[p]] L)

/-- A local coefficient embedding restricts to the corresponding global multiplication label. -/
def localTateCoefficientLabel : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] L :=
  (τ.restrictScalars ℚ).comp
    (Algebra.algHom ℚ (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k))

/-- Evaluating the original coefficient tensor is the actual completion map followed by its embedding. -/
theorem localTateCoefficientLabel_tensor :
    coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField (p ^ (k + 1))) L
      (localTateCoefficientLabel p k L τ) =
        τ.comp (realPrimePowerCompletionTensorEquiv p k).toAlgHom := by
  ext f
  change coefficientTensorEmbedding ℚ ℚ_[p] _ L (localTateCoefficientLabel p k L τ)
      ((1 : ℚ_[p]) ⊗ₜ[ℚ] f) =
    τ (realPrimePowerCompletionTensorEquiv p k ((1 : ℚ_[p]) ⊗ₜ[ℚ] f))
  simp [coefficientTensorEmbedding_tmul, localTateCoefficientLabel]
  rfl

variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S)
  (φ : 𝓞 (realCyclotomicField (p ^ (k + 1))) →+* End A)

set_option maxHeartbeats 1000000 in
/-- The native tensor over the completed coefficient field is the tensor over the original coefficient algebra. -/
def localCoefficientTateTensorEquiv :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    letI : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1)))
        (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (fiberTensorTateAction K A x p _ φ).toRingHom
    letI : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
    letI : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1))) L :=
      (coefficientTensorEmbedding ℚ ℚ_[p] _ L (localTateCoefficientLabel p k L τ)).toAlgebra
    (L ⊗[RealPrimePowerCompletion p k] rationalTate K (fiber K A x).X p) ≃ₗ[L]
      (L ⊗[ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1))] rationalTate K (fiber K A x).X p) := by
  let F := realCyclotomicField (p ^ (k + 1))
  let C := RealPrimePowerCompletion p k
  let W := rationalTate K (fiber K A x).X p
  letI : Module C W := Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
  letI : Module (ℚ_[p] ⊗[ℚ] F) W := Module.compHom _ (fiberTensorTateAction K A x p F φ).toRingHom
  letI : Algebra C L := τ.toAlgebra
  letI : Algebra (ℚ_[p] ⊗[ℚ] F) L :=
    (coefficientTensorEmbedding ℚ ℚ_[p] F L (localTateCoefficientLabel p k L τ)).toAlgebra
  letI : Algebra (ℚ_[p] ⊗[ℚ] F) C := (realPrimePowerCompletionTensorEquiv p k).toAlgHom.toAlgebra
  letI : IsScalarTower (ℚ_[p] ⊗[ℚ] F) C L := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact AlgHom.congr_fun (localTateCoefficientLabel_tensor p k L τ) a)
  letI : IsScalarTower (ℚ_[p] ⊗[ℚ] F) C W := IsScalarTower.of_algebraMap_smul (by
    intro a v
    change localCoefficientTateAction K A x p k φ (realPrimePowerCompletionTensorEquiv p k a) v =
      fiberTensorTateAction K A x p F φ a v
    change fiberTensorTateAction K A x p F φ
      ((realPrimePowerCompletionTensorEquiv p k).symm (realPrimePowerCompletionTensorEquiv p k a)) v = _
    rw [AlgEquiv.symm_apply_apply])
  letI : TensorProduct.CompatibleSMul (ℚ_[p] ⊗[ℚ] F) C L W :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective L W
      (realPrimePowerCompletionTensorEquiv p k).surjective
  exact TensorProduct.equivOfCompatibleSMul (ℚ_[p] ⊗[ℚ] F) C L L W

/-- Changing from the coefficient tensor algebra to its completion preserves pure tensors. -/
@[simp] theorem localCoefficientTateTensorEquiv_tmul
    (l : L) (v : rationalTate K (fiber K A x).X p) :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    letI : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1)))
        (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (fiberTensorTateAction K A x p _ φ).toRingHom
    letI : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
    letI : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1))) L :=
      (coefficientTensorEmbedding ℚ ℚ_[p] _ L (localTateCoefficientLabel p k L τ)).toAlgebra
    localCoefficientTateTensorEquiv p k L τ K A x φ
      (l ⊗ₜ[RealPrimePowerCompletion p k] v) =
      l ⊗ₜ[ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1))] v := rfl

variable (hL : ∀ a : realCyclotomicField (p ^ (k + 1)),
  ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

set_option maxHeartbeats 1000000 in
/-- Scalar extension of the actual native completion module is the actual embedding-labelled Tate summand. -/
def localCoefficientLabelledTateEquiv :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    letI : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
    (L ⊗[RealPrimePowerCompletion p k] rationalTate K (fiber K A x).X p) ≃ₗ[L]
      labelledTateSummand K (fiber K A x).X p (realCyclotomicField (p ^ (k + 1))) L hL
        (fiberPointsAction K (AlgebraicClosure K) A x _ φ) (localTateCoefficientLabel p k L τ) := by
  letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
  letI : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1)))
      (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (fiberTensorTateAction K A x p _ φ).toRingHom
  letI : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
  letI : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1))) L :=
    (coefficientTensorEmbedding ℚ ℚ_[p] _ L (localTateCoefficientLabel p k L τ)).toAlgebra
  exact (localCoefficientTateTensorEquiv p k L τ K A x φ).trans
    (fiberCoefficientTensorTateEquiv K A x p _ φ L hL (localTateCoefficientLabel p k L τ))

/-- The completed-coefficient comparison still sends pure tensors to the actual labelled projector. -/
@[simp] theorem localCoefficientLabelledTateEquiv_tmul
    (l : L) (v : rationalTate K (fiber K A x).X p) :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    letI : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
    (localCoefficientLabelledTateEquiv p k L τ K A x φ hL
      (l ⊗ₜ[RealPrimePowerCompletion p k] v) : L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) =
      labelledTateProjection K (fiber K A x).X p (realCyclotomicField (p ^ (k + 1))) L hL
        (fiberPointsAction K (AlgebraicClosure K) A x _ φ) (localTateCoefficientLabel p k L τ)
        (l ⊗ₜ[ℚ_[p]] v) := by
  let : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
  let : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
  exact fiberCoefficientTensorTateEquiv_tmul K A x p _ φ L hL
    (localTateCoefficientLabel p k L τ) l v

set_option maxHeartbeats 1000000 in
/-- The actual native completed-coefficient representation extends to the actual labelled Tate representation. -/
def localCoefficientLabelledTateRepresentationEquiv :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    letI : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
    ((localCoefficientTateRepresentation K A x p k φ).baseChange L).Equiv
      (labelledTateSubrepresentation K (fiber K A x).X p (realCyclotomicField (p ^ (k + 1))) L hL
        (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
        (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ)
        (localTateCoefficientLabel p k L τ)).toRepresentation := by
  letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
  letI : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
  refine .mk (localCoefficientLabelledTateEquiv p k L τ K A x φ hL) ?_
  intro g
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  induction w using TensorProduct.inductionOn with
  | add w z hw hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hw hz
  | tmul l v =>
    change (localCoefficientLabelledTateEquiv p k L τ K A x φ hL
        (((localCoefficientTateRepresentation K A x p k φ).baseChange L) g
          (l ⊗ₜ[RealPrimePowerCompletion p k] v)) : L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) =
      (tateRepresentation K (fiber K A x).X p).baseChange L g
        (localCoefficientLabelledTateEquiv p k L τ K A x φ hL
          (l ⊗ₜ[RealPrimePowerCompletion p k] v) : L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p)
    rw [Representation.baseChange_tmul, localCoefficientTateRepresentation_apply,
      localCoefficientLabelledTateEquiv_tmul, localCoefficientLabelledTateEquiv_tmul]
    exact LinearMap.congr_fun
      (tensorTateAction_commute K (fiber K A x).X p _ L
        (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
        (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ) g
        (embeddingIdempotent ℚ _ L hL (localTateCoefficientLabel p k L τ))) (l ⊗ₜ[ℚ_[p]] v)

/-- The dimension of the actual labelled Tate summand equals the native completed-coefficient dimension. -/
theorem finrank_labelledTateSummand_eq_localCoefficientTateRep :
    Module.finrank L (labelledTateSummand K (fiber K A x).X p
      (realCyclotomicField (p ^ (k + 1))) L hL
      (fiberPointsAction K (AlgebraicClosure K) A x _ φ) (localTateCoefficientLabel p k L τ)) =
        Module.finrank (RealPrimePowerCompletion p k) (localCoefficientTateRep K A x p k φ) := by
  let : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
  let : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
  rw [← (localCoefficientLabelledTateEquiv p k L τ K A x φ hL).finrank_eq,
    Module.finrank_baseChange]
  rfl

variable [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

set_option maxHeartbeats 1000000 in
/-- The same labelled family has the scalar extension of the native completion representation as its arithmetic fibre. -/
def labelledTateLocalSystemLocalCoefficientEquiv :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    letI : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
    (Scheme.arithmeticFiberRepresentation K S
      (labelledTateLocalSystem K A p L _ φ hL (localTateCoefficientLabel p k L τ)) x).Equiv
      ((localCoefficientTateRepresentation K A x p k φ).baseChange L) := by
  letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
  letI : Algebra (RealPrimePowerCompletion p k) L := τ.toAlgebra
  exact (labelledTateLocalSystem_arithmeticEquiv K A p L x _ φ hL
    (localTateCoefficientLabel p k L τ)).trans
      (localCoefficientLabelledTateRepresentationEquiv p k L τ K A x φ hL).symm

/-- The rank of the actual labelled family fibre is the native completed-coefficient Tate rank. -/
theorem finrank_labelledTateLocalSystem_eq_localCoefficientTateRep :
    Module.finrank L ((labelledTateLocalSystem K A p L _ φ hL
      (localTateCoefficientLabel p k L τ)).obj (Scheme.etaleFiberPoint K S x)) =
        Module.finrank (RealPrimePowerCompletion p k) (localCoefficientTateRep K A x p k φ) :=
  (labelledTateLocalSystemArithmeticFiberIso K A p L x _ φ hL
    (localTateCoefficientLabel p k L τ)).toLinearEquiv.finrank_eq.trans
      (finrank_labelledTateSummand_eq_localCoefficientTateRep p k L τ K A x φ hL)

end AlgebraicGeometry.GroupScheme
