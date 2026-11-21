/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.CoefficientScalarExtension
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientPaths
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LabelledFiber

/-! # Coefficient ranks of the actual labelled Tate family

A coefficient-algebra basis of the native geometric Tate module gives the
same dimension at every embedding-labelled image of the scalar-extended
family. The coefficient action throughout is induced by the original scheme
endomorphisms, as in [TripathiGoswami, coefficient-label lemma].
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra ChangeOfRings
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
  (x : Spec (CommRingCat.of K) ⟶ S)

set_option maxHeartbeats 1000000 in
/-- The actual geometric-to-arithmetic fibre comparison is linear over the original
coefficient tensor algebra induced by the scheme endomorphisms. -/
def coefficientRationalGeometricFiberTateEquiv :
    let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    let W := rationalTate K (fiber K A x).X p
    letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
      Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
    letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
      Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
    V ≃ₗ[ℚ_[p] ⊗[ℚ] F] W := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let W := rationalTate K (fiber K A x).X p
  letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
  refine { (rationalGeometricFiberTateEquiv K A x p).toLinearEquiv.toAddEquiv with
    map_smul' := ?_ }
  intro a v
  exact rationalGeometricFiberTateEquiv_tensorCoefficients K A p F φ x a v

/-- Coefficient-linear fibre comparison has the original map on Tate vectors. -/
@[simp] theorem coefficientRationalGeometricFiberTateEquiv_apply
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    coefficientRationalGeometricFiberTateEquiv K A p F φ x v =
      rationalGeometricFiberTateEquiv K A x p v := rfl

omit [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left] in
set_option maxHeartbeats 1000000 in
/-- The actual fibre coefficient action extends its original rational Tate scalars. -/
theorem fiberTensorTateAction_scalarTower :
    let W := rationalTate K (fiber K A x).X p
    letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
      Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
    IsScalarTower ℚ_[p] (ℚ_[p] ⊗[ℚ] F) W := by
  let W := rationalTate K (fiber K A x).X p
  let : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
  apply IsScalarTower.of_algebraMap_smul
  intro c v
  change fiberTensorTateAction K A x p F φ (algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] F) c) v = c • v
  rw [(fiberTensorTateAction K A x p F φ).commutes]
  rfl

omit [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left] in
set_option maxHeartbeats 1000000 in
/-- Scalar-extending the native fibre coefficient action gives exactly the previously
constructed scheme-induced action on its extended Tate module. -/
theorem fiberCoefficientScalarExtensionAction_eq :
    let W := rationalTate K (fiber K A x).X p
    letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
      Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
    letI : IsScalarTower ℚ_[p] (ℚ_[p] ⊗[ℚ] F) W :=
      fiberTensorTateAction_scalarTower K A p F φ x
    Algebra.TensorProduct.coefficientScalarExtensionAction ℚ ℚ_[p] F L W =
      tensorTateAction K (fiber K A x).X p F L
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) := by
  let W := rationalTate K (fiber K A x).X p
  let : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
  let : IsScalarTower ℚ_[p] (ℚ_[p] ⊗[ℚ] F) W :=
    fiberTensorTateAction_scalarTower K A p F φ x
  refine NumberField.RingOfIntegers.tensorExtension_unique F
    (A := Module.End L (L ⊗[ℚ_[p]] W)) L
    (extendedIntegerTateAction K (fiber K A x).X p F L
      (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ))
    (Algebra.TensorProduct.coefficientScalarExtensionAction ℚ ℚ_[p] F L W) ?_
  intro c
  rw [Algebra.TensorProduct.coefficientScalarExtensionAction_compHom_tmul]
  exact congrArg (fun f : Module.End ℚ_[p] W => f.baseChange L)
    (NumberField.RingOfIntegers.tensorExtension_integer F ℚ_[p]
      (integerTateAction K (fiber K A x).X p F
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)) c)

variable (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

set_option maxHeartbeats 1000000 in
/-- A basis over the original coefficient algebra computes the dimension of each actual
embedding-idempotent Tate summand of the scheme-theoretic fibre. -/
theorem finrank_labelledTateSummand_of_geometricBasis {I : Type*} [Fintype I] :
    let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
      Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
    ∀ (_b : Module.Basis I (ℚ_[p] ⊗[ℚ] F) V) (σ : F →ₐ[ℚ] L),
      Module.finrank L (labelledTateSummand K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ) = Fintype.card I := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let W := rationalTate K (fiber K A x).X p
  let : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  let : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
  let : IsScalarTower ℚ_[p] (ℚ_[p] ⊗[ℚ] F) W :=
    fiberTensorTateAction_scalarTower K A p F φ x
  dsimp only
  intro b σ
  change Module.finrank L (LinearMap.range
    (tensorTateAction K (fiber K A x).X p F L
      (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
      (Algebra.TensorProduct.embeddingIdempotent ℚ F L hL σ))) = _
  rw [← fiberCoefficientScalarExtensionAction_eq K A p L F φ x]
  exact Algebra.TensorProduct.finrank_coefficientScalarExtensionProjection ℚ ℚ_[p] F L W
    (b.map (coefficientRationalGeometricFiberTateEquiv K A p F φ x)) hL σ

set_option maxHeartbeats 1000000 in
/-- The actual labelled local-system fibre has the same rank, through its previously
constructed equivariant arithmetic fibre comparison. -/
theorem finrank_labelledTateLocalSystem_obj {I : Type*} [Fintype I] :
    let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
      Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
    ∀ (_b : Module.Basis I (ℚ_[p] ⊗[ℚ] F) V) (σ : F →ₐ[ℚ] L),
      Module.finrank L ((labelledTateLocalSystem K A p L F φ hL σ).obj
        (Scheme.etaleFiberPoint K S x)) = Fintype.card I := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  dsimp only
  intro b σ
  exact (labelledTateLocalSystemArithmeticFiberIso K A p L x F φ hL σ).toLinearEquiv.finrank_eq.trans
    (finrank_labelledTateSummand_of_geometricBasis K A p L F φ x hL b σ)

set_option maxHeartbeats 1000000 in
/-- A rank-two basis of the original geometric coefficient module gives dimension two in
every actual embedding-idempotent Tate summand of the same scheme-theoretic fibre. -/
theorem finrank_labelledTateSummand_eq_two :
    let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
      Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
    ∀ (_b : Module.Basis (Fin 2) (ℚ_[p] ⊗[ℚ] F) V) (σ : F →ₐ[ℚ] L),
      Module.finrank L (labelledTateSummand K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ) = 2 := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  dsimp only
  intro b σ
  simpa only [Fintype.card_fin] using
    finrank_labelledTateSummand_of_geometricBasis K A p L F φ x hL b σ

set_option maxHeartbeats 1000000 in
/-- A coefficient basis at one actual geometric fibre computes the ranks at every fibre
connected to it by an actual geometric path. -/
theorem finrank_labelledTateLocalSystem_obj_of_path
    (E : Type u) [Field E] (y : Spec (CommRingCat.of E) ⟶ S)
    (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor E y)
    {I : Type*} [Fintype I] :
    letI : Module (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
      Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
    ∀ (_b : Module.Basis I (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))))
      (σ : F →ₐ[ℚ] L),
      Module.finrank L ((labelledTateLocalSystem E A p L F φ hL σ).obj
        (Scheme.etaleFiberPoint E S y)) = Fintype.card I := by
  let : Module (ℚ_[p] ⊗[ℚ] F)
      (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
    Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
  let : Module (ℚ_[p] ⊗[ℚ] F)
      (TateModule.rational p (Additive (Scheme.geometricPointOver E y ⟶ A.X))) :=
    Module.compHom _ (geometricTensorTateAction E A p F φ y).toRingHom
  intro b σ
  exact finrank_labelledTateLocalSystem_obj E A p L F φ y hL
    (b.map (coefficientTateGeometricPathEquiv K E e A p F φ)) σ

end AlgebraicGeometry.GroupScheme
