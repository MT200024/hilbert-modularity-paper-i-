/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientRank

/-! # Bases of the actual coefficient-labelled Tate fibres

The original coefficient-algebra basis induces bases of the actual labelled
Tate summands. Their vectors are the original basis vectors, transported to the
scheme-theoretic fibre, scalar-extended and projected by the same coefficient
idempotents. This refines the coefficient-label construction in
[TripathiGoswami, coefficient-label lemma].
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
  (x : Spec (CommRingCat.of K) ⟶ S)
  (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

set_option maxHeartbeats 1000000 in
/-- The original geometric coefficient basis induces a basis of each actual labelled
Tate summand, using the original scheme-induced coefficient action. -/
def labelledTateBasisOfGeometricBasis {I : Type*} [Fintype I] :
    letI : Module (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
      Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
    Module.Basis I (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) →
      (σ : F →ₐ[ℚ] L) → Module.Basis I L
        (labelledTateSummand K (fiber K A x).X p F L hL
          (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ) := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let W := rationalTate K (fiber K A x).X p
  letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
  letI : IsScalarTower ℚ_[p] (ℚ_[p] ⊗[ℚ] F) W :=
    fiberTensorTateAction_scalarTower K A p F φ x
  intro b σ
  refine (Algebra.TensorProduct.coefficientScalarExtensionProjectionBasis ℚ ℚ_[p] F L W
    (b.map (coefficientRationalGeometricFiberTateEquiv K A p F φ x)) hL σ).map
      (LinearEquiv.ofEq _ _ ?_)
  rw [fiberCoefficientScalarExtensionAction_eq K A p L F φ x]
  rfl

set_option maxHeartbeats 1000000 in
/-- Labelled basis vectors are the actual idempotent projections of the original vectors. -/
@[simp] theorem labelledTateBasisOfGeometricBasis_coe {I : Type*} [Fintype I] :
    letI : Module (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
      Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
    ∀ (b : Module.Basis I (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))))
      (σ : F →ₐ[ℚ] L) (i : I),
      (labelledTateBasisOfGeometricBasis K A p L F φ x hL b σ i :
        L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) =
      labelledTateProjection K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ
        ((1 : L) ⊗ₜ[ℚ_[p]] rationalGeometricFiberTateEquiv K A x p (b i)) := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let W := rationalTate K (fiber K A x).X p
  let : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  let : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
  let : IsScalarTower ℚ_[p] (ℚ_[p] ⊗[ℚ] F) W :=
    fiberTensorTateAction_scalarTower K A p F φ x
  intro b σ i
  change (Algebra.TensorProduct.coefficientScalarExtensionProjectionBasis ℚ ℚ_[p] F L W
    (b.map (coefficientRationalGeometricFiberTateEquiv K A p F φ x)) hL σ i : L ⊗[ℚ_[p]] W) = _
  rw [Algebra.TensorProduct.coefficientScalarExtensionProjectionBasis_coe,
    fiberCoefficientScalarExtensionAction_eq K A p L F φ x]
  rfl

set_option maxHeartbeats 1000000 in
/-- The same basis gives coordinates on the actual labelled local-system fibre, through
its equivariant comparison with the native labelled Tate summand. -/
def labelledTateLocalSystemBasisOfGeometricBasis {I : Type*} [Fintype I] :
    letI : Module (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
      Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
    Module.Basis I (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) →
      (σ : F →ₐ[ℚ] L) → Module.Basis I L
        ((labelledTateLocalSystem K A p L F φ hL σ).obj (Scheme.etaleFiberPoint K S x)) := by
  letI : Module (ℚ_[p] ⊗[ℚ] F)
      (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
    Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
  intro b σ
  exact (labelledTateBasisOfGeometricBasis K A p L F φ x hL b σ).map
    (labelledTateLocalSystemArithmeticFiberIso K A p L x F φ hL σ).toLinearEquiv.symm

set_option maxHeartbeats 1000000 in
/-- Arithmetic fibre comparison identifies the two bases vector by vector. -/
@[simp] theorem labelledTateLocalSystemBasisOfGeometricBasis_arithmetic {I : Type*} [Fintype I] :
    letI : Module (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
      Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
    ∀ (b : Module.Basis I (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))))
      (σ : F →ₐ[ℚ] L) (i : I),
      (labelledTateLocalSystemArithmeticFiberIso K A p L x F φ hL σ).hom
        (labelledTateLocalSystemBasisOfGeometricBasis K A p L F φ x hL b σ i) =
      labelledTateBasisOfGeometricBasis K A p L F φ x hL b σ i := by
  let : Module (ℚ_[p] ⊗[ℚ] F)
      (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
    Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
  intro b σ i
  exact (labelledTateLocalSystemArithmeticFiberIso K A p L x F φ hL σ).toLinearEquiv.apply_symm_apply _

set_option maxHeartbeats 1000000 in
/-- Inclusion of the labelled-family basis agrees with the original native projector formula. -/
theorem labelledTateLocalSystemBasisOfGeometricBasis_native {I : Type*} [Fintype I] :
    letI : Module (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
      Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
    ∀ (b : Module.Basis I (ℚ_[p] ⊗[ℚ] F)
        (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))))
      (σ : F →ₐ[ℚ] L) (i : I),
      (nativeExtendedGeometricFiberTateIso K A p L x).hom
        (((labelledTateLocalSystemInclusion K A p L F φ hL σ).app
          (Scheme.etaleFiberPoint K S x)).hom
          (labelledTateLocalSystemBasisOfGeometricBasis K A p L F φ x hL b σ i)) =
      labelledTateProjection K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ
        ((1 : L) ⊗ₜ[ℚ_[p]] rationalGeometricFiberTateEquiv K A x p (b i)) := by
  let : Module (ℚ_[p] ⊗[ℚ] F)
      (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
    Module.compHom _ (geometricTensorTateAction K A p F φ x).toRingHom
  intro b σ i
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (labelledTateLocalSystemArithmeticFiberIso_hom_subtype K A p L x F φ hL σ))
    (labelledTateLocalSystemBasisOfGeometricBasis K A p L F φ x hL b σ i)
  change (((labelledTateLocalSystemArithmeticFiberIso K A p L x F φ hL σ).hom
      (labelledTateLocalSystemBasisOfGeometricBasis K A p L F φ x hL b σ i)) :
      L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) = _ at h
  rw [labelledTateLocalSystemBasisOfGeometricBasis_arithmetic] at h
  exact h.symm.trans (labelledTateBasisOfGeometricBasis_coe K A p L F φ x hL b σ i)

end AlgebraicGeometry.GroupScheme
