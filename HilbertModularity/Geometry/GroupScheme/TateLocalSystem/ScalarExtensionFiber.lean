/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.Category.ModuleCat.ScalarExtension
public import HilbertModularity.Algebra.Category.ModuleCat.FunctorCategory
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientFiber
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientDecomposition

/-! # Arithmetic fibres after extending Tate coefficients -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra ChangeOfRings
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [Field L] [Algebra ℚ_[p] L]
  (x : Spec (CommRingCat.of K) ⟶ S)

set_option maxHeartbeats 1000000 in
/-- Coefficient extension preserves the comparison with the actual scheme-theoretic fibre. -/
def extendedGeometricFiberTateIso :
    (extendedTateLocalSystem K A p L).obj (Scheme.etaleFiberPoint K S x) ≅
      (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).obj
        (ModuleCat.of ℚ_[p] (rationalTate K (fiber K A x).X p)) :=
  (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).mapIso
    (rationalGeometricFiberTateEquiv K A x p).toLinearEquiv.toModuleIso

set_option maxHeartbeats 1000000 in
/-- The extended comparison map is the scalar extension of the original fibre comparison. -/
@[simp]
theorem extendedGeometricFiberTateIso_hom :
    (extendedGeometricFiberTateIso K A p L x).hom =
      (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map
        (rationalGeometricFiberTateEquiv K A x p).toLinearEquiv.toModuleIso.hom := rfl

set_option maxHeartbeats 1000000 in
/-- Extended fibre comparison fixes the new coefficient tensorand. -/
@[simp]
theorem extendedGeometricFiberTateIso_tmul (c : L)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    (extendedGeometricFiberTateIso K A p L x).hom
        (c ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L] v) =
      c ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L] (rationalGeometricFiberTateEquiv K A x p v) :=
  ModuleCat.ExtendScalars.map_tmul _ _ _ _

set_option maxHeartbeats 1000000 in
/-- Extended arithmetic comparison takes values in the native tensor product of the actual fibre. -/
def nativeExtendedGeometricFiberTateIso :
    (extendedTateLocalSystem K A p L).obj (Scheme.etaleFiberPoint K S x) ≅
      ModuleCat.of L (L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) :=
  extendedGeometricFiberTateIso K A p L x ≪≫
    ModuleCat.extendScalarsTensorIso ℚ_[p] L
      (ModuleCat.of ℚ_[p] (rationalTate K (fiber K A x).X p))

set_option maxHeartbeats 1000000 in
/-- The native extended comparison sends a pure tensor to the same coefficient and fibre vector. -/
@[simp]
theorem nativeExtendedGeometricFiberTateIso_tmul (c : L)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    (nativeExtendedGeometricFiberTateIso K A p L x).hom
        (c ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L] v) =
      c ⊗ₜ[ℚ_[p]] (rationalGeometricFiberTateEquiv K A x p v) := by
  change (ModuleCat.extendScalarsTensorIso ℚ_[p] L
      (ModuleCat.of ℚ_[p] (rationalTate K (fiber K A x).X p))).hom
        ((extendedGeometricFiberTateIso K A p L x).hom
          (c ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L] v)) = _
  rw [extendedGeometricFiberTateIso_tmul]
  exact ModuleCat.extendScalarsTensorIso_tmul ℚ_[p] L
    (ModuleCat.of ℚ_[p] (rationalTate K (fiber K A x).X p)) c
    (rationalGeometricFiberTateEquiv K A x p v)

set_option maxHeartbeats 1000000 in
/-- The native extended comparison is the original comparison followed by the canonical tensor iso. -/
@[simp]
theorem nativeExtendedGeometricFiberTateIso_hom :
    (nativeExtendedGeometricFiberTateIso K A p L x).hom =
      (extendedGeometricFiberTateIso K A p L x).hom ≫
        (ModuleCat.extendScalarsTensorIso ℚ_[p] L
          (ModuleCat.of ℚ_[p] (rationalTate K (fiber K A x).X p))).hom := rfl


set_option maxHeartbeats 1000000 in
/-- The native extended fibre comparison intertwines the actual arithmetic loops. -/
theorem nativeExtendedGeometricFiberTateIso_arithmetic
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (extendedTateLocalSystem K A p L).map (Scheme.arithmeticFiberLoop K S x g) ≫
        (nativeExtendedGeometricFiberTateIso K A p L x).hom =
      (nativeExtendedGeometricFiberTateIso K A p L x).hom ≫
        ModuleCat.ofHom ((tateRepresentation K (fiber K A x).X p).baseChange L g) := by
  let e := rationalGeometricFiberTateEquiv K A x p
  let T := ModuleCat.extendScalars (algebraMap ℚ_[p] L)
  have h : (rationalTateLocalSystem K A p).map (Scheme.arithmeticFiberLoop K S x g) ≫
      e.toLinearEquiv.toModuleIso.hom = e.toLinearEquiv.toModuleIso.hom ≫
        ModuleCat.ofHom (tateRepresentation K (fiber K A x).X p g) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    have h₁ := congrArg e (rationalTateLocalSystem_loop K A p x
      (Scheme.galoisToEtaleFundamentalGroup K x g) v)
    have h₂ := LinearMap.congr_fun (e.isIntertwining' g) v
    exact h₁.trans h₂
  have he : T.map ((rationalTateLocalSystem K A p).map
        (Scheme.arithmeticFiberLoop K S x g)) ≫
      (extendedGeometricFiberTateIso K A p L x).hom =
      (extendedGeometricFiberTateIso K A p L x).hom ≫
        T.map (ModuleCat.ofHom (tateRepresentation K (fiber K A x).X p g)) := by
    rw [extendedGeometricFiberTateIso_hom]
    exact (T.map_comp _ _).symm.trans ((congrArg T.map h).trans (T.map_comp _ _))
  let c := (ModuleCat.extendScalarsTensorIso ℚ_[p] L
    (ModuleCat.of ℚ_[p] (rationalTate K (fiber K A x).X p))).hom
  have hn := ModuleCat.extendScalarsTensorIso_naturality ℚ_[p] L
    (ModuleCat.of ℚ_[p] (rationalTate K (fiber K A x).X p))
    (ModuleCat.ofHom (tateRepresentation K (fiber K A x).X p g))
  rw [nativeExtendedGeometricFiberTateIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ c) he).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => (extendedGeometricFiberTateIso K A p L x).hom ≫ f) hn).trans
          (Category.assoc _ _ _).symm)))

set_option maxHeartbeats 1000000 in
/-- Arithmetic specialization of the extended single family is the scalar-extended native Tate representation. -/
def extendedTateLocalSystem_arithmeticEquiv :
    Representation.Equiv
      (Scheme.arithmeticFiberRepresentation K S (extendedTateLocalSystem K A p L) x)
      ((tateRepresentation K (fiber K A x).X p).baseChange L) :=
  .mk (nativeExtendedGeometricFiberTateIso K A p L x).toLinearEquiv (by
    intro g
    exact congrArg ModuleCat.Hom.hom
      (nativeExtendedGeometricFiberTateIso_arithmetic K A p L x g))

variable (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ L]

set_option maxHeartbeats 1000000 in
/-- The extended comparison intertwines the original integral coefficient endomorphisms. -/
theorem extendedGeometricFiberTateIso_integer (a : 𝓞 F) :
    ((extendedTensorTateLocalSystemAction K A p L F φ ((1 : L) ⊗ₜ[ℚ] (a : F))).app
        (Scheme.etaleFiberPoint K S x)) ≫ (extendedGeometricFiberTateIso K A p L x).hom =
      (extendedGeometricFiberTateIso K A p L x).hom ≫
        (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map
          (ModuleCat.ofHom (fiberNumberFieldTateAction K A x p F φ (a : F))) := by
  have h : ((numberFieldTateLocalSystemAction K A p F φ (a : F)).app
        (Scheme.etaleFiberPoint K S x)) ≫
        (rationalGeometricFiberTateEquiv K A x p).toLinearEquiv.toModuleIso.hom =
      (rationalGeometricFiberTateEquiv K A x p).toLinearEquiv.toModuleIso.hom ≫
        ModuleCat.ofHom (fiberNumberFieldTateAction K A x p F φ (a : F)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    exact rationalGeometricFiberTateEquiv_integer K A p F φ x a v
  rw [numberFieldTateLocalSystemAction_integer] at h
  rw [extendedTensorTateLocalSystemAction_integer]
  have he := congrArg (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map h
  rw [extendedTateLocalSystemEndomorphism_app, extendedGeometricFiberTateIso_hom]
  exact ((ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map_comp _ _).symm.trans
    (he.trans ((ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map_comp _ _))

set_option maxHeartbeats 1000000 in
/-- Native arithmetic comparison intertwines integral coefficients after extending Tate scalars. -/
theorem nativeExtendedGeometricFiberTateIso_integer (a : 𝓞 F) :
    ((extendedTensorTateLocalSystemAction K A p L F φ ((1 : L) ⊗ₜ[ℚ] (a : F))).app
        (Scheme.etaleFiberPoint K S x)) ≫ (nativeExtendedGeometricFiberTateIso K A p L x).hom =
      (nativeExtendedGeometricFiberTateIso K A p L x).hom ≫
        ModuleCat.ofHom ((fiberNumberFieldTateAction K A x p F φ (a : F)).baseChange L) := by
  rw [nativeExtendedGeometricFiberTateIso_hom, ← Category.assoc,
    extendedGeometricFiberTateIso_integer, Category.assoc,
    ModuleCat.extendScalarsTensorIso_naturality, ← Category.assoc]

set_option maxHeartbeats 1000000 in
/-- Evaluating the whole tensor action gives the tensor extension of the evaluated integer action. -/
theorem extendedTensorTateLocalSystemAction_app (z : L ⊗[ℚ] F) :
    ((extendedTensorTateLocalSystemAction K A p L F φ z).app
      (Scheme.etaleFiberPoint K S x)).hom =
      NumberField.RingOfIntegers.tensorExtension F L
        ((ModuleCat.functorEndApp L (extendedTateLocalSystem K A p L)
          (Scheme.etaleFiberPoint K S x)).toRingHom.comp
          ((extendedTateLocalSystemEndomorphismMap K A p L).comp
            ((rationalTateLocalSystemEndomorphismMap K A p).comp φ))) z :=
  AlgHom.congr_fun (NumberField.RingOfIntegers.tensorExtension_comp F L _
    (ModuleCat.functorEndApp L (extendedTateLocalSystem K A p L)
      (Scheme.etaleFiberPoint K S x))) z

set_option maxHeartbeats 1000000 in
/-- The full split coefficient action specializes to the native action on the actual Tate fibre. -/
theorem nativeExtendedGeometricFiberTateIso_coefficients (z : L ⊗[ℚ] F)
    (v : (extendedTateLocalSystem K A p L).obj (Scheme.etaleFiberPoint K S x)) :
    (nativeExtendedGeometricFiberTateIso K A p L x).hom.hom
        (((extendedTensorTateLocalSystemAction K A p L F φ z).app
          (Scheme.etaleFiberPoint K S x)).hom v) =
      tensorTateAction K (fiber K A x).X p F L
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) z
          ((nativeExtendedGeometricFiberTateIso K A p L x).hom.hom v) := by
  let a := (ModuleCat.functorEndApp L (extendedTateLocalSystem K A p L)
    (Scheme.etaleFiberPoint K S x)).toRingHom.comp
      ((extendedTateLocalSystemEndomorphismMap K A p L).comp
        ((rationalTateLocalSystemEndomorphismMap K A p).comp φ))
  let b := extendedIntegerTateAction K (fiber K A x).X p F L
    (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
  let f := (nativeExtendedGeometricFiberTateIso K A p L x).hom.hom
  have ha (c : 𝓞 F) : a c =
      ((extendedTensorTateLocalSystemAction K A p L F φ ((1 : L) ⊗ₜ[ℚ] (c : F))).app
        (Scheme.etaleFiberPoint K S x)).hom := by
    rw [extendedTensorTateLocalSystemAction_integer]
    rfl
  have hb (c : 𝓞 F) : b c =
      (fiberNumberFieldTateAction K A x p F φ (c : F)).baseChange L := by
    rw [fiberNumberFieldTateAction_integer]
    rfl
  have hi : ∀ (c : 𝓞 F) (w : (extendedTateLocalSystem K A p L).obj
      (Scheme.etaleFiberPoint K S x)), f (a c w) = b c (f w) := by
    intro c w
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (nativeExtendedGeometricFiberTateIso_integer K A p L x F φ c)) w
    have h' : f (((extendedTensorTateLocalSystemAction K A p L F φ
          ((1 : L) ⊗ₜ[ℚ] (c : F))).app (Scheme.etaleFiberPoint K S x)).hom w) =
        (fiberNumberFieldTateAction K A x p F φ (c : F)).baseChange L (f w) := by
      simpa only [f, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] using h
    exact (congrArg f (LinearMap.congr_fun (ha c) w)).trans
      (h'.trans (LinearMap.congr_fun (hb c) (f w)).symm)
  have h₁ := LinearMap.congr_fun (extendedTensorTateLocalSystemAction_app K A p L x F φ z) v
  have h₂ := NumberField.RingOfIntegers.tensorExtension_intertwines F a b f hi z v
  exact (congrArg f h₁).trans h₂

end AlgebraicGeometry.GroupScheme
