/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateGeometricPathCoefficients
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.ScalarExtensionFiber
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Coefficient-labelled Tate fibres along geometric paths

The path on the actual Tate modules preserves the original endomorphisms.
It therefore preserves the primitive projectors of the split coefficient
algebra and identifies the same embedding-labelled factors.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra ChangeOfRings
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (C : Type u) [Field C] [Algebra ℚ_[p] C]

/-- The actual rational Tate path, expressed as an isomorphism of family fibres. -/
def rationalTateGeometricPathIso :
    (rationalTateLocalSystem K A p).obj (Scheme.etaleFiberPoint K S x) ≅
      (rationalTateLocalSystem L A p).obj (Scheme.etaleFiberPoint L S y) :=
  (rationalTateGeometricPathEquiv K L e A p).toModuleIso

/-- The same geometric path after extension to a common coefficient field. -/
abbrev extendedTateGeometricPathIso :
    (extendedTateLocalSystem K A p C).obj (Scheme.etaleFiberPoint K S x) ≅
      (extendedTateLocalSystem L A p C).obj (Scheme.etaleFiberPoint L S y) :=
  (ModuleCat.extendScalars (algebraMap ℚ_[p] C)).mapIso (rationalTateGeometricPathIso K L e A p)

set_option maxHeartbeats 1000000 in
/-- Scalar-extended path transport retains every original group-scheme endomorphism. -/
theorem extendedTateGeometricPathIso_endomorphism (f : End A) :
    ((extendedTateLocalSystemEndomorphism K A p C (rationalTateLocalSystemMap K p f)).app
        (Scheme.etaleFiberPoint K S x)) ≫ (extendedTateGeometricPathIso K L e A p C).hom =
      (extendedTateGeometricPathIso K L e A p C).hom ≫
        ((extendedTateLocalSystemEndomorphism L A p C (rationalTateLocalSystemMap L p f)).app
          (Scheme.etaleFiberPoint L S y)) := by
  let E := rationalTateGeometricPathIso K L e A p
  let T := ModuleCat.extendScalars (algebraMap ℚ_[p] C)
  have h : (rationalTateLocalSystemMap K p f).app (Scheme.etaleFiberPoint K S x) ≫ E.hom =
      E.hom ≫ (rationalTateLocalSystemMap L p f).app (Scheme.etaleFiberPoint L S y) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change rationalTateGeometricPathEquiv K L e A p
      (((rationalTateLocalSystemMap K p f).app (Scheme.etaleFiberPoint K S x)).hom v) =
      ((rationalTateLocalSystemMap L p f).app (Scheme.etaleFiberPoint L S y)).hom
        (rationalTateGeometricPathEquiv K L e A p v)
    exact (congrArg (rationalTateGeometricPathEquiv K L e A p)
      (rationalTateLocalSystemMap_app_apply K p f x v)).trans
        ((LinearMap.congr_fun (rationalTateGeometricPathEquiv_natural K L e p f) v).trans
          (rationalTateLocalSystemMap_app_apply L p f y
            (rationalTateGeometricPathEquiv K L e A p v)).symm)
  rw [extendedTateLocalSystemEndomorphism_app, extendedTateLocalSystemEndomorphism_app]
  change T.map _ ≫ T.map E.hom = T.map E.hom ≫ T.map _
  exact (T.map_comp _ _).symm.trans ((congrArg T.map h).trans (T.map_comp _ _))

variable (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ C]

set_option maxHeartbeats 1000000 in
/-- Geometric Tate paths preserve the full split coefficient algebra. -/
theorem extendedTateGeometricPathIso_coefficients (a : C ⊗[ℚ] F)
    (v : (extendedTateLocalSystem K A p C).obj (Scheme.etaleFiberPoint K S x)) :
    (extendedTateGeometricPathIso K L e A p C).hom.hom
        (((extendedTensorTateLocalSystemAction K A p C F φ a).app
          (Scheme.etaleFiberPoint K S x)).hom v) =
      ((extendedTensorTateLocalSystemAction L A p C F φ a).app
        (Scheme.etaleFiberPoint L S y)).hom
        ((extendedTateGeometricPathIso K L e A p C).hom.hom v) := by
  rw [extendedTensorTateLocalSystemAction_app, extendedTensorTateLocalSystemAction_app]
  apply NumberField.RingOfIntegers.tensorExtension_intertwines F _ _
    (extendedTateGeometricPathIso K L e A p C).hom.hom
  intro c w
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (extendedTateGeometricPathIso_endomorphism K L e A p C (φ c))) w

variable (hC : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ C)).Splits)

set_option maxHeartbeats 1000000 in
/-- The geometric path carries each coefficient projector range to the same labelled range. -/
theorem extendedTateGeometricPathIso_map_labelledRange (τ : F →ₐ[ℚ] C) :
    (LinearMap.range ((labelledTateLocalSystemProjection K A p C F φ hC τ).app
      (Scheme.etaleFiberPoint K S x)).hom).map (extendedTateGeometricPathIso K L e A p C).hom.hom =
      LinearMap.range ((labelledTateLocalSystemProjection L A p C F φ hC τ).app
        (Scheme.etaleFiberPoint L S y)).hom := by
  have h : (extendedTateGeometricPathIso K L e A p C).hom.hom.comp
        ((labelledTateLocalSystemProjection K A p C F φ hC τ).app
          (Scheme.etaleFiberPoint K S x)).hom =
      (((labelledTateLocalSystemProjection L A p C F φ hC τ).app
        (Scheme.etaleFiberPoint L S y)).hom).comp
          (extendedTateGeometricPathIso K L e A p C).hom.hom := by
    apply LinearMap.ext
    intro v
    exact extendedTateGeometricPathIso_coefficients K L e A p C F φ
      (Algebra.TensorProduct.embeddingIdempotent ℚ F C hC τ) v
  rw [← LinearMap.range_comp, h]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (extendedTateGeometricPathIso K L e A p C).toLinearEquiv)

set_option maxHeartbeats 1000000 in
/-- One actual geometric path identifies the embedding-labelled Tate factors over different fields. -/
def labelledTateGeometricPathIso (τ : F →ₐ[ℚ] C) :
    (labelledTateLocalSystem K A p C F φ hC τ).obj (Scheme.etaleFiberPoint K S x) ≅
      (labelledTateLocalSystem L A p C F φ hC τ).obj (Scheme.etaleFiberPoint L S y) :=
  labelledTateLocalSystemFiberIso K A p C F φ hC τ (Scheme.etaleFiberPoint K S x) ≪≫
    ((extendedTateGeometricPathIso K L e A p C).toLinearEquiv.ofSubmodules _ _
      (extendedTateGeometricPathIso_map_labelledRange K L e A p C F φ hC τ)).toModuleIso ≪≫
    (labelledTateLocalSystemFiberIso L A p C F φ hC τ (Scheme.etaleFiberPoint L S y)).symm

set_option maxHeartbeats 1000000 in
/-- The labelled path is the restriction of the ambient geometric Tate path. -/
@[reassoc] theorem labelledTateGeometricPathIso_hom_inclusion (τ : F →ₐ[ℚ] C) :
    (labelledTateGeometricPathIso K L e A p C F φ hC τ).hom ≫
        (labelledTateLocalSystemInclusion L A p C F φ hC τ).app (Scheme.etaleFiberPoint L S y) =
      (labelledTateLocalSystemInclusion K A p C F φ hC τ).app (Scheme.etaleFiberPoint K S x) ≫
        (extendedTateGeometricPathIso K L e A p C).hom := by
  dsimp only [labelledTateLocalSystemInclusion]
  rw [← labelledTateLocalSystemFiberIso_hom_subtype L A p C F φ hC τ,
    ← labelledTateLocalSystemFiberIso_hom_subtype K A p C F φ hC τ]
  dsimp only [labelledTateGeometricPathIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rfl

end AlgebraicGeometry.GroupScheme
