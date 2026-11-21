/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.ScalarExtensionFiber
public import HilbertModularity.Geometry.TateModule.CoefficientDecomposition
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Labelled geometric fibres of the single Tate family

The coefficient comparison identifies each image family with the same embedding-labelled
Tate summand of the actual pullback fibre, following [TripathiGoswami].
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
  (L : Type u) [Field L] [Algebra ℚ_[p] L]
  (x : Spec (CommRingCat.of K) ⟶ S)

variable (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ L]

variable (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

set_option maxHeartbeats 1000000 in
/-- The native arithmetic comparison carries each family projector range to the same labelled Tate summand. -/
theorem nativeExtendedGeometricFiberTateIso_map_labelledRange (σ : F →ₐ[ℚ] L) :
    (LinearMap.range ((labelledTateLocalSystemProjection K A p L F φ hL σ).app
      (Scheme.etaleFiberPoint K S x)).hom).map
        (nativeExtendedGeometricFiberTateIso K A p L x).hom.hom =
      labelledTateSummand K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ := by
  have hc : (nativeExtendedGeometricFiberTateIso K A p L x).hom.hom.comp
        ((labelledTateLocalSystemProjection K A p L F φ hL σ).app
          (Scheme.etaleFiberPoint K S x)).hom =
      (labelledTateProjection K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ).comp
          (nativeExtendedGeometricFiberTateIso K A p L x).hom.hom := by
    apply LinearMap.ext
    intro v
    exact nativeExtendedGeometricFiberTateIso_coefficients K A p L x F φ
      (Algebra.TensorProduct.embeddingIdempotent ℚ F L hL σ) v
  rw [← LinearMap.range_comp, hc]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (nativeExtendedGeometricFiberTateIso K A p L x).toLinearEquiv)

set_option maxHeartbeats 1000000 in
/-- The fibre of a labelled family is canonically its native labelled geometric Tate module. -/
def labelledTateLocalSystemArithmeticFiberIso (σ : F →ₐ[ℚ] L) :
    (labelledTateLocalSystem K A p L F φ hL σ).obj (Scheme.etaleFiberPoint K S x) ≅
      ModuleCat.of L (labelledTateSummand K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ) :=
  labelledTateLocalSystemFiberIso K A p L F φ hL σ (Scheme.etaleFiberPoint K S x) ≪≫
    ((nativeExtendedGeometricFiberTateIso K A p L x).toLinearEquiv.ofSubmodules _ _
      (nativeExtendedGeometricFiberTateIso_map_labelledRange K A p L x F φ hL σ)).toModuleIso

set_option maxHeartbeats 1000000 in
/-- The labelled arithmetic comparison is the restriction of the ambient native fibre comparison. -/
@[reassoc]
theorem labelledTateLocalSystemArithmeticFiberIso_hom_subtype (σ : F →ₐ[ℚ] L) :
    (labelledTateLocalSystemArithmeticFiberIso K A p L x F φ hL σ).hom ≫
        ModuleCat.ofHom (labelledTateSummand K (fiber K A x).X p F L hL
          (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ).subtype =
      (CategoryTheory.Limits.image.ι (labelledTateLocalSystemProjection K A p L F φ hL σ)).app
        (Scheme.etaleFiberPoint K S x) ≫ (nativeExtendedGeometricFiberTateIso K A p L x).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (labelledTateLocalSystemFiberIso_hom_subtype K A p L F φ hL σ
      (Scheme.etaleFiberPoint K S x))) v
  exact congrArg (nativeExtendedGeometricFiberTateIso K A p L x).hom h

set_option maxHeartbeats 1000000 in
/-- Arithmetic specialization of each labelled family is its native labelled Tate subrepresentation. -/
def labelledTateLocalSystem_arithmeticEquiv (σ : F →ₐ[ℚ] L) :
    Representation.Equiv
      (Scheme.arithmeticFiberRepresentation K S (labelledTateLocalSystem K A p L F φ hL σ) x)
      (labelledTateSubrepresentation K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
        (fiberPointsAction_realized K (AlgebraicClosure K) A x (𝓞 F) φ) σ).toRepresentation := by
  let E := labelledTateLocalSystemArithmeticFiberIso K A p L x F φ hL σ
  let e := (nativeExtendedGeometricFiberTateIso K A p L x).hom.hom
  let i := CategoryTheory.Limits.image.ι (labelledTateLocalSystemProjection K A p L F φ hL σ)
  have hsub := labelledTateLocalSystemArithmeticFiberIso_hom_subtype K A p L x F φ hL σ
  have hs (w : (labelledTateLocalSystem K A p L F φ hL σ).obj (Scheme.etaleFiberPoint K S x)) :
      ((E.hom.hom w) : L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) =
        e ((i.app (Scheme.etaleFiberPoint K S x)).hom w) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hsub) w
  refine Representation.Equiv.mk E.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  let a := (labelledTateLocalSystem K A p L F φ hL σ).map (Scheme.arithmeticFiberLoop K S x g)
  let b := (extendedTateLocalSystem K A p L).map (Scheme.arithmeticFiberLoop K S x g)
  have hn := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (i.naturality (Scheme.arithmeticFiberLoop K S x g))) v
  have he := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (nativeExtendedGeometricFiberTateIso_arithmetic K A p L x g))
      ((i.app (Scheme.etaleFiberPoint K S x)).hom v)
  change ((E.hom.hom (a.hom v)) : L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) =
    ((tateRepresentation K (fiber K A x).X p).baseChange L g)
      ((E.hom.hom v) : L ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p)
  calc
    _ = e ((i.app (Scheme.etaleFiberPoint K S x)).hom (a.hom v)) := hs _
    _ = e (b.hom ((i.app (Scheme.etaleFiberPoint K S x)).hom v)) := congrArg e hn
    _ = ((tateRepresentation K (fiber K A x).X p).baseChange L g)
        (e ((i.app (Scheme.etaleFiberPoint K S x)).hom v)) := he
    _ = _ := congrArg ((tateRepresentation K (fiber K A x).X p).baseChange L g) (hs v).symm

end AlgebraicGeometry.GroupScheme
