/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.Conjugation

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.FieldCoordinate
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.ScalarExtensionFiber
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Coefficient-labelled Tate fibres under field-coordinate isomorphisms

Transport preserves the integral endomorphisms of the original family, hence its
whole coefficient tensor algebra and its embedding-labelled projector images.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra ChangeOfRings
namespace AlgebraicGeometry.GroupScheme
universe u
variable (E K : Type u) [Field E] [Field K] (σ : E ≃+* K)
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [Field L] [Algebra ℚ_[p] L]

/-- The native rational Tate comparison, with the actual family fibre modules as its endpoints. -/
def rationalTateFieldCoordinateIso :
    (rationalTateLocalSystem E A p).obj (Scheme.etaleFiberPoint E S x) ≅
      (rationalTateLocalSystem K A p).obj
        (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)) :=
  (rationalTateFieldCoordinateEquiv E K σ x A p).toModuleIso

/-- Extend the actual field-coordinate comparison to the same coefficient field. -/
abbrev extendedTateFieldCoordinateIso :
    (extendedTateLocalSystem E A p L).obj (Scheme.etaleFiberPoint E S x) ≅
      (extendedTateLocalSystem K A p L).obj
        (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)) :=
  (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).mapIso
    (rationalTateFieldCoordinateIso E K σ x A p)

set_option maxHeartbeats 1000000 in
/-- The forward coordinate map is the standard scalar extension of the rational comparison. -/
theorem extendedTateFieldCoordinateIso_hom :
    (extendedTateFieldCoordinateIso E K σ x A p L).hom =
      (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map
        (rationalTateFieldCoordinateIso E K σ x A p).hom :=
  Functor.mapIso_hom (ModuleCat.extendScalars (algebraMap ℚ_[p] L))
    (rationalTateFieldCoordinateIso E K σ x A p)

set_option maxHeartbeats 2000000 in
/-- Extended coordinate transport retains each endomorphism of the original group scheme. -/
theorem extendedTateFieldCoordinateIso_endomorphism (f : End A) :
    ((extendedTateLocalSystemEndomorphism E A p L (rationalTateLocalSystemMap E p f)).app
        (Scheme.etaleFiberPoint E S x)) ≫ (extendedTateFieldCoordinateIso E K σ x A p L).hom =
      (extendedTateFieldCoordinateIso E K σ x A p L).hom ≫
        ((extendedTateLocalSystemEndomorphism K A p L (rationalTateLocalSystemMap K p f)).app
          (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x))) := by
  let e := (rationalTateFieldCoordinateIso E K σ x A p)
  let T := ModuleCat.extendScalars (algebraMap ℚ_[p] L)
  have h : (rationalTateLocalSystemMap E p f).app (Scheme.etaleFiberPoint E S x) ≫ e.hom =
      e.hom ≫ (rationalTateLocalSystemMap K p f).app
        (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change rationalTateFieldCoordinateEquiv E K σ x A p
      (((rationalTateLocalSystemMap E p f).app (Scheme.etaleFiberPoint E S x)).hom v) =
      ((rationalTateLocalSystemMap K p f).app
        (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x))).hom
          (rationalTateFieldCoordinateEquiv E K σ x A p v)
    exact (congrArg (rationalTateFieldCoordinateEquiv E K σ x A p)
      (rationalTateLocalSystemMap_app_apply E p f x v)).trans
        ((rationalTateFieldCoordinateEquiv_endomorphism E K σ x A p f v).trans
          (rationalTateLocalSystemMap_app_apply K p f
            (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
            (rationalTateFieldCoordinateEquiv E K σ x A p v)).symm)
  rw [extendedTateLocalSystemEndomorphism_app, extendedTateLocalSystemEndomorphism_app,
    extendedTateFieldCoordinateIso_hom]
  exact (T.map_comp _ _).symm.trans ((congrArg T.map h).trans (T.map_comp _ _))

set_option maxHeartbeats 1000000 in
/-- Scalar-extended coordinate transport intertwines the actual arithmetic loops. -/
theorem extendedTateFieldCoordinateIso_arithmetic
    (g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
    (extendedTateLocalSystem E A p L).map (Scheme.arithmeticFiberLoop E S x g) ≫
        (extendedTateFieldCoordinateIso E K σ x A p L).hom =
      (extendedTateFieldCoordinateIso E K σ x A p L).hom ≫
        (extendedTateLocalSystem K A p L).map
          (Scheme.arithmeticFiberLoop K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
            (AlgebraicClosure.galoisFieldEquiv E K σ g)) := by
  let e := (rationalTateFieldCoordinateIso E K σ x A p)
  let T := ModuleCat.extendScalars (algebraMap ℚ_[p] L)
  have h : (rationalTateLocalSystem E A p).map (Scheme.arithmeticFiberLoop E S x g) ≫ e.hom =
      e.hom ≫ (rationalTateLocalSystem K A p).map
        (Scheme.arithmeticFiberLoop K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
          (AlgebraicClosure.galoisFieldEquiv E K σ g)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    have hE := rationalTateLocalSystem_loop E A p x
      (Scheme.galoisToEtaleFundamentalGroup E x g) v
    have hK := rationalTateLocalSystem_loop K A p
      (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
      (Scheme.galoisToEtaleFundamentalGroup K
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
        (AlgebraicClosure.galoisFieldEquiv E K σ g))
      (rationalTateFieldCoordinateEquiv E K σ x A p v)
    exact (congrArg (rationalTateFieldCoordinateEquiv E K σ x A p) hE).trans
      ((LinearMap.congr_fun
        ((rationalTateFieldCoordinateRepresentationEquiv E K σ x A p).isIntertwining' g) v).trans
          hK.symm)
  rw [extendedTateFieldCoordinateIso_hom]
  exact (T.map_comp _ _).symm.trans ((congrArg T.map h).trans (T.map_comp _ _))

variable (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ L]

set_option maxHeartbeats 1000000 in
/-- The full coefficient algebra commutes with field-coordinate transport. -/
theorem extendedTateFieldCoordinateIso_coefficients (z : L ⊗[ℚ] F)
    (v : (extendedTateLocalSystem E A p L).obj (Scheme.etaleFiberPoint E S x)) :
    (extendedTateFieldCoordinateIso E K σ x A p L).hom.hom
        (((extendedTensorTateLocalSystemAction E A p L F φ z).app
          (Scheme.etaleFiberPoint E S x)).hom v) =
      ((extendedTensorTateLocalSystemAction K A p L F φ z).app
        (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x))).hom
        ((extendedTateFieldCoordinateIso E K σ x A p L).hom.hom v) := by
  rw [extendedTensorTateLocalSystemAction_app, extendedTensorTateLocalSystemAction_app]
  apply NumberField.RingOfIntegers.tensorExtension_intertwines F _ _
    (extendedTateFieldCoordinateIso E K σ x A p L).hom.hom
  intro c w
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (extendedTateFieldCoordinateIso_endomorphism E K σ x A p L (φ c))) w

variable (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

set_option maxHeartbeats 1000000 in
/-- Field-coordinate transport carries each coefficient projector range to the same labelled range. -/
theorem extendedTateFieldCoordinateIso_map_labelledRange (τ : F →ₐ[ℚ] L) :
    (LinearMap.range ((labelledTateLocalSystemProjection E A p L F φ hL τ).app
      (Scheme.etaleFiberPoint E S x)).hom).map
        (extendedTateFieldCoordinateIso E K σ x A p L).hom.hom =
      LinearMap.range ((labelledTateLocalSystemProjection K A p L F φ hL τ).app
        (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x))).hom := by
  have hc : (extendedTateFieldCoordinateIso E K σ x A p L).hom.hom.comp
        ((labelledTateLocalSystemProjection E A p L F φ hL τ).app
          (Scheme.etaleFiberPoint E S x)).hom =
      (((labelledTateLocalSystemProjection K A p L F φ hL τ).app
        (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x))).hom).comp
          (extendedTateFieldCoordinateIso E K σ x A p L).hom.hom := by
    apply LinearMap.ext
    intro v
    exact extendedTateFieldCoordinateIso_coefficients E K σ x A p L F φ
      (Algebra.TensorProduct.embeddingIdempotent ℚ F L hL τ) v
  rw [← LinearMap.range_comp, hc]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (extendedTateFieldCoordinateIso E K σ x A p L).toLinearEquiv)

set_option maxHeartbeats 1000000 in
/-- The same embedding-labelled family fibres are identified under a change of parameter field. -/
def labelledTateFieldCoordinateIso (τ : F →ₐ[ℚ] L) :
    (labelledTateLocalSystem E A p L F φ hL τ).obj (Scheme.etaleFiberPoint E S x) ≅
      (labelledTateLocalSystem K A p L F φ hL τ).obj
        (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)) :=
  labelledTateLocalSystemFiberIso E A p L F φ hL τ (Scheme.etaleFiberPoint E S x) ≪≫
    ((extendedTateFieldCoordinateIso E K σ x A p L).toLinearEquiv.ofSubmodules _ _
      (extendedTateFieldCoordinateIso_map_labelledRange E K σ x A p L F φ hL τ)).toModuleIso ≪≫
    (labelledTateLocalSystemFiberIso K A p L F φ hL τ
      (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x))).symm

set_option maxHeartbeats 1000000 in
/-- The labelled coordinate comparison is the restriction of its ambient Tate comparison. -/
@[reassoc]
theorem labelledTateFieldCoordinateIso_hom_inclusion (τ : F →ₐ[ℚ] L) :
    (labelledTateFieldCoordinateIso E K σ x A p L F φ hL τ).hom ≫
        (labelledTateLocalSystemInclusion K A p L F φ hL τ).app
          (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)) =
      (labelledTateLocalSystemInclusion E A p L F φ hL τ).app
        (Scheme.etaleFiberPoint E S x) ≫ (extendedTateFieldCoordinateIso E K σ x A p L).hom := by
  dsimp only [labelledTateLocalSystemInclusion]
  rw [← labelledTateLocalSystemFiberIso_hom_subtype K A p L F φ hL τ,
    ← labelledTateLocalSystemFiberIso_hom_subtype E A p L F φ hL τ]
  dsimp only [labelledTateFieldCoordinateIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rfl

set_option maxHeartbeats 4000000 in
/-- The coordinate isomorphism of labelled fibres intertwines their native arithmetic loops. -/
theorem labelledTateFieldCoordinateIso_arithmetic (τ : F →ₐ[ℚ] L)
    (g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
    (labelledTateLocalSystem E A p L F φ hL τ).map (Scheme.arithmeticFiberLoop E S x g) ≫
        (labelledTateFieldCoordinateIso E K σ x A p L F φ hL τ).hom =
      (labelledTateFieldCoordinateIso E K σ x A p L F φ hL τ).hom ≫
        (labelledTateLocalSystem K A p L F φ hL τ).map
          (Scheme.arithmeticFiberLoop K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
            (AlgebraicClosure.galoisFieldEquiv E K σ g)) := by
  exact CategoryTheory.NatTrans.intertwines_of_mono
    (labelledTateLocalSystemInclusion E A p L F φ hL τ)
    (labelledTateLocalSystemInclusion K A p L F φ hL τ)
    (Scheme.etaleFiberPoint E S x)
    (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x))
    (Scheme.arithmeticFiberLoop E S x g)
    (Scheme.arithmeticFiberLoop K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
      (AlgebraicClosure.galoisFieldEquiv E K σ g))
    (labelledTateFieldCoordinateIso E K σ x A p L F φ hL τ).hom
    (extendedTateFieldCoordinateIso E K σ x A p L).hom
    (labelledTateFieldCoordinateIso_hom_inclusion E K σ x A p L F φ hL τ)
    (extendedTateFieldCoordinateIso_arithmetic E K σ x A p L g)

set_option maxHeartbeats 1000000 in
/-- Each embedding-labelled arithmetic fibre is transported with the native conjugated Galois action. -/
def labelledTateFieldCoordinateRepresentationEquiv (τ : F →ₐ[ℚ] L) :
    Representation.Equiv
      (Scheme.arithmeticFiberRepresentation E S (labelledTateLocalSystem E A p L F φ hL τ) x)
      ((Scheme.arithmeticFiberRepresentation K S (labelledTateLocalSystem K A p L F φ hL τ)
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)).comp
          (AlgebraicClosure.galoisFieldEquiv E K σ).toMonoidHom) := by
  refine Representation.Equiv.mk
    (labelledTateFieldCoordinateIso E K σ x A p L F φ hL τ).toLinearEquiv ?_
  intro g
  exact congrArg ModuleCat.Hom.hom
    (labelledTateFieldCoordinateIso_arithmetic E K σ x A p L F φ hL τ g)

end AlgebraicGeometry.GroupScheme
