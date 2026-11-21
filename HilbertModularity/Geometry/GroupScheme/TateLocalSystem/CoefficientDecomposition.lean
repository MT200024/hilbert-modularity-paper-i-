/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.Abelian.Idempotents
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.ScalarExtension
public import HilbertModularity.LinearAlgebra.CoefficientDecomposition
public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # Labelled factors of a single Tate family

Scalar extension changes the coefficients of one Tate family without changing
its geometric fibre groupoid. An integral real-multiplication action extends
to the split coefficient algebra. Its primitive idempotents are natural
endomorphisms, whose categorical images give the labelled families in
[TripathiGoswami, coefficient-label lemma]. Each image fibre is canonically
the range of the corresponding coefficient projector.

The construction uses a given family and integral coefficient action. It does
not assert the existence or rank of the Darmon family.
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

variable (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
  [Algebra ℚ L]

/-- The split coefficient algebra acts naturally on the extended single Tate family. -/
def extendedTensorTateLocalSystemAction :
    L ⊗[ℚ] F →ₐ[L] End (extendedTateLocalSystem K A p L) :=
  NumberField.RingOfIntegers.tensorExtension F L
    ((extendedTateLocalSystemEndomorphismMap K A p L).comp
      ((rationalTateLocalSystemEndomorphismMap K A p).comp φ))

/-- Integral coefficients after scalar extension still come from the original scheme map. -/
@[simp]
theorem extendedTensorTateLocalSystemAction_integer (a : 𝓞 F) :
    extendedTensorTateLocalSystemAction K A p L F φ ((1 : L) ⊗ₜ[ℚ] (a : F)) =
      extendedTateLocalSystemEndomorphism K A p L (rationalTateLocalSystemMap K p (φ a)) :=
  NumberField.RingOfIntegers.tensorExtension_integer F L _ a

variable (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)

/-- The primitive coefficient projector is a natural endomorphism of one extended family. -/
def labelledTateLocalSystemProjection (σ : F →ₐ[ℚ] L) :
    End (extendedTateLocalSystem K A p L) :=
  extendedTensorTateLocalSystemAction K A p L F φ
    (Algebra.TensorProduct.embeddingIdempotent ℚ F L hL σ)

/-- Coefficient projectors on the whole family are complete and orthogonal. -/
theorem completeOrthogonalIdempotents_labelledTateLocalSystemProjection :
    CompleteOrthogonalIdempotents (labelledTateLocalSystemProjection K A p L F φ hL) :=
  (Algebra.TensorProduct.completeOrthogonalIdempotents_embeddingIdempotent ℚ F L hL).map
    (extendedTensorTateLocalSystemAction K A p L F φ).toRingHom

/-- The labelled factor is the categorical image of its projector on the original family. -/
abbrev labelledTateLocalSystem (σ : F →ₐ[ℚ] L) :
    Scheme.EtaleFiberGroupoid K S ⥤ ModuleCat L :=
  CategoryTheory.Limits.image (labelledTateLocalSystemProjection K A p L F φ hL σ)

/-- The labelled family includes naturally into its original scalar-extended Tate family. -/
def labelledTateLocalSystemInclusion (σ : F →ₐ[ℚ] L) :
    labelledTateLocalSystem K A p L F φ hL σ ⟶ extendedTateLocalSystem K A p L :=
  CategoryTheory.Limits.image.ι (labelledTateLocalSystemProjection K A p L F φ hL σ)

/-- Inclusion of a labelled family is injective at each geometric fibre. -/
instance labelledTateLocalSystemInclusion_app_mono (σ : F →ₐ[ℚ] L)
    (x : Scheme.EtaleFiberGroupoid K S) :
    Mono ((labelledTateLocalSystemInclusion K A p L F φ hL σ).app x) := by
  dsimp only [labelledTateLocalSystemInclusion]
  infer_instance

/-- At every point the labelled family is the range of the same coefficient projector. -/
def labelledTateLocalSystemFiberIso (σ : F →ₐ[ℚ] L)
    (x : Scheme.EtaleFiberGroupoid K S) :
    (labelledTateLocalSystem K A p L F φ hL σ).obj x ≅
      ModuleCat.of L (LinearMap.range ((labelledTateLocalSystemProjection K A p L F φ hL σ).app x).hom) :=
  (PreservesImage.iso ((evaluation _ _).obj x)
    (labelledTateLocalSystemProjection K A p L F φ hL σ)).symm ≪≫
      ModuleCat.imageIsoRange ((labelledTateLocalSystemProjection K A p L F φ hL σ).app x)

/-- The canonical fibre-range comparison commutes with inclusion into the ambient family. -/
@[reassoc]
theorem labelledTateLocalSystemFiberIso_hom_subtype (σ : F →ₐ[ℚ] L)
    (x : Scheme.EtaleFiberGroupoid K S) :
    (labelledTateLocalSystemFiberIso K A p L F φ hL σ x).hom ≫
      ModuleCat.ofHom (LinearMap.range
        ((labelledTateLocalSystemProjection K A p L F φ hL σ).app x).hom).subtype =
      (CategoryTheory.Limits.image.ι
        (labelledTateLocalSystemProjection K A p L F φ hL σ)).app x := by
  change ((PreservesImage.iso ((evaluation _ _).obj x)
      (labelledTateLocalSystemProjection K A p L F φ hL σ)).inv ≫
      (ModuleCat.imageIsoRange
        ((labelledTateLocalSystemProjection K A p L F φ hL σ).app x)).hom) ≫ _ = _
  rw [Category.assoc, ModuleCat.imageIsoRange_hom_subtype]
  exact PreservesImage.inv_comp_image_ι_map _ _

/-- The whole coefficient algebra acts through the selected embedding on its image family. -/
theorem tensorAction_labelledTateLocalSystem (σ : F →ₐ[ℚ] L) (z : L ⊗[ℚ] F) :
    CategoryTheory.Limits.image.ι (labelledTateLocalSystemProjection K A p L F φ hL σ) ≫
        extendedTensorTateLocalSystemAction K A p L F φ z =
      Algebra.TensorProduct.embeddingEquiv ℚ F L hL z σ •
        CategoryTheory.Limits.image.ι (labelledTateLocalSystemProjection K A p L F φ hL σ) := by
  apply (cancel_epi (CategoryTheory.Limits.factorThruImage
    (labelledTateLocalSystemProjection K A p L F φ hL σ))).1
  rw [← Category.assoc, CategoryTheory.Limits.image.fac, Linear.comp_smul,
    CategoryTheory.Limits.image.fac]
  change extendedTensorTateLocalSystemAction K A p L F φ z *
      extendedTensorTateLocalSystemAction K A p L F φ
        (Algebra.TensorProduct.embeddingIdempotent ℚ F L hL σ) = _
  rw [← map_mul, Algebra.TensorProduct.mul_embeddingIdempotent, map_smul]
  rfl

/-- A number-field coefficient acts through its chosen embedding on the labelled family. -/
theorem numberFieldAction_labelledTateLocalSystem (σ : F →ₐ[ℚ] L) (a : F) :
    CategoryTheory.Limits.image.ι (labelledTateLocalSystemProjection K A p L F φ hL σ) ≫
        extendedTensorTateLocalSystemAction K A p L F φ ((1 : L) ⊗ₜ[ℚ] a) =
      σ a • CategoryTheory.Limits.image.ι
        (labelledTateLocalSystemProjection K A p L F φ hL σ) := by
  simpa only [Algebra.TensorProduct.embeddingEquiv_tmul, one_mul] using
    tensorAction_labelledTateLocalSystem K A p L F φ hL σ ((1 : L) ⊗ₜ[ℚ] a)

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- The same extended Tate family decomposes as the biproduct of all its labelled image families. -/
def labelledTateLocalSystemDecomposition :
    extendedTateLocalSystem K A p L ≅
      CategoryTheory.Limits.biproduct (fun σ : F →ₐ[ℚ] L => labelledTateLocalSystem K A p L F φ hL σ) :=
  CategoryTheory.Limits.idempotentImageBiproductIso
    (completeOrthogonalIdempotents_labelledTateLocalSystemProjection K A p L F φ hL)

/-- Each labelled image family is a canonical natural retract of the extended Tate family. -/
theorem labelledTateLocalSystem_retraction (σ : F →ₐ[ℚ] L) :
    CategoryTheory.Limits.image.ι (labelledTateLocalSystemProjection K A p L F φ hL σ) ≫
        CategoryTheory.Limits.factorThruImage (labelledTateLocalSystemProjection K A p L F φ hL σ) =
      𝟙 (labelledTateLocalSystem K A p L F φ hL σ) := by
  have h := (CategoryTheory.Limits.idempotentImageBicone
    (completeOrthogonalIdempotents_labelledTateLocalSystemProjection K A p L F φ hL)).ι_π σ σ
  simpa only [labelledTateLocalSystem, CategoryTheory.Limits.idempotentImageBicone, dite_eq_left rfl,
    eqToHom_refl] using h

end AlgebraicGeometry.GroupScheme
