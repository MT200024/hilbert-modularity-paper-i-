/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.FunctionField
public import Mathlib.FieldTheory.RatFunc.Basic

/-! # The rational coordinate of the punctured parameter scheme

The punctured line is `Spec K[X,1/(X(X-1))]`. Its inclusion in `K(X)` gives
a dominant point over the rational-function field, retaining the base-field structure.
-/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine
variable (R : Type*) [CommRing R]

/-- The coordinate-ring description of the three-punctured projective line. -/
def puncturedAffineIso : punctured R ≅
    Spec (CommRingCat.of (Localization.Away
      ((Polynomial.X : Polynomial R) * (Polynomial.X - 1)))) :=
  (puncturedChartIso R).symm ≪≫
    Scheme.isoOfEq _ (chartMap_preimage_puncturedOpen R) ≪≫
      basicOpenIsoSpecAway ((Polynomial.X : Polynomial R) * (Polynomial.X - 1))

/-- The three-punctured projective line is affine over any coefficient ring. -/
instance punctured_isAffine : IsAffine (punctured R) :=
  IsAffine.of_isIso (puncturedAffineIso R).hom

/-- The localized affine coordinates use the original standard projective chart. -/
@[reassoc]
theorem puncturedAffineIso_inv_inclusion :
    (puncturedAffineIso R).inv ≫ puncturedInclusion R =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R)
        (Localization.Away ((Polynomial.X : Polynomial R) * (Polynomial.X - 1))))) ≫
          chartMap R 0 1 (by decide) := by
  simp only [puncturedAffineIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    puncturedChartIso_hom_inclusion]
  have h := Scheme.isoOfEq_inv_ι_assoc (Spec (CommRingCat.of (Polynomial R)))
    (chartMap_preimage_puncturedOpen R) (chartMap R 0 1 (by decide))
  rw [h, ← basicOpenIsoSpecAway_hom_SpecMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The affine coordinate description is over the original coefficient ring. -/
@[reassoc]
theorem puncturedAffineIso_inv_toSpec :
    (puncturedAffineIso R).inv ≫ puncturedToSpec R =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (Polynomial R)
          (Localization.Away ((Polynomial.X : Polynomial R) * (Polynomial.X - 1)))).comp
            Polynomial.C)) := by
  rw [puncturedToSpec, ← Category.assoc, puncturedAffineIso_inv_inclusion,
    Category.assoc, chartMap_toSpec, ← Spec.map_comp]
  rfl

variable (K : Type*) [Field K]

/-- Embed the punctured affine coordinate ring in the rational-function field. -/
def puncturedCoordinatesToRatFunc :
    Localization.Away ((Polynomial.X : Polynomial K) * (Polynomial.X - 1)) →+* RatFunc K :=
  Localization.awayLift (algebraMap (Polynomial K) (RatFunc K)) _
    (isUnit_iff_ne_zero.mpr (by
      intro h
      have hz := (IsFractionRing.injective (Polynomial K) (RatFunc K))
        (h.trans (map_zero _).symm)
      exact (mul_ne_zero Polynomial.X_ne_zero
        (by simpa using (Polynomial.X_sub_C_ne_zero (1 : K)))) hz))

/-- Polynomial functions retain their value under the coordinate-ring embedding. -/
@[simp]
theorem puncturedCoordinatesToRatFunc_algebraMap (f : Polynomial K) :
    puncturedCoordinatesToRatFunc K (algebraMap (Polynomial K) _ f) =
      algebraMap (Polynomial K) (RatFunc K) f := by
  simp [puncturedCoordinatesToRatFunc, Localization.awayLift, IsLocalization.Away.lift_eq]

/-- The affine coordinate-ring map is injective. -/
theorem puncturedCoordinatesToRatFunc_injective :
    Function.Injective (puncturedCoordinatesToRatFunc K) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (S := _)
    (M := Submonoid.powers ((Polynomial.X : Polynomial K) * (Polynomial.X - 1)))
    (puncturedCoordinatesToRatFunc K)
  intro f hf
  rw [puncturedCoordinatesToRatFunc_algebraMap] at hf
  have : f = 0 := (IsFractionRing.injective (Polynomial K) (RatFunc K))
    (hf.trans (map_zero _).symm)
  rw [this, map_zero]

/-- The rational coordinate gives a point of the punctured line over `K(X)`. -/
def puncturedRationalPoint : Spec (CommRingCat.of (RatFunc K)) ⟶ punctured K :=
  Spec.map (CommRingCat.ofHom (puncturedCoordinatesToRatFunc K)) ≫
    (puncturedAffineIso K).inv

/-- This rational-function-field point is generic: its image is dense. -/
instance puncturedRationalPoint_isDominant : IsDominant (puncturedRationalPoint K) := by
  let : IsDominant (Spec.map (CommRingCat.ofHom (puncturedCoordinatesToRatFunc K))) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (puncturedCoordinatesToRatFunc K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (puncturedCoordinatesToRatFunc_injective K)]
    exact bot_le
  unfold puncturedRationalPoint
  infer_instance

/-- The generic rational coordinate is a point over the original ground field. -/
@[reassoc]
theorem puncturedRationalPoint_toSpec :
    puncturedRationalPoint K ≫ puncturedToSpec K =
      Spec.map (CommRingCat.ofHom (algebraMap K (RatFunc K))) := by
  rw [puncturedRationalPoint, Category.assoc, puncturedAffineIso_inv_toSpec,
    ← Spec.map_comp]
  congr 1
  ext r
  change puncturedCoordinatesToRatFunc K
    (algebraMap (Polynomial K) _ (Polynomial.C r)) = algebraMap K (RatFunc K) r
  rw [puncturedCoordinatesToRatFunc_algebraMap]
  exact (IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) r).symm

end AlgebraicGeometry.ProjectiveLine
