/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveChart
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk

/-! # Affine coordinates and the generic point of the punctured projective line

The complement of zero, one and infinity lies in the polynomial chart and
is the open where `X (X - 1)` is invertible. Over a field this open is integral,
so its generic point defines an actual field-valued point of the parameter scheme.
-/

@[expose] public noncomputable section
open CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveLine
variable (R : Type*) [CommRing R]

/-- In the standard affine chart, the three-punctured line inverts `X (X - 1)`. -/
theorem chartMap_preimage_puncturedOpen :
    chartMap R 0 1 (by decide) ⁻¹ᵁ puncturedOpen R =
      PrimeSpectrum.basicOpen ((Polynomial.X : Polynomial R) * (Polynomial.X - 1)) := by
  have h (s : MvPolynomial (Fin 2) R) (hs : s.IsHomogeneous 1) :
      chartMap R 0 1 (by decide) ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin 2) R) s =
          PrimeSpectrum.basicOpen (chartCoordinates R 0 s) :=
    Proj.fromSpecOfUnit_preimage_basicOpen_one (homogeneousSubmodule (Fin 2) R)
      (chartCoordinates R 0) (isHomogeneous_X R (1 : Fin 2)) hs
      (by simp [chartCoordinates])
  rw [puncturedOpen_eq]
  change (chartMap R 0 1 (by decide) ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (X 0)) ⊓
    (chartMap R 0 1 (by decide) ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (X 1)) ⊓
    (chartMap R 0 1 (by decide) ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (X 0 - X 1)) = _
  rw [h _ (isHomogeneous_X R 0), h _ (isHomogeneous_X R 1),
    h _ ((isHomogeneous_X R 0).sub (isHomogeneous_X R 1))]
  simp [chartCoordinates, PrimeSpectrum.basicOpen_mul]
  ext x
  constructor
  · intro hx
    exact ⟨hx.1.1, hx.2⟩
  · intro hx
    exact ⟨⟨hx.1, trivial⟩, hx.2⟩

/-- The punctured base lies entirely in the chart whose second coordinate is one. -/
theorem puncturedOpen_le_chartRange :
    puncturedOpen R ≤ (chartMap R 0 1 (by decide)).opensRange := by
  rw [chartMap_opensRange, puncturedOpen_eq]
  exact inf_le_left.trans inf_le_right

/-- Restricting the affine parameterization gives the entire punctured base. -/
def puncturedChartIso :
    (chartMap R 0 1 (by decide) ⁻¹ᵁ puncturedOpen R).toScheme ≅ punctured R :=
  IsOpenImmersion.isoOfRangeEq
    ((chartMap R 0 1 (by decide) ⁻¹ᵁ puncturedOpen R).ι ≫ chartMap R 0 1 (by decide))
    (puncturedInclusion R) (by
      have h : chartMap R 0 1 (by decide) ''ᵁ
          (chartMap R 0 1 (by decide) ⁻¹ᵁ puncturedOpen R) = puncturedOpen R := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
          inf_eq_right.mpr (puncturedOpen_le_chartRange R)]
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      change ((chartMap R 0 1 (by decide) ''ᵁ
        (chartMap R 0 1 (by decide) ⁻¹ᵁ puncturedOpen R)) : Set (ProjectiveLine R)) = _
      rw [h]
      exact (Scheme.Opens.range_ι (puncturedOpen R)).symm)

/-- The affine chart isomorphism respects the original inclusion in the projective line. -/
@[reassoc]
theorem puncturedChartIso_hom_inclusion :
    (puncturedChartIso R).hom ≫ puncturedInclusion R =
      (chartMap R 0 1 (by decide) ⁻¹ᵁ puncturedOpen R).ι ≫ chartMap R 0 1 (by decide) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

variable (K : Type*) [Field K]

/-- The generic polynomial prime lies in the punctured affine chart. -/
theorem bot_mem_chartMap_preimage_puncturedOpen :
    (⊥ : PrimeSpectrum (Polynomial K)) ∈
      chartMap K 0 1 (by decide) ⁻¹ᵁ puncturedOpen K := by
  rw [chartMap_preimage_puncturedOpen]
  change (Polynomial.X : Polynomial K) * (Polynomial.X - 1) ∉ (⊥ : Ideal (Polynomial K))
  simpa only [Ideal.mem_bot] using mul_ne_zero Polynomial.X_ne_zero
    (by simpa using (Polynomial.X_sub_C_ne_zero (1 : K)))

/-- The punctured projective line over a field is integral. -/
instance punctured_isIntegral : IsIntegral (punctured K) := by
  let U := chartMap K 0 1 (by decide) ⁻¹ᵁ puncturedOpen K
  let : Nonempty U :=
    ⟨⟨(⊥ : PrimeSpectrum (Polynomial K)), bot_mem_chartMap_preimage_puncturedOpen K⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  exact IsIntegral.of_isIso (puncturedChartIso K).hom

/-- The canonical point over the function field of the actual punctured parameter scheme. -/
def puncturedGenericPoint :
    Spec (punctured K).functionField ⟶ punctured K :=
  (punctured K).fromSpecStalk (genericPoint (punctured K))

/-- This field-valued point maps its unique closed point to the generic point. -/
@[simp]
theorem puncturedGenericPoint_closedPoint :
    puncturedGenericPoint K (IsLocalRing.closedPoint (punctured K).functionField) =
      genericPoint (punctured K) :=
  Scheme.fromSpecStalk_closedPoint

/-- The canonical function-field point has dense image in the punctured base. -/
instance puncturedGenericPoint_isDominant : IsDominant (puncturedGenericPoint K) := by
  have h : Dense ({genericPoint (punctured K)} : Set (punctured K)) :=
    dense_iff_closure_eq.mpr (genericPoint_spec (punctured K))
  exact ⟨h.mono (Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint (punctured K).functionField, puncturedGenericPoint_closedPoint K⟩)⟩

end AlgebraicGeometry.ProjectiveLine
