/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveInvolution
public import HilbertModularity.Geometry.ProjectiveLine.RationalCoordinate
public import HilbertModularity.Geometry.ProjectiveChartNaturality
public import HilbertModularity.FieldTheory.RatFunc.Involution
import Mathlib.Tactic.FinCases

/-! # The involution on the generic rational coordinate -/

@[expose] public noncomputable section
open CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.ProjectiveLine
variable (R : Type*) [CommRing R]

/-- In the standard affine chart the homogeneous involution is polynomial substitution. -/
theorem chartCoordinates_comp_complementGraded :
    (chartCoordinates R 0).comp (complementGraded R).toRingHom =
      (Polynomial.complementAlgEquiv R).toRingHom.comp (chartCoordinates R 0) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [chartCoordinates]
  · intro i
    fin_cases i <;> simp [chartCoordinates]

set_option backward.isDefEq.respectTransparency false in
/-- The projective complement involution restricts to `X ↦ 1 - X` on its affine chart. -/
@[reassoc]
theorem chartMap_complement :
    chartMap R 0 1 (by decide) ≫ complement R =
      Spec.map (CommRingCat.ofHom (Polynomial.complementAlgEquiv R).toRingHom) ≫
        chartMap R 0 1 (by decide) := by
  have h := Proj.fromSpecOfUnit_comp_map
    (homogeneousSubmodule (Fin 2) R) (homogeneousSubmodule (Fin 2) R)
    (chartCoordinates R 0) (complementGraded R) (complementGraded_irrelevant R)
    (r := X 1) (by decide : 0 < 1) (isHomogeneous_X R 1)
    (by simp [chartCoordinates])
  have hchart (r : MvPolynomial (Fin 2) R)
      (hr : r ∈ homogeneousSubmodule (Fin 2) R 1)
      (hu : IsUnit (chartCoordinates R 0 r)) (heq : r = X 1) :
      Proj.fromSpecOfUnit (homogeneousSubmodule (Fin 2) R) (chartCoordinates R 0)
        (by decide : 0 < 1) hr hu = chartMap R 0 1 (by decide) := by
    subst r
    rfl
  have h₀ := hchart (complementGraded R (X 1))
    ((complementGraded R).map_mem (isHomogeneous_X R (1 : Fin 2)))
    (by simp [chartCoordinates]) (complementGraded_X_one R)
  rw [h₀] at h
  simp only [chartCoordinates_comp_complementGraded] at h
  have hc := Proj.fromSpecOfUnit_comp (homogeneousSubmodule (Fin 2) R)
    (chartCoordinates R 0) (Polynomial.complementAlgEquiv R).toRingHom
    (r := X 1) (by decide : 0 < 1) (isHomogeneous_X R 1)
    (by simp [chartCoordinates])
  simpa only [chartMap, complement] using h.trans hc

variable (K : Type*) [Field K]

/-- The generic rational coordinate transforms by the actual punctured scheme involution. -/
@[reassoc]
theorem puncturedRationalPoint_complement :
    puncturedRationalPoint K ≫ (puncturedComplementIso K).hom =
      Spec.map (CommRingCat.ofHom (RatFunc.complementAlgEquiv K).toRingHom) ≫
        puncturedRationalPoint K := by
  apply (cancel_mono (puncturedInclusion K)).mp
  simp only [Category.assoc, puncturedComplementIso_hom_inclusion]
  have hp : puncturedRationalPoint K ≫ puncturedInclusion K =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) (RatFunc K))) ≫
        chartMap K 0 1 (by decide) := by
    rw [puncturedRationalPoint, Category.assoc, puncturedAffineIso_inv_inclusion,
      ← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    exact RingHom.ext (puncturedCoordinatesToRatFunc_algebraMap K)
  rw [← Category.assoc, hp, Category.assoc, chartMap_complement,
    ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact (RatFunc.complementAlgEquiv_algebraMap K f).symm

end AlgebraicGeometry.ProjectiveLine
