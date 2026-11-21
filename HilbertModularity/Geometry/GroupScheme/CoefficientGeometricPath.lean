/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GroupGeometricPath
public import HilbertModularity.Geometry.Etale.GroupSchemeCoefficients

/-! # Coefficient-linear transport of a finite étale group scheme

An actual geometric path transports the original points of one finite étale
group scheme. Naturality with respect to its coefficient endomorphisms makes
this transport linear, also when the two points have different residue fields.
-/

public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory finiteEtaleBraidedCategory

variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S)) [Etale A.X.hom] [IsFinite A.X.hom]

/-- The group path on the actual points of one finite étale group scheme. -/
def finiteEtalePointGeometricPathEquiv :
    Additive (geometricPointOver K x ⟶ A.X) ≃+
      Additive (geometricPointOver L y ⟶ A.X) :=
  (finiteGroupFiberPointsEquiv K x A).toAdditive.symm.trans
    (((finiteGroupFiberGeometricPathIso K L e).app
      (finiteEtaleGroupObject A)).commGroupIsoToMulEquiv.toAdditive.trans
        (finiteGroupFiberPointsEquiv L y A).toAdditive)

/-- The group transport is the given path on the underlying cover. -/
theorem finiteEtalePointGeometricPathEquiv_apply
    (v : Additive (geometricPointOver K x ⟶ A.X)) :
    (finiteEtalePointGeometricPathEquiv K L e A v).toMul =
      e.hom.app (finiteEtaleGroupCover A) v.toMul := (rfl)

/-- Transport intertwines the actual finite étale monodromy action after
conjugating the fundamental group by the geometric path. -/
theorem finiteEtalePointGeometricPathEquiv_monodromy
    (σ : etaleFundamentalGroup K x)
    (v : Additive (geometricPointOver K x ⟶ A.X)) :
    finiteEtalePointGeometricPathEquiv K L e A
        (Additive.ofMul (σ.hom.app (finiteEtaleGroupCover A) v.toMul)) =
      Additive.ofMul
        ((geometricFiberPathGroupEquiv K L e σ).hom.app (finiteEtaleGroupCover A)
          (finiteEtalePointGeometricPathEquiv K L e A v).toMul) := by
  change e.hom.app (finiteEtaleGroupCover A)
      (σ.hom.app (finiteEtaleGroupCover A) v.toMul) =
    (geometricFiberPathGroupEquiv K L e σ).hom.app (finiteEtaleGroupCover A)
      (e.hom.app (finiteEtaleGroupCover A) v.toMul)
  exact finiteGroupFiberGeometricPathIso_smul K L e (finiteEtaleGroupObject A) σ v.toMul

/-- Naturality makes geometric transport commute with the original scheme endomorphism. -/
theorem finiteEtalePointGeometricPathEquiv_endomorphism
    (f : End A) (v : Additive (geometricPointOver K x ⟶ A.X)) :
    finiteEtalePointGeometricPathEquiv K L e A
        (Additive.ofMul (v.toMul ≫ f.hom.hom.hom)) =
      Additive.ofMul ((finiteEtalePointGeometricPathEquiv K L e A v).toMul ≫
        f.hom.hom.hom) := by
  change e.hom.app (finiteEtaleGroupCover A) (v.toMul ≫ f.hom.hom.hom) =
    e.hom.app (finiteEtaleGroupCover A) v.toMul ≫ f.hom.hom.hom
  have h := ConcreteCategory.congr_hom
    ((finiteGroupFiberGeometricPathIso K L e).hom.naturality
      (finiteEtaleGroupObjectMap f)) v.toMul
  have hx := finiteGroupFiberPointsEquiv_natural K x A f v.toMul
  have hy := finiteGroupFiberPointsEquiv_natural L y A f
    (e.hom.app (finiteEtaleGroupCover A) v.toMul)
  erw [finiteGroupFiberPointsEquiv_apply K x A,
    finiteGroupFiberPointsEquiv_apply K x A] at hx
  erw [finiteGroupFiberPointsEquiv_apply L y A,
    finiteGroupFiberPointsEquiv_apply L y A] at hy
  change e.hom.app (finiteEtaleGroupCover A)
      ((finiteGroupFiberFunctor K x).map (finiteEtaleGroupObjectMap f) v.toMul) =
    (finiteGroupFiberFunctor L y).map (finiteEtaleGroupObjectMap f)
      (e.hom.app (finiteEtaleGroupCover A) v.toMul) at h
  erw [hx, hy] at h
  exact h

variable (R : Type*) [CommRing R] (φ : R →+* End A)

/-- The actual geometric path on group-scheme points is linear for every
endomorphism of the same coefficient action. -/
def finiteEtaleCoefficientGeometricPathEquiv :
    letI := finiteEtalePointModule K A R φ x
    letI := finiteEtalePointModule L A R φ y
    Additive (geometricPointOver K x ⟶ A.X) ≃ₗ[R]
      Additive (geometricPointOver L y ⟶ A.X) := by
  letI := finiteEtalePointModule K A R φ x
  letI := finiteEtalePointModule L A R φ y
  exact { finiteEtalePointGeometricPathEquiv K L e A with
    map_smul' r v := by
      exact finiteEtalePointGeometricPathEquiv_endomorphism K L e A (φ r) v }

/-- Coefficient-linear geometric transport uses the original path on points. -/
theorem finiteEtaleCoefficientGeometricPathEquiv_apply
    (v : Additive (geometricPointOver K x ⟶ A.X)) :
    (finiteEtaleCoefficientGeometricPathEquiv K L e A R φ v).toMul =
      e.hom.app (finiteEtaleGroupCover A) v.toMul := (rfl)

end AlgebraicGeometry.Scheme
