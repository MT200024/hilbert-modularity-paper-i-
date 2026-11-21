/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GroupPointComparison
public import HilbertModularity.Geometry.GroupScheme.FiberPoints
public import HilbertModularity.Geometry.GroupScheme.PrimeKernel
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Actual coefficient actions on finite étale group-scheme local systems

A ring acting on one finite étale group scheme acts on its actual geometric
points at every fibre. Naturality of étale paths makes this one coefficient-linear
local system, retaining the original geometric points and arithmetic action.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory finiteEtaleBraidedCategory
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  [AlgebraicGeometry.Etale A.X.hom] [IsFinite A.X.hom]

/-- The finite étale group-scheme local system, on its original geometric point groups. -/
def finiteEtalePointLocalSystem : EtaleFiberGroupoid K S ⥤ AddCommGrpCat :=
  (finiteGroupFiberLocalSystem K (finiteEtaleGroupObject A) ⋙ CommGrpCat.toAddCommGrp).copyObj
    (fun x => AddCommGrpCat.of (Additive (geometricPointOver K x ⟶ A.X)))
    (fun x => (finiteGroupFiberPointsEquiv K x A).toAdditive.toAddCommGrpIso)

/-- The point local system has exactly the actual group-scheme points at each fibre. -/
@[simp]
theorem finiteEtalePointLocalSystem_obj (x : EtaleFiberGroupoid K S) :
    (finiteEtalePointLocalSystem K A).obj x =
      AddCommGrpCat.of (Additive (geometricPointOver K x ⟶ A.X)) := rfl

/-- Path transport on the original points is the original natural isomorphism on the finite cover. -/
theorem finiteEtalePointLocalSystem_map_apply {x y : EtaleFiberGroupoid K S} (e : x ⟶ y)
    (v : Additive (geometricPointOver K x ⟶ A.X)) :
    ((finiteEtalePointLocalSystem K A).map e v).toMul =
      e.hom.iso.hom.app (finiteEtaleGroupCover A) v.toMul := by
  change finiteGroupFiberPointsEquiv K y A
    ((finiteGroupFiberPathIso K e.hom.iso).hom.app (finiteEtaleGroupObject A)
      ((finiteGroupFiberPointsEquiv K x A).symm v.toMul)) = _
  erw [finiteGroupFiberPointsEquiv_apply K y A, finiteGroupFiberPathIso_apply]

/-- Every actual étale path commutes with each endomorphism of the same finite étale group scheme. -/
theorem finiteEtalePointLocalSystem_map_endomorphism
    {x y : EtaleFiberGroupoid K S} (e : x ⟶ y) (f : End A)
    (v : Additive (geometricPointOver K x ⟶ A.X)) :
    (finiteEtalePointLocalSystem K A).map e
        (Additive.ofMul (v.toMul ≫ f.hom.hom.hom)) =
      Additive.ofMul (((finiteEtalePointLocalSystem K A).map e v).toMul ≫
        f.hom.hom.hom) := by
  change ((finiteEtalePointLocalSystem K A).map e
    (Additive.ofMul (v.toMul ≫ f.hom.hom.hom))).toMul = _
  erw [finiteEtalePointLocalSystem_map_apply K A e
    (Additive.ofMul (v.toMul ≫ f.hom.hom.hom)),
    finiteEtalePointLocalSystem_map_apply K A e v]
  have h := ConcreteCategory.congr_hom
    ((finiteGroupFiberPathIso K e.hom.iso).hom.naturality (finiteEtaleGroupObjectMap f)) v.toMul
  have hx := finiteGroupFiberPointsEquiv_natural K x A f v.toMul
  have hy := finiteGroupFiberPointsEquiv_natural K y A f
    (e.hom.iso.hom.app (finiteEtaleGroupCover A) v.toMul)
  erw [finiteGroupFiberPointsEquiv_apply K x A, finiteGroupFiberPointsEquiv_apply K x A] at hx
  erw [finiteGroupFiberPointsEquiv_apply K y A, finiteGroupFiberPointsEquiv_apply K y A] at hy
  change e.hom.iso.hom.app (finiteEtaleGroupCover A)
      ((finiteGroupFiberFunctor K x).map (finiteEtaleGroupObjectMap f) v.toMul) =
    (finiteGroupFiberFunctor K y).map (finiteEtaleGroupObjectMap f)
      (e.hom.iso.hom.app (finiteEtaleGroupCover A) v.toMul) at h
  erw [hx, hy] at h
  exact h

variable (R : Type*) [CommRing R] (φ : R →+* End A)

/-- The actual coefficient scheme action gives the module on each original geometric point group. -/
@[instance_reducible]
def finiteEtalePointModule (x : EtaleFiberGroupoid K S) :
    Module R (Additive (geometricPointOver K x ⟶ A.X)) :=
  Module.compHom _ ((CommGrp.pointsEndomorphismMap (geometricPointOver K x) A).comp φ)

set_option backward.isDefEq.respectTransparency false in
/-- Actual étale path transport is linear for the given scheme coefficient action. -/
theorem finiteEtalePointLocalSystem_map_smul {x y : EtaleFiberGroupoid K S} (e : x ⟶ y)
    (r : R) (v : Additive (geometricPointOver K x ⟶ A.X)) :
    letI (z : EtaleFiberGroupoid K S) := finiteEtalePointModule K A R φ z
    (finiteEtalePointLocalSystem K A).map e (r • v) =
      r • (show Additive (geometricPointOver K y ⟶ A.X) from
        (finiteEtalePointLocalSystem K A).map e v) :=
  finiteEtalePointLocalSystem_map_endomorphism K A e (φ r) v

/-- One actual finite étale group scheme with coefficients gives a linear local system of its actual points. -/
def finiteEtaleCoefficientLocalSystem : EtaleFiberGroupoid K S ⥤ ModuleCat R := by
  letI := fun x => finiteEtalePointModule K A R φ x
  exact {
    obj x := ModuleCat.of R (Additive (geometricPointOver K x ⟶ A.X))
    map e := ModuleCat.ofHom {
      __ := ((finiteEtalePointLocalSystem K A).map e).hom
      map_smul' r v := finiteEtalePointLocalSystem_map_smul K A R φ e r v }
    map_id x := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact congrArg (fun f : (finiteEtalePointLocalSystem K A).obj x ⟶
        (finiteEtalePointLocalSystem K A).obj x => f v)
          ((finiteEtalePointLocalSystem K A).map_id x)
    map_comp {x y z} e f := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact congrArg (fun h : (finiteEtalePointLocalSystem K A).obj x ⟶
        (finiteEtalePointLocalSystem K A).obj z => h v)
          ((finiteEtalePointLocalSystem K A).map_comp e f) }

/-- Coefficient linearization preserves the actual path maps on geometric points. -/
@[simp]
theorem finiteEtaleCoefficientLocalSystem_map_apply {x y : EtaleFiberGroupoid K S}
    (e : x ⟶ y) (v : Additive (geometricPointOver K x ⟶ A.X)) :
    (finiteEtaleCoefficientLocalSystem K A R φ).map e v =
      (finiteEtalePointLocalSystem K A).map e v := rfl

/-- At arithmetic loops the coefficient-linear local system is the original Galois action on points. -/
theorem finiteEtaleCoefficientLocalSystem_arithmetic (x : Spec (CommRingCat.of K) ⟶ S)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : Additive (geometricPointOver K x ⟶ A.X)) :
    ((finiteEtaleCoefficientLocalSystem K A R φ).map (arithmeticFiberLoop K S x g) v).toMul =
      arithmeticFiberPointMap K x g ≫ v.toMul := by
  exact finiteEtalePointLocalSystem_map_apply K A (arithmeticFiberLoop K S x g) v

/-- The actual coefficient local-system fibre is the geometric point module of the actual pulled-back group scheme. -/
def finiteEtaleCoefficientFiberEquiv (x : Spec (CommRingCat.of K) ⟶ S) :
    letI := GroupScheme.pointsCoefficientModule K (GroupScheme.fiber K A x) R
      ((GroupScheme.fiberEndomorphismMap K A x).comp φ)
    (finiteEtaleCoefficientLocalSystem K A R φ).obj x ≃ₗ[R]
      GroupScheme.Points K (AlgebraicClosure K) (GroupScheme.fiber K A x).X := by
  letI := GroupScheme.pointsCoefficientModule K (GroupScheme.fiber K A x) R
    ((GroupScheme.fiberEndomorphismMap K A x).comp φ)
  exact {
    __ := GroupScheme.geometricFiberPointsAddEquiv K A x
    map_smul' r v := GroupScheme.geometricFiberPointsAddEquiv_map K A A x (φ r) v }

/-- The linear fibre comparison intertwines the arithmetic loop with the actual Galois action on fibre points. -/
theorem finiteEtaleCoefficientFiberEquiv_arithmetic (x : Spec (CommRingCat.of K) ⟶ S)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : Additive (geometricPointOver K x ⟶ A.X)) :
    letI := GroupScheme.pointsCoefficientModule K (GroupScheme.fiber K A x) R
      ((GroupScheme.fiberEndomorphismMap K A x).comp φ)
    finiteEtaleCoefficientFiberEquiv K A R φ x
        ((finiteEtaleCoefficientLocalSystem K A R φ).map (arithmeticFiberLoop K S x g) v) =
      g • finiteEtaleCoefficientFiberEquiv K A R φ x v := by
  change (GroupScheme.geometricFiberPointsAddEquiv K A x
    ((finiteEtaleCoefficientLocalSystem K A R φ).map (arithmeticFiberLoop K S x g) v)).toMul = _
  have h := finiteEtaleCoefficientLocalSystem_arithmetic K A R φ x g v
  change (finiteEtaleCoefficientLocalSystem K A R φ).map (arithmeticFiberLoop K S x g) v =
    Additive.ofMul (arithmeticFiberPointMap K x g ≫ v.toMul) at h
  rw [h]
  exact GroupScheme.geometricFiberPointsAddEquiv_arithmetic K A x g v

end AlgebraicGeometry.Scheme
