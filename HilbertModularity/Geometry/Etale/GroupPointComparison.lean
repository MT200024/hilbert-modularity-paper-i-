/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.GroupObjectPoints
public import HilbertModularity.Geometry.Etale.FiniteGroupScheme

/-! # Finite group fibres and the original geometric point group

The group structure obtained from finite étale covers agrees with the given
group-scheme law on its actual geometric points. The comparison is the identity
on the underlying scheme morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory finiteEtaleBraidedCategory
  CategoryTheory.coyonedaBraided

variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S) (A : CommGrp (Over S))
  [AlgebraicGeometry.Etale A.X.hom] [IsFinite A.X.hom]

/-- Fibre formation and finite-group-scheme reflection identify the two actual group fibres. -/
def finiteGroupFiberSchemeIso :
    (finiteGroupFiberFunctor K x).obj (finiteEtaleGroupObject A) ≅
      ((coyoneda.obj (Opposite.op (geometricPointOver K x))).mapCommGrp ⋙
        commGrpTypeEquivalenceCommGrp.functor).obj A := by
  let P := geometricPointOver K x
  let e : finiteGeometricFiberFunctor K x ≅
      finiteEtaleForget S ⋙ coyoneda.obj (Opposite.op P) := Iso.refl _
  exact commGrpTypeEquivalenceCommGrp.functor.mapIso
    ((Functor.mapCommGrpNatIso e).app (finiteEtaleGroupObject A) ≪≫
      (Functor.mapCommGrpCompIso (F := finiteEtaleForget S)
        (G := coyoneda.obj (Opposite.op P))).app (finiteEtaleGroupObject A) ≪≫
      (coyoneda.obj (Opposite.op P)).mapCommGrp.mapIso (finiteEtaleGroupObjectIso A))

/-- The finite group fibre is the usual geometric group of points of the original group scheme. -/
def finiteGroupFiberPointsEquiv :
    (finiteGroupFiberFunctor K x).obj (finiteEtaleGroupObject A) ≃*
      (geometricPointOver K x ⟶ A.X) :=
  (finiteGroupFiberSchemeIso K x A).commGroupIsoToMulEquiv.trans
    (CategoryTheory.coyonedaCommGroupPointsEquiv (geometricPointOver K x) A)

/-- The group comparison keeps every original geometric point unchanged. -/
@[simp]
theorem finiteGroupFiberPointsEquiv_apply
    (f : (finiteGroupFiberFunctor K x).obj (finiteEtaleGroupObject A)) :
    finiteGroupFiberPointsEquiv K x A f = f := by
  change (f : geometricPointOver K x ⟶ A.X) ≫ 𝟙 A.X = f
  exact Category.comp_id _


variable {B : CommGrp (Over S)}
  [AlgebraicGeometry.Etale B.X.hom] [IsFinite B.X.hom]

/-- The geometric point comparison respects each original group-scheme morphism. -/
theorem finiteGroupFiberPointsEquiv_natural (f : A ⟶ B)
    (v : (finiteGroupFiberFunctor K x).obj (finiteEtaleGroupObject A)) :
    finiteGroupFiberPointsEquiv K x B
        ((finiteGroupFiberFunctor K x).map (finiteEtaleGroupObjectMap f) v) =
      finiteGroupFiberPointsEquiv K x A v ≫ f.hom.hom.hom := by
  simp only [finiteGroupFiberPointsEquiv_apply]
  have h : ((finiteEtaleForget S).mapCommGrp.map
      (finiteEtaleGroupObjectMap f)).hom.hom.hom = f.hom.hom.hom := by
    rw [finiteEtaleGroupObjectMap_forget]
    change (𝟙 A.X) ≫ f.hom.hom.hom ≫ (𝟙 B.X) = f.hom.hom.hom
    simp only [Category.id_comp, Category.comp_id]
  exact congrArg (fun g : A.X ⟶ B.X => (v : geometricPointOver K x ⟶ A.X) ≫ g) h

end AlgebraicGeometry.Scheme
