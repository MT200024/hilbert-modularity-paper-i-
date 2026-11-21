/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.CommGroupObject
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
public import Mathlib.CategoryTheory.Limits.Yoneda

/-! # The group law on a representable geometric fibre

The group object obtained by applying a representable functor has exactly
the usual group law on the set of morphisms into the original group object.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

local instance coyonedaBraided (P : C) : (coyoneda.obj (Opposite.op P)).Braided :=
  Functor.Braided.ofChosenFiniteProducts _

/-- The tensor comparison on representable fibres sends two points to their product pairing. -/
theorem coyoneda_tensorator_apply (P X Y : C) (f : P ⟶ X) (g : P ⟶ Y) :
    Functor.LaxMonoidal.μ (coyoneda.obj (Opposite.op P)) X Y (f, g) = lift f g := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
    exact ConcreteCategory.congr_hom (CC := fun X => X)
      (Functor.Monoidal.μ_fst (coyoneda.obj (Opposite.op P)) X Y) (f, g)
  · rw [lift_snd]
    exact ConcreteCategory.congr_hom (CC := fun X => X)
      (Functor.Monoidal.μ_snd (coyoneda.obj (Opposite.op P)) X Y) (f, g)

set_option backward.isDefEq.respectTransparency false in
/-- The group fibre of a representable functor is the usual group of points, by the identity map. -/
def coyonedaCommGroupPointsEquiv (P : C) (A : CommGrp C) :
    ((coyoneda.obj (Opposite.op P)).mapCommGrp ⋙ commGrpTypeEquivalenceCommGrp.functor).obj A ≃*
      (P ⟶ A.X) where
  toEquiv := Equiv.refl _
  map_mul' f g := by
    change Functor.LaxMonoidal.μ (coyoneda.obj (Opposite.op P)) A.X A.X (f, g) ≫ μ[A.X] =
      lift f g ≫ μ[A.X]
    exact congrArg (fun h : P ⟶ A.X ⊗ A.X => h ≫ μ[A.X])
      (coyoneda_tensorator_apply P A.X A.X f g)

/-- The representable group-fibre identification is literally the identity on points. -/
@[simp]
theorem coyonedaCommGroupPointsEquiv_apply (P : C) (A : CommGrp C)
    (f : ((coyoneda.obj (Opposite.op P)).mapCommGrp ⋙
      commGrpTypeEquivalenceCommGrp.functor).obj A) :
    coyonedaCommGroupPointsEquiv P A f = f := rfl

end CategoryTheory

namespace CategoryTheory.CommGrp
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (P : C) (A : CommGrp C)

/-- Endomorphisms of a commutative group object act as a ring on its ordinary group of points. -/
def pointsEndomorphismMap : End A →+* AddMonoid.End (Additive (P ⟶ A.X)) where
  toFun f := (IsMonHom.monoidHom f.hom.hom.hom P).toAdditive
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    exact Category.comp_id x.toMul
  map_mul' f g := by
    apply AddMonoidHom.ext
    intro x
    exact (Category.assoc x.toMul g.hom.hom.hom f.hom.hom.hom).symm
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    exact MonObj.comp_one x.toMul
  map_add' f g := by
    apply AddMonoidHom.ext
    intro x
    exact MonObj.comp_mul x.toMul f.hom.hom.hom g.hom.hom.hom

/-- The point action is postcomposition with the original group-object endomorphism. -/
@[simp]
theorem pointsEndomorphismMap_apply (f : End A) (x : Additive (P ⟶ A.X)) :
    (pointsEndomorphismMap P A f x).toMul = x.toMul ≫ f.hom.hom.hom := rfl

end CategoryTheory.CommGrp
