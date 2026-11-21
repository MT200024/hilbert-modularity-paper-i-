/- Assembled by AxiomProver. -/

module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Addition of morphisms of commutative group objects

Commutative group objects in a cartesian monoidal category form a preadditive
category. Addition is induced by the group law of the target. In particular,
endomorphisms of a commutative group scheme form a ring.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.CommGrp

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- The usual additive notation for the pointwise group of group-object morphisms. -/
def homAdditiveEquiv (A B : CommGrp C) :
    (A ⟶ B) ≃ Additive (A.toGrp ⟶ B.toGrp) where
  toFun f := Additive.ofMul f.hom
  invFun f := InducedCategory.homMk f.toMul
  left_inv _ := rfl
  right_inv _ := rfl

/-- Morphisms of commutative group objects add by the group law of their target. -/
instance : Preadditive (CommGrp C) where
  homGroup A B := (homAdditiveEquiv A B).addCommGroup
  add_comp A B D f g h := by
    apply CommGrp.hom_ext
    change (f.hom.hom.hom * g.hom.hom.hom) ≫ h.hom.hom.hom =
      f.hom.hom.hom ≫ h.hom.hom.hom * g.hom.hom.hom ≫ h.hom.hom.hom
    exact MonObj.mul_comp _ _ _
  comp_add A B D f g h := by
    apply CommGrp.hom_ext
    change f.hom.hom.hom ≫ (g.hom.hom.hom * h.hom.hom.hom) =
      f.hom.hom.hom ≫ g.hom.hom.hom * f.hom.hom.hom ≫ h.hom.hom.hom
    exact MonObj.comp_mul _ _ _

/-- Addition of group-scheme morphisms is pointwise multiplication on the underlying object. -/
@[simp]
theorem add_hom {A B : CommGrp C} (f g : A ⟶ B) :
    (f + g).hom.hom.hom = f.hom.hom.hom * g.hom.hom.hom := rfl

/-- The zero group-scheme morphism is the constant unit map. -/
@[simp]
theorem zero_hom (A B : CommGrp C) :
    (0 : A ⟶ B).hom.hom.hom = (1 : A.X ⟶ B.X) := rfl

/-- Negation of a group-scheme morphism uses inversion in the target. -/
@[simp]
theorem neg_hom {A B : CommGrp C} (f : A ⟶ B) :
    (-f).hom.hom.hom = f.hom.hom.hom⁻¹ := rfl

end CategoryTheory.CommGrp

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) [F.Braided]

/-- A functor preserving finite products preserves addition of group-object morphisms. -/
instance mapCommGrp_additive : F.mapCommGrp.Additive where
  map_add {A B f g} := by
    apply CommGrp.hom_ext
    change F.map (f.hom.hom.hom * g.hom.hom.hom) =
      F.map f.hom.hom.hom * F.map g.hom.hom.hom
    exact F.map_mul f.hom.hom.hom g.hom.hom.hom

end CategoryTheory.Functor
