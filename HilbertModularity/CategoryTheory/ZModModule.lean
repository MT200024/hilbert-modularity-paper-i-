/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.ZMod

/-! # Linearizing additive-group-valued functors over residue rings -/

@[expose] public section
namespace CategoryTheory.Functor
universe v u w
variable {C : Type u} [Category.{v} C] (F : C ⥤ AddCommGrpCat.{w})
  (n : ℕ) [∀ X, Module (ZMod n) (F.obj X)]

/-- Every additive-group-valued functor with `ZMod n`-module objects is canonically linear. -/
def toZModModuleCat : C ⥤ ModuleCat (ZMod n) where
  obj X := ModuleCat.of (ZMod n) (F.obj X)
  map f := ModuleCat.ofHom ((F.map f).hom.toZModLinearMap n)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : F.obj X ⟶ F.obj X => f v) (F.map_id X)
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    exact congrArg (fun h : F.obj X ⟶ F.obj Z => h v) (F.map_comp f g)

/-- Linearization leaves the actual maps of underlying groups unchanged. -/
@[simp]
theorem toZModModuleCat_map_apply {X Y : C} (f : X ⟶ Y) (v : F.obj X) :
    (F.toZModModuleCat n).map f v = F.map f v := rfl

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans
universe v u w
variable {C : Type u} [Category.{v} C] {F G : C ⥤ AddCommGrpCat.{w}}
  (n : ℕ) [∀ X, Module (ZMod n) (F.obj X)] [∀ X, Module (ZMod n) (G.obj X)]

/-- A natural transformation of residue-module-valued additive groups is canonically linear. -/
def toZModModuleCat (η : F ⟶ G) : F.toZModModuleCat n ⟶ G.toZModModuleCat n where
  app X := ModuleCat.ofHom ((η.app X).hom.toZModLinearMap n)
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    exact congrArg (fun h : F.obj X ⟶ G.obj Y => h v) (η.naturality f)

/-- Linearization preserves every component of the original natural transformation. -/
@[simp]
theorem toZModModuleCat_app_apply (η : F ⟶ G) (X : C) (v : F.obj X) :
    (η.toZModModuleCat n).app X v = η.app X v := rfl

end CategoryTheory.NatTrans
