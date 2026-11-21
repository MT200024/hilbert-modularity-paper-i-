/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Evaluation of natural module endomorphisms -/

@[expose] public noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace ModuleCat
universe u v w z
variable (R : Type u) [CommRing R] {C : Type w} [Category.{v} C]
  (F : C ⥤ ModuleCat.{z} R) (x : C)

/-- Evaluate a natural endomorphism at an object as an endomorphism of its native module. -/
def functorEndApp : End F →ₐ[R] Module.End R (F.obj x) where
  toFun f := (f.app x).hom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end ModuleCat
