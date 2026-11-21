/- Assembled by AxiomProver. -/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! # Cohomology under an equivalence of sites

Transport of abelian sheaves along an equivalence of sites is exact. Together
with the canonical transport of constant sheaves, it therefore induces an
additive equivalence on their actual Ext-defined cohomology groups.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits Abelian

universe u v u' v' w t t'

section Ext

variable {A : Type*} [Category* A] [Abelian A] [HasExt.{t} A]

/-- Transport of the contravariant argument of an Ext group along an isomorphism. -/
def Abelian.Ext.precompIso {X Y : A} (e : X ≅ Y) (Z : A) (n : ℕ) :
    Ext Y Z n ≃+ Ext X Z n where
  toFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp

end Ext

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
  [e.inverse.IsDenseSubsite K J]

/-- The site equivalence transports constant sheaves by uniqueness of the left
adjoint to sections at a terminal object. -/
def Equivalence.sheafCongrConstant (A : Type*) [Category* A]
    [HasWeakSheafify J A] [HasWeakSheafify K A] {T : C} (hT : IsTerminal T) :
    constantSheaf J A ⋙ (e.sheafCongr J K A).functor ≅ constantSheaf K A :=
  ((constantSheafAdj J A hT).comp (e.sheafCongr J K A).toAdjunction).leftAdjointUniq
    (constantSheafAdj K A (hT.isTerminalObj e.functor T))

/-- Transport of abelian sheaves preserves addition of morphisms. -/
instance Equivalence.sheafCongr_functor_additive :
    (e.sheafCongr J K AddCommGrpCat.{w}).functor.Additive where
  map_add := by
    intro F G f g
    ext U x
    rfl

variable [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{t} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{t'} (Sheaf K AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- An equivalence of sites induces an equivalence on actual sheaf cohomology. -/
def Equivalence.sheafCongrCohomology {T : C} (hT : IsTerminal T)
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    F.H n ≃+ ((e.sheafCongr J K AddCommGrpCat.{w}).functor.obj F).H n :=
  (AddEquiv.ofBijective
    ((e.sheafCongr J K AddCommGrpCat.{w}).functor.mapExtAddHom
      ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) F n)
    ((e.sheafCongr J K AddCommGrpCat.{w}).functor.mapExt_bijective_of_preservesInjectiveObjects
      _ _ n)).trans
    (Ext.precompIso ((e.sheafCongrConstant J K AddCommGrpCat.{w} hT).app
      (AddCommGrpCat.of (ULift ℤ))).symm _ n)

/-- The cohomology equivalence is the exact-functor map followed by the canonical
constant-sheaf comparison. -/
theorem Equivalence.sheafCongrCohomology_apply {T : C} (hT : IsTerminal T)
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : F.H n) :
    e.sheafCongrCohomology J K hT F n x =
      (Ext.mk₀ ((e.sheafCongrConstant J K AddCommGrpCat.{w} hT).app
        (AddCommGrpCat.of (ULift ℤ))).inv).comp
          (x.mapExactFunctor (e.sheafCongr J K AddCommGrpCat.{w}).functor) (zero_add n) := rfl

/-- Site transport is natural in the coefficient sheaf. -/
theorem Equivalence.sheafCongrCohomology_natural {T : C} (hT : IsTerminal T)
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (n : ℕ) (x : F.H n) :
    e.sheafCongrCohomology J K hT G n (Sheaf.H.map f n x) =
      Sheaf.H.map ((e.sheafCongr J K AddCommGrpCat.{w}).functor.map f) n
        (e.sheafCongrCohomology J K hT F n x) := by
  simp only [Equivalence.sheafCongrCohomology_apply, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

end CategoryTheory
