/- Assembled by AxiomProver. -/

module

public import Mathlib.CategoryTheory.Conj

/-! # Conjugation and restriction of intertwined categorical morphisms -/

@[expose] public section
namespace CategoryTheory.Iso
universe u v
variable {C : Type u} [Category.{v} C] {X Y : C}

/-- An intertwining isomorphism identifies automorphisms by inverse conjugation. -/
theorem conjAut_symm_eq_of_intertwines (e : X ≅ Y) (a : Aut X) (b : Aut Y)
    (h : e.hom ≫ b.hom = a.hom ≫ e.hom) : e.symm.conjAut b = a := by
  apply Iso.ext
  rw [Iso.conjAut_hom, Iso.conj_apply]
  change e.hom ≫ b.hom ≫ e.inv = a.hom
  rw [← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id]

end CategoryTheory.Iso

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {X Y X' Y' : C}

/-- An ambient intertwining square restricts through compatible inclusions when the
inclusion of the target is a monomorphism. -/
theorem intertwines_of_mono (i : X ⟶ X') (j : Y ⟶ Y') [Mono j]
    (e : X ⟶ Y) (a : X' ⟶ Y') (f : End X) (g : End Y) (F : End X') (G : End Y')
    (hi : f ≫ i = i ≫ F) (hj : g ≫ j = j ≫ G)
    (he : e ≫ j = i ≫ a) (ha : F ≫ a = a ≫ G) : f ≫ e = e ≫ g := by
  apply (cancel_mono j).mp
  calc
    (f ≫ e) ≫ j = f ≫ (i ≫ a) := by rw [Category.assoc, he]
    _ = (i ≫ F) ≫ a := by rw [← Category.assoc, hi]
    _ = i ≫ (a ≫ G) := by rw [Category.assoc, ha]
    _ = (e ≫ j) ≫ G := by rw [← Category.assoc, ← he]
    _ = e ≫ (g ≫ j) := by rw [Category.assoc, ← hj]
    _ = (e ≫ g) ≫ j := (Category.assoc _ _ _).symm

/-- Naturality restricts an ambient intertwining square to subfunctors whose target
inclusion is pointwise monic. The two source categories may be different. -/
theorem NatTrans.intertwines_of_mono {D E : Type*} [Category D] [Category E]
    {P P' : D ⥤ C} {Q Q' : E ⥤ C} (i : P ⟶ P') (j : Q ⟶ Q')
    (x : D) (y : E) [Mono (j.app y)] (u : End x) (v : End y)
    (e : P.obj x ⟶ Q.obj y) (a : P'.obj x ⟶ Q'.obj y)
    (he : e ≫ j.app y = i.app x ≫ a)
    (ha : P'.map u ≫ a = a ≫ Q'.map v) : P.map u ≫ e = e ≫ Q.map v :=
  CategoryTheory.intertwines_of_mono (i.app x) (j.app y) e a
    (P.map u) (Q.map v) (P'.map u) (Q'.map v)
    (i.naturality u) (j.naturality v) he ha

end CategoryTheory
