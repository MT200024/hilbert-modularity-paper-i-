/- Assembled by AxiomProver. -/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.CofilteredSystem

/-! # Comparing finite-valued functors through their category of elements

A section over the cofiltered category of elements is precisely a compatible
choice of images for all fibre points.
-/

@[expose] public section
namespace CategoryTheory.Functor
universe u v w
variable {C : Type u} [Category.{v} C]

/-- A finite-valued functor receives a natural transformation from a functor with
cofiltered elements if it is nonempty wherever the source functor is nonempty. -/
theorem nonempty_natTrans_of_finite (F G : C ⥤ Type w)
    [IsCofilteredOrEmpty F.Elements] [∀ X, Finite (G.obj X)]
    (h : ∀ X, Nonempty (F.obj X) → Nonempty (G.obj X)) : Nonempty (F ⟶ G) := by
  let H := Elements.π F ⋙ G
  have : ∀ X : F.Elements, Finite (H.obj X) := fun X =>
    inferInstanceAs (Finite (G.obj X.obj))
  have : ∀ X : F.Elements, Nonempty (H.obj X) := fun X => h X.obj ⟨X.val⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system H
  refine ⟨{ app := fun X => ↾fun x => s (F.elementsMk X x), naturality := ?_ }⟩
  intro X Y f
  ext x
  change s (F.elementsMk Y (F.map f x)) = G.map f (s (F.elementsMk X x))
  exact (hs (⟨f, rfl⟩ : F.elementsMk X x ⟶ F.elementsMk Y (F.map f x))).symm

end CategoryTheory.Functor
