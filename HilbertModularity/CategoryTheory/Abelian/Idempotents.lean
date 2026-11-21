/- Assembled by AxiomProver. -/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.Idempotents

/-! # Decomposition into images of complete orthogonal projectors -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {I : Type w} [Fintype I] {X : C} {e : I → End X}
  (h : CompleteOrthogonalIdempotents e)

/-- The images of complete orthogonal projectors form a bicone on the original object. -/
def idempotentImageBicone : Bicone (fun i => image (e i)) where
  pt := X
  π i := factorThruImage (e i)
  ι i := image.ι (e i)
  ι_π i j := by
    classical
    by_cases hij : i = j
    · subst j
      simp only [dite_eq_left rfl, eqToHom_refl]
      apply (cancel_epi (factorThruImage (e i))).1
      apply (cancel_mono (image.ι (e i))).1
      simpa only [End.asHom, End.mul_def, Category.assoc, image.fac_assoc, image.fac, Category.comp_id,
        Category.id_comp] using congrArg End.asHom (h.idem i).eq
    · simp only [dite_eq_right hij]
      apply (cancel_epi (factorThruImage (e i))).1
      apply (cancel_mono (image.ι (e j))).1
      simpa only [End.asHom, End.mul_def, Category.assoc, image.fac_assoc, image.fac, comp_zero,
        zero_comp] using congrArg End.asHom (h.ortho (Ne.symm hij))

/-- Completeness makes the image bicone a simultaneous product and coproduct. -/
def idempotentImageBiconeIsBilimit : (idempotentImageBicone h).IsBilimit :=
  isBilimitOfTotal _ (by
    let f : End X →+ (X ⟶ X) :=
      { toFun := End.asHom, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have ht := congrArg f h.complete
    rw [map_sum] at ht
    change (∑ i, (e i).asHom) = 𝟙 X at ht
    change (∑ i, factorThruImage (e i) ≫ image.ι (e i)) = 𝟙 X
    calc
      _ = ∑ i, (e i).asHom := by
        apply Finset.sum_congr rfl
        intro i _
        exact image.fac (e i)
      _ = 𝟙 X := ht)

/-- Complete orthogonal projectors decompose the object as the biproduct of their images. -/
def idempotentImageBiproductIso : X ≅ biproduct (fun i => image (e i)) :=
  (idempotentImageBiconeIsBilimit h).isLimit.conePointUniqueUpToIso (biproduct.isLimit _)

/-- The decomposition coordinate is the canonical factorization through its projector image. -/
@[reassoc]
theorem idempotentImageBiproductIso_hom_π (i : I) :
    (idempotentImageBiproductIso h).hom ≫ biproduct.π (fun i => image (e i)) i =
      factorThruImage (e i) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (idempotentImageBiconeIsBilimit h).isLimit (biproduct.isLimit _) ⟨i⟩

end CategoryTheory.Limits
