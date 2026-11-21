/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.CommGroupObject

/-! # Reflecting commutative group objects along fully faithful functors -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided]

/-- Reflect a commutative group law on the image of an object through a fully faithful functor. -/
def FullyFaithful.commGrp (hF : F.FullyFaithful) (X : C)
    [GrpObj (F.obj X)] [IsCommMonObj (F.obj X)] : CommGrp C := by
  letI : GrpObj X := hF.grpObj X
  exact { X := X, comm := {
    mul_comm := hF.map_injective (by
      change F.map ((β_ X X).hom ≫ hF.preimage
        (OplaxMonoidal.δ F X X ≫ μ[F.obj X])) =
          F.map (hF.preimage (OplaxMonoidal.δ F X X ≫ μ[F.obj X]))
      rw [F.map_comp, hF.map_preimage]
      simp only [Functor.map_braiding, Category.assoc,
        Monoidal.μ_δ_assoc, IsCommMonObj.mul_comm]) } }

/-- Applying the functor to the reflected commutative group recovers the original group law. -/
def FullyFaithful.commGrpMapIso (hF : F.FullyFaithful) (X : C)
    [GrpObj (F.obj X)] [IsCommMonObj (F.obj X)] :
    F.mapCommGrp.obj (hF.commGrp X) ≅ CommGrp.mk (F.obj X) :=
  CommGrp.mkIso (Iso.refl _) (by
    change (LaxMonoidal.ε F ≫ F.map (hF.preimage
      (OplaxMonoidal.η F ≫ η[F.obj X]))) ≫ 𝟙 _ = η[F.obj X]
    simp) (by
    change (LaxMonoidal.μ F X X ≫ F.map (hF.preimage
      (OplaxMonoidal.δ F X X ≫ μ[F.obj X]))) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ[F.obj X]
    simp)

end CategoryTheory.Functor
namespace CategoryTheory.CommGrp

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- A subgroup object of a commutative group object is commutative. -/
def ofMono {X : C} [GrpObj X] (A : CommGrp C) (f : X ⟶ A.X)
    [Mono f] [IsMonHom f] : CommGrp C where
  X := X
  comm := by
    refine { mul_comm := ?_ }
    apply (cancel_mono f).1
    simp only [Category.assoc, IsMonHom.mul_hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]

end CategoryTheory.CommGrp
