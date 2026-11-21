/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.TorsionFunctor
public import HilbertModularity.Geometry.GroupScheme.TorsionPoints

/-! # Morphisms of the actual finite étale torsion covers -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory torsionObjectEtale torsionObjectIsFinite
variable {S : Scheme.{u}} {A B D : CommGrp (Over S)} (n : ℕ)
  [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left]
  [IsFinite (n • 𝟙 B).hom.hom.hom.left] [Etale (n • 𝟙 B).hom.hom.hom.left]

/-- A group-scheme morphism induces a morphism of its actual finite étale torsion covers. -/
def finiteEtaleTorsionMap (f : A ⟶ B) :
    finiteEtaleTorsionObject A n ⟶ finiteEtaleTorsionObject B n :=
  Scheme.finiteEtaleGroupObjectMap (CommGrp.torsionMap f n)

/-- The map of actual torsion covers preserves identity morphisms. -/
@[simp]
theorem finiteEtaleTorsionMap_id :
    finiteEtaleTorsionMap n (𝟙 A) = 𝟙 (finiteEtaleTorsionObject A n) := by
  unfold finiteEtaleTorsionMap
  rw [CommGrp.torsionMap_id]
  exact Scheme.finiteEtaleGroupObjectMap_id

/-- Composition of group-scheme maps induces composition on the actual torsion covers. -/
@[simp]
theorem finiteEtaleTorsionMap_comp
    [IsFinite (n • 𝟙 D).hom.hom.hom.left] [Etale (n • 𝟙 D).hom.hom.hom.left]
    (f : A ⟶ B) (g : B ⟶ D) :
    finiteEtaleTorsionMap n (f ≫ g) = finiteEtaleTorsionMap n f ≫ finiteEtaleTorsionMap n g := by
  unfold finiteEtaleTorsionMap
  rw [CommGrp.torsionMap_comp]
  exact Scheme.finiteEtaleGroupObjectMap_comp _ _

/-- Every actual group-scheme morphism induces a natural map of its torsion fibre families. -/
def torsionGroupLocalSystemMap (K : Type u) [Field K] (f : A ⟶ B) :
    Scheme.finiteGroupFiberLocalSystem K (finiteEtaleTorsionObject A n) ⟶
      Scheme.finiteGroupFiberLocalSystem K (finiteEtaleTorsionObject B n) :=
  (Scheme.finiteGroupFiberLocalSystemFunctor K S).map (finiteEtaleTorsionMap n f)

/-- The finite-cover map sends each ordinary torsion point through the original scheme morphism. -/
theorem finiteTorsionFiberPointsEquiv_map (K : Type u) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ S) (f : A ⟶ B)
    (v : Additive ((Scheme.finiteGroupFiberFunctor K x).obj (finiteEtaleTorsionObject A n))) :
    (finiteTorsionFiberPointsEquiv K x B n (Additive.ofMul
      ((Scheme.finiteGroupFiberFunctor K x).map (finiteEtaleTorsionMap n f) v.toMul))).val.toMul =
      (finiteTorsionFiberPointsEquiv K x A n v).val.toMul ≫ f.hom.hom.hom := by
  rw [finiteTorsionFiberPointsEquiv_apply, finiteTorsionFiberPointsEquiv_apply]
  have h := Scheme.finiteGroupFiberPointsEquiv_natural K x
    (CommGrp.torsionObject A n) (CommGrp.torsionMap f n) v.toMul
  simp only [Scheme.finiteGroupFiberPointsEquiv_apply] at h
  change (Scheme.finiteGroupFiberFunctor K x).map (finiteEtaleTorsionMap n f) v.toMul =
    v.toMul ≫ (CommGrp.torsionMap f n).hom.hom.hom at h
  erw [h]
  exact (Category.assoc v.toMul (CommGrp.torsionMap f n).hom.hom.hom
    (show (CommGrp.torsionObject B n).X ⟶ B.X from Grp.kernelInclusion (n • 𝟙 B).hom)).trans
      ((congrArg (fun k : (CommGrp.torsionObject A n).X ⟶ B.X => v.toMul ≫ k)
        (CommGrp.torsionMap_inclusion f n)).trans
          (Category.assoc v.toMul
            (show (CommGrp.torsionObject A n).X ⟶ A.X from Grp.kernelInclusion (n • 𝟙 A).hom)
            f.hom.hom.hom).symm)

end AlgebraicGeometry.GroupScheme

