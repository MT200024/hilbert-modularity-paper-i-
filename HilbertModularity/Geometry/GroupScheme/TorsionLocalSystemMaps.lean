/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TorsionMaps
public import HilbertModularity.Geometry.GroupScheme.TorsionLocalSystem

/-! # Natural maps of the native geometric torsion families -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S)) (n : ℕ)
  [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left]

/-- The native torsion-point family is naturally the actual finite-cover fibre family. -/
def torsionPointLocalSystemIso :
    (Scheme.finiteGroupFiberLocalSystem K (finiteEtaleTorsionObject A n) ⋙
      CommGrpCat.toAddCommGrp) ≅ torsionPointLocalSystem K A n := by
  unfold torsionPointLocalSystem
  exact Functor.isoCopyObj _ _ _

variable {A} {B : CommGrp (Over S)}
  [IsFinite (n • 𝟙 B).hom.hom.hom.left] [Etale (n • 𝟙 B).hom.hom.hom.left]

/-- A morphism of group schemes induces a natural transformation of their native torsion families. -/
def torsionPointLocalSystemMap (f : A ⟶ B) :
    torsionPointLocalSystem K A n ⟶ torsionPointLocalSystem K B n :=
  (torsionPointLocalSystemIso K A n).inv ≫
    whiskerRight (torsionGroupLocalSystemMap n K f) CommGrpCat.toAddCommGrp ≫
      (torsionPointLocalSystemIso K B n).hom

/-- The native family map is the original finite-cover map under the point comparisons. -/
@[simp]
theorem torsionPointLocalSystemMap_apply (f : A ⟶ B) (x : Scheme.EtaleFiberGroupoid K S)
    (v : AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    (torsionPointLocalSystemMap K n f).app x v =
      finiteTorsionFiberPointsEquiv K x B n (Additive.ofMul
        ((Scheme.finiteGroupFiberFunctor K x).map (finiteEtaleTorsionMap n f)
          ((finiteTorsionFiberPointsEquiv K x A n).symm v).toMul)) := rfl

/-- At every geometric point the natural transformation is the actual scheme map on torsion. -/
theorem torsionPointLocalSystemMap_point (f : A ⟶ B) (x : Scheme.EtaleFiberGroupoid K S)
    (v : AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    ((torsionPointLocalSystemMap K n f).app x v).val.toMul = v.val.toMul ≫ f.hom.hom.hom := by
  rw [torsionPointLocalSystemMap_apply]
  have h := finiteTorsionFiberPointsEquiv_map n K x f
    ((finiteTorsionFiberPointsEquiv K x A n).symm v)
  rw [AddEquiv.apply_symm_apply] at h
  exact h

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] torsionPointZModModule
variable (K : Type u) [Field K] {S : Scheme.{u}} {A B : CommGrp (Over S)} (n : ℕ)
  [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left]
  [IsFinite (n • 𝟙 B).hom.hom.hom.left] [Etale (n • 𝟙 B).hom.hom.hom.left]

/-- The natural transformation on native torsion points is linear for the residue coefficients. -/
def torsionModuleLocalSystemMap (f : A ⟶ B) :
    torsionModuleLocalSystem K A n ⟶ torsionModuleLocalSystem K B n :=
  (torsionPointLocalSystemMap K n f).toZModModuleCat n

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} {A B : CommGrp (Over S)}
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 B).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 B).hom.hom.hom.left]

/-- The same torsion-family morphism is linear over the compatible p-adic coefficients. -/
def torsionPadicLocalSystemMap (f : A ⟶ B) (n : ℕ) :
    torsionPadicLocalSystem K A p n ⟶ torsionPadicLocalSystem K B p n :=
  whiskerRight (torsionModuleLocalSystemMap K (p ^ n) f)
    (ModuleCat.restrictScalars (PadicInt.toZModPow n))

/-- At every point, the p-adic family map is the original scheme morphism on torsion. -/
theorem torsionPadicLocalSystemMap_point (f : A ⟶ B) (n : ℕ)
    (x : Scheme.EtaleFiberGroupoid K S)
    (v : TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    ((torsionPadicLocalSystemMap K p f n).app x v).val.toMul =
      v.val.toMul ≫ f.hom.hom.hom :=
  torsionPointLocalSystemMap_point K (p ^ n) f x v

/-- The p-adic torsion-family map is exactly the ordinary torsion map of geometric points. -/
theorem torsionPadicLocalSystemMap_eq (f : A ⟶ B) (n : ℕ)
    (x : Scheme.EtaleFiberGroupoid K S)
    (v : TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    (torsionPadicLocalSystemMap K p f n).app x v =
      TateModule.torsionMap p
        (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive n v := by
  apply Subtype.ext
  exact torsionPadicLocalSystemMap_point K p f n x v


end AlgebraicGeometry.GroupScheme
