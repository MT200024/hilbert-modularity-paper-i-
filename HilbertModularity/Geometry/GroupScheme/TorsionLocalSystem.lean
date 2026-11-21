/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TorsionMonodromy
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.NatIso
public import HilbertModularity.CategoryTheory.ZModModule
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import HilbertModularity.Geometry.GroupScheme.TateMonodromy
public import HilbertModularity.Geometry.GroupScheme.TorsionTransitionComparison

/-! # The actual family of geometric torsion point groups -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S)) (n : ℕ)
  [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left]

/-- The actual finite étale torsion cover gives one family of native geometric torsion groups. -/
def torsionPointLocalSystem : Scheme.EtaleFiberGroupoid K S ⥤ AddCommGrpCat :=
  ((Scheme.finiteGroupFiberLocalSystem K (finiteEtaleTorsionObject A n)) ⋙
    CommGrpCat.toAddCommGrp).copyObj
      (fun x => AddCommGrpCat.of
        (AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n))
      (fun x => (finiteTorsionFiberPointsEquiv K x A n).toAddCommGrpIso)

/-- At every point the family is the ordinary torsion subgroup of the same group scheme. -/
@[simp]
theorem torsionPointLocalSystem_obj (x : Scheme.EtaleFiberGroupoid K S) :
    (torsionPointLocalSystem K A n).obj x = AddCommGrpCat.of
      (AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) := rfl

/-- Its action at each geometric loop is the already constructed native torsion monodromy. -/
@[simp]
theorem torsionPointLocalSystem_loop (x : Spec (CommRingCat.of K) ⟶ S)
    (σ : Scheme.etaleFundamentalGroup K x)
    (v : AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    (torsionPointLocalSystem K A n).map (Scheme.etaleFiberPath K S σ) v =
      (finiteTorsionMonodromy K x A n σ).toAdd v := rfl

/-- Path transport on native torsion points is the original transport on finite-cover fibres. -/
theorem torsionPointLocalSystem_map_apply {x y : Scheme.EtaleFiberGroupoid K S} (e : x ⟶ y)
    (v : AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    (torsionPointLocalSystem K A n).map e v =
      finiteTorsionFiberPointsEquiv K y A n (Additive.ofMul
        ((Scheme.finiteGroupFiberLocalSystem K (finiteEtaleTorsionObject A n)).map e
          ((finiteTorsionFiberPointsEquiv K x A n).symm v).toMul)) := rfl

local instance torsionPointZModModule (x : Scheme.EtaleFiberGroupoid K S) :
    Module (ZMod n) ((torsionPointLocalSystem K A n).obj x) :=
  AddSubgroup.torsionBy.zmodModule

/-- The native torsion family is linear over its natural residue coefficient ring. -/
def torsionModuleLocalSystem : Scheme.EtaleFiberGroupoid K S ⥤ ModuleCat (ZMod n) :=
  (torsionPointLocalSystem K A n).toZModModuleCat n

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Restriction along the canonical residue map gives the finite-level `p`-adic family. -/
def torsionPadicLocalSystem (n : ℕ) : Scheme.EtaleFiberGroupoid K S ⥤ ModuleCat ℤ_[p] :=
  torsionModuleLocalSystem K A (p ^ n) ⋙ ModuleCat.restrictScalars (PadicInt.toZModPow n)

/-- The finite-level family recovers the actual native torsion representation at every loop. -/
@[simp]
theorem torsionPadicLocalSystem_loop (x : Spec (CommRingCat.of K) ⟶ S)
    (σ : Scheme.etaleFundamentalGroup K x) (n : ℕ)
    (v : TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    (torsionPadicLocalSystem K A p n).map (Scheme.etaleFiberPath K S σ) v =
      torsionMonodromyRepresentation K x A p n σ v := rfl

/-- Every actual étale path commutes with multiplication-by-`p` between native torsion levels. -/
theorem torsionPadicLocalSystem_transition {x y : Scheme.EtaleFiberGroupoid K S}
    (e : x ⟶ y) (n : ℕ)
    (v : TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) (n + 1)) :
    TateModule.transition p (Additive (Scheme.geometricPointOver K y ⟶ A.X)) n
        ((torsionPadicLocalSystem K A p (n + 1)).map e v) =
      (torsionPadicLocalSystem K A p n).map e
        (TateModule.transition p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n v) := by
  let ex := finiteTorsionFiberPointsEquiv K x A (p ^ (n + 1))
  let ey := finiteTorsionFiberPointsEquiv K y A (p ^ n)
  obtain ⟨w, rfl⟩ := ex.surjective v
  change TateModule.transition p (Additive (Scheme.geometricPointOver K y ⟶ A.X)) n
      ((torsionPointLocalSystem K A (p ^ (n + 1))).map e (ex w)) =
    (torsionPointLocalSystem K A (p ^ n)).map e
      (TateModule.transition p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n (ex w))
  rw [torsionPointLocalSystem_map_apply, torsionPointLocalSystem_map_apply]
  rw [AddEquiv.symm_apply_apply]
  rw [← finiteTorsionFiberPointsEquiv_transition K x A p n w]
  rw [AddEquiv.symm_apply_apply]
  rw [← finiteTorsionFiberPointsEquiv_transition K y A p n]
  have h := congrArg (fun f => f w.toMul)
    (((Scheme.finiteGroupFiberLocalSystemFunctor K S).map
      (finiteEtaleTorsionTransition A p n)).naturality e)
  exact congrArg (fun z => ey (Additive.ofMul z)) h

end AlgebraicGeometry.GroupScheme

