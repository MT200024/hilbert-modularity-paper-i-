/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TorsionPoints
public import HilbertModularity.Geometry.Etale.GroupFiberAction
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Topology.Algebra.Group.Basic
public import HilbertModularity.RepresentationTheory.ZMod

/-! # Monodromy on the actual torsion groups of geometric points

Finite étale monodromy acts on the native torsion subgroup through the
identity-on-points comparison with the finite étale kernel fibre.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory

variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S) (A : CommGrp (Over S)) (n : ℕ)
  [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left]

/-- Monodromy acts by additive automorphisms on the actual geometric torsion subgroup. -/
def finiteTorsionMonodromy : Scheme.etaleFundamentalGroup K x →*
    Multiplicative (AddAut (AddSubgroup.torsionBy
      (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n)) :=
  ((AddAut.congr (finiteTorsionFiberPointsEquiv K x A n)).toMultiplicative.toMonoidHom).comp
    (((AddAutAdditive
      ((Scheme.finiteGroupFiberFunctor K x).obj (finiteEtaleTorsionObject A n))).symm.toMultiplicativeRight.toMonoidHom).comp
      (MulDistribMulAction.toMulAut (Scheme.etaleFundamentalGroup K x)
        ((Scheme.finiteGroupFiberFunctor K x).obj (finiteEtaleTorsionObject A n))))

/-- Native torsion monodromy is the original finite-fibre action under the point comparison. -/
@[simp]
theorem finiteTorsionMonodromy_apply (σ : Scheme.etaleFundamentalGroup K x)
    (v : AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    (finiteTorsionMonodromy K x A n σ).toAdd v =
      finiteTorsionFiberPointsEquiv K x A n (Additive.ofMul (σ •
        ((finiteTorsionFiberPointsEquiv K x A n).symm v).toMul)) := rfl

local instance torsionPointsZModModule :
    Module (ZMod n)
      (AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :=
  AddSubgroup.torsionBy.zmodModule

/-- Finite monodromy is linear over the natural residue coefficient ring. -/
def finiteTorsionRepresentation : Representation (ZMod n) (Scheme.etaleFundamentalGroup K x)
    (AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :=
  Representation.ofAddAutZMod n (finiteTorsionMonodromy K x A n)

/-- Restriction along the arithmetic Galois map gives the original action on torsion points. -/
theorem finiteTorsionMonodromy_arithmetic
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    ((finiteTorsionMonodromy K x A n
      (Scheme.galoisToEtaleFundamentalGroup K x g)).toAdd v).val.toMul =
      Scheme.arithmeticFiberPointMap K x g ≫ v.val.toMul := by
  let e := finiteTorsionFiberPointsEquiv K x A n
  have hv : (e.symm v).toMul ≫ Grp.kernelInclusion (n • 𝟙 A).hom = v.val.toMul := by
    have h := congrArg (fun w => w.val.toMul) (e.apply_symm_apply v)
    change (finiteTorsionFiberPointsEquiv K x A n (e.symm v)).val.toMul = v.val.toMul at h
    rwa [finiteTorsionFiberPointsEquiv_apply] at h
  rw [finiteTorsionMonodromy_apply]
  change (finiteTorsionFiberPointsEquiv K x A n (Additive.ofMul
    (Scheme.galoisToEtaleFundamentalGroup K x g • (e.symm v).toMul))).val.toMul = _
  rw [finiteTorsionFiberPointsEquiv_apply, Scheme.finiteGroupFiber_arithmetic_smul]
  change (Scheme.arithmeticFiberPointMap K x g ≫ (e.symm v).toMul) ≫
    Grp.kernelInclusion (n • 𝟙 A).hom = Scheme.arithmeticFiberPointMap K x g ≫ v.val.toMul
  exact (Category.assoc (Scheme.arithmeticFiberPointMap K x g) (e.symm v).toMul
    (Grp.kernelInclusion (n • 𝟙 A).hom)).trans
      (congrArg (fun w => Scheme.arithmeticFiberPointMap K x g ≫ w) hv)


variable [TopologicalSpace (Additive (Scheme.geometricPointOver K x ⟶ A.X))]
  [DiscreteTopology (Additive (Scheme.geometricPointOver K x ⟶ A.X))]

/-- Geometric monodromy on the native torsion subgroup is jointly continuous. -/
theorem continuous_finiteTorsionMonodromy :
    Continuous (fun gv : Scheme.etaleFundamentalGroup K x ×
      AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n =>
        (finiteTorsionMonodromy K x A n gv.1).toAdd gv.2) := by
  let e := finiteTorsionFiberPointsEquiv K x A n
  have hi : Continuous (fun v => (e.symm v).toMul) := continuous_of_discreteTopology
  have ho : Continuous (fun v : (Scheme.finiteGroupFiberFunctor K x).obj
      (finiteEtaleTorsionObject A n) => e (Additive.ofMul v)) := continuous_of_discreteTopology
  change Continuous (fun gv : Scheme.etaleFundamentalGroup K x ×
      AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n =>
    e (Additive.ofMul (gv.1 • (e.symm gv.2).toMul)))
  exact ho.comp (continuous_fst.smul (hi.comp continuous_snd))

end AlgebraicGeometry.GroupScheme
