/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.EtaleKernel
public import HilbertModularity.Geometry.Etale.GroupPointComparison
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Geometric fibres of finite étale torsion group schemes

The actual geometric fibre of the kernel of multiplication identifies with the
ordinary torsion subgroup of the geometric point group. This comparison retains
the original scheme morphisms and their additive group law.
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

local instance torsionObjectEtale : Etale (CommGrp.torsionObject A n).X.hom :=
  kernel_etale (n • 𝟙 A)

local instance torsionObjectIsFinite : IsFinite (CommGrp.torsionObject A n).X.hom :=
  kernel_isFinite (n • 𝟙 A)

/-- The finite étale torsion fibre is the ordinary torsion subgroup of geometric points. -/
def finiteTorsionFiberPointsEquiv :
    Additive ((Scheme.finiteGroupFiberFunctor K x).obj (finiteEtaleTorsionObject A n)) ≃+
      AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n :=
  (Scheme.finiteGroupFiberPointsEquiv K x (CommGrp.torsionObject A n)).toAdditive.trans
    (CommGrp.torsionPointAddEquiv A n (Scheme.geometricPointOver K x))

/-- The torsion-fibre comparison sends a point to its image under the actual kernel inclusion. -/
@[simp]
theorem finiteTorsionFiberPointsEquiv_apply
    (v : Additive ((Scheme.finiteGroupFiberFunctor K x).obj (finiteEtaleTorsionObject A n))) :
    (finiteTorsionFiberPointsEquiv K x A n v).val.toMul =
      v.toMul ≫ Grp.kernelInclusion (n • 𝟙 A).hom := by
  change Scheme.finiteGroupFiberPointsEquiv K x (CommGrp.torsionObject A n) v.toMul ≫
    Grp.kernelInclusion (n • 𝟙 A).hom = _
  exact congrArg (fun f : Scheme.geometricPointOver K x ⟶ (CommGrp.torsionObject A n).X =>
    f ≫ Grp.kernelInclusion (n • 𝟙 A).hom)
    (Scheme.finiteGroupFiberPointsEquiv_apply K x (CommGrp.torsionObject A n) v.toMul)

end AlgebraicGeometry.GroupScheme
