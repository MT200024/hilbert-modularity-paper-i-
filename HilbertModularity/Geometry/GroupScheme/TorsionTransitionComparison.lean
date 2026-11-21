/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TorsionPoints
public import HilbertModularity.Geometry.GroupScheme.TorsionTower
public import HilbertModularity.Algebra.TateModule

/-! # The torsion-cover tower and the ordinary Tate transition maps -/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory torsionObjectEtale torsionObjectIsFinite

variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S) (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The actual torsion-cover transition becomes multiplication by `p` on native torsion points. -/
theorem finiteTorsionFiberPointsEquiv_transition (n : ℕ)
    (v : Additive ((Scheme.finiteGroupFiberFunctor K x).obj
      (finiteEtaleTorsionObject A (p ^ (n + 1))))) :
    finiteTorsionFiberPointsEquiv K x A (p ^ n)
        (Additive.ofMul ((Scheme.finiteGroupFiberFunctor K x).map
          (finiteEtaleTorsionTransition A p n) v.toMul)) =
      TateModule.transition p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n
        (finiteTorsionFiberPointsEquiv K x A (p ^ (n + 1)) v) := by
  apply Subtype.ext
  change (finiteTorsionFiberPointsEquiv K x A (p ^ n)
      (Additive.ofMul ((Scheme.finiteGroupFiberFunctor K x).map
        (finiteEtaleTorsionTransition A p n) v.toMul))).val.toMul =
    (finiteTorsionFiberPointsEquiv K x A (p ^ (n + 1)) v).val.toMul ^ p
  rw [finiteTorsionFiberPointsEquiv_apply, finiteTorsionFiberPointsEquiv_apply]
  have h := Scheme.finiteGroupFiberPointsEquiv_natural K x
    (CommGrp.torsionObject A (p ^ (n + 1))) (CommGrp.torsionTransition A p n) v.toMul
  simp only [Scheme.finiteGroupFiberPointsEquiv_apply] at h
  change (Scheme.finiteGroupFiberFunctor K x).map (finiteEtaleTorsionTransition A p n) v.toMul =
    v.toMul ≫ (CommGrp.torsionTransition A p n).hom.hom.hom at h
  erw [h]
  exact CommGrp.torsionTransition_points A p n (Scheme.geometricPointOver K x) v.toMul

end AlgebraicGeometry.GroupScheme
