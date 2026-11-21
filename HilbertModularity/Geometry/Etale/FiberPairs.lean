/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteProducts

/-! # Pairs of points in actual finite étale fibres -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
universe u
variable {S : Scheme.{u}} (K : Type u) [Field K]
  (x : Spec (CommRingCat.of K) ⟶ S) {X Y : S.FiniteEtale}

set_option backward.isDefEq.respectTransparency false in
/-- Pair two geometric fibre points using the actual scheme fibre product. -/
def finiteArithmeticFiberPair
    (a : (finiteArithmeticFiberFunctor K x).obj X)
    (b : (finiteArithmeticFiberFunctor K x).obj Y) :
    (finiteArithmeticFiberFunctor K x).obj (finiteEtaleProduct X Y) :=
  Over.homMk (pullback.lift a.left b.left (a.w.trans b.w.symm)) (by
    change pullback.lift a.left b.left _ ≫
      (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom) = (geometricPointOver K x).hom
    rw [← Category.assoc, pullback.lift_fst]
    exact a.w)

set_option backward.isDefEq.respectTransparency false in
/-- The first projection recovers the first geometric fibre point. -/
@[simp] theorem finiteArithmeticFiberPair_fst
    (a : (finiteArithmeticFiberFunctor K x).obj X)
    (b : (finiteArithmeticFiberFunctor K x).obj Y) :
    (finiteArithmeticFiberFunctor K x).map (finiteEtaleProductFst X Y)
      (finiteArithmeticFiberPair K x a b) = a := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The second projection recovers the second geometric fibre point. -/
@[simp] theorem finiteArithmeticFiberPair_snd
    (a : (finiteArithmeticFiberFunctor K x).obj X)
    (b : (finiteArithmeticFiberFunctor K x).obj Y) :
    (finiteArithmeticFiberFunctor K x).map (finiteEtaleProductSnd X Y)
      (finiteArithmeticFiberPair K x a b) = b := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme
