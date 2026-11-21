/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GroupFiber

/-! # Continuous group actions on finite étale group fibres -/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory finiteEtaleBraidedCategory
variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S) (A : CommGrp S.FiniteEtale)

/-- The actual profinite fundamental group acts by group automorphisms on a finite group fibre. -/
instance finiteGroupFiber_mulDistribMulAction :
    MulDistribMulAction (etaleFundamentalGroup K x) ((finiteGroupFiberFunctor K x).obj A) where
  toMulAction := inferInstanceAs (MulAction (Aut (finiteArithmeticFiberFunctor K x))
    ((finiteArithmeticFiberFunctor K x).obj A.X))
  smul_one σ := ((finiteGroupFiberPathIso K σ).hom.app A).hom.map_one
  smul_mul σ v w := ((finiteGroupFiberPathIso K σ).hom.app A).hom.map_mul v w

/-- The topology on the group fibre is the discrete topology on its actual finite set. -/
instance finiteGroupFiber_topologicalSpace :
    TopologicalSpace ((finiteGroupFiberFunctor K x).obj A) :=
  inferInstanceAs (TopologicalSpace ((finiteArithmeticFiberFunctor K x).obj A.X))

instance finiteGroupFiber_discreteTopology :
    DiscreteTopology ((finiteGroupFiberFunctor K x).obj A) := ⟨rfl⟩

/-- Monodromy acts continuously on every actual finite group fibre. -/
instance finiteGroupFiber_continuousSMul :
    ContinuousSMul (etaleFundamentalGroup K x) ((finiteGroupFiberFunctor K x).obj A) :=
  inferInstanceAs (ContinuousSMul (Aut (finiteArithmeticFiberFunctor K x))
    ((finiteArithmeticFiberFunctor K x).obj A.X))

/-- Arithmetic specialization is restriction along the actual rational-point Galois map. -/
@[simp]
theorem finiteGroupFiber_arithmetic_smul
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : (finiteGroupFiberFunctor K x).obj A) :
    galoisToEtaleFundamentalGroup K x g • v =
      arithmeticFiberPointMap K x g ≫ v := rfl

end AlgebraicGeometry.Scheme
