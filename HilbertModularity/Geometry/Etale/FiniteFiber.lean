/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.ArithmeticFiber
public import HilbertModularity.Geometry.Etale.GeometricFiber
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-! # Finite étale fibres and their profinite automorphism group

The geometric fibre functor on actual finite étale covers takes values in
finite sets. Its natural automorphisms form the usual étale fundamental group,
with the standard profinite topology from mathlib. A rational point gives an
algebraic homomorphism from the absolute Galois group into this group.
Continuity and the geometric fundamental-group exact sequence are separate results.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual finite étale cover has a finite fibre at the chosen geometric point. -/
instance finite_arithmeticFiber (X : S.FiniteEtale) :
    Finite ((arithmeticFiberFunctor K x).obj X.obj) := by
  change Finite (Over.mk (geometricPointOver K x).hom ⟶ Over.mk X.obj.hom)
  exact RationalPoint.finite_geometricFiber (AlgebraicClosure K) X.obj.hom
    (geometricPointOver K x).hom

/-- The actual finite-set-valued geometric fibre functor on finite étale covers. -/
def finiteArithmeticFiberFunctor : S.FiniteEtale ⥤ FintypeCat.{u} :=
  finiteEtaleFiberFunctor (AlgebraicClosure K) (geometricPointOver K x).hom

/-- The finite fibres retain their actual arithmetic Galois action. -/
instance finiteArithmeticFiberMulAction (X : S.FiniteEtale) :
    MulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      ((finiteArithmeticFiberFunctor K x).obj X) :=
  inferInstanceAs (MulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    ((arithmeticFiberFunctor K x).obj X.obj))

/-- The arithmetic action is natural on the finite étale category. -/
instance finiteArithmeticFiber_isNaturalSMul :
    PreGaloisCategory.IsNaturalSMul (finiteArithmeticFiberFunctor K x)
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  naturality g {_X _Y} f y := arithmeticFiber_map_smul K x f.hom g y

/-- The étale fundamental group is the actual profinite automorphism group of
this geometric fibre functor on finite étale covers. -/
abbrev etaleFundamentalGroup : ProfiniteGrp :=
  ProfiniteGrp.of (Aut (finiteArithmeticFiberFunctor K x))

/-- The chosen rational point induces the algebraic Galois homomorphism into the
actual profinite fibre-automorphism group. -/
def galoisToEtaleFundamentalGroup :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* etaleFundamentalGroup K x :=
  PreGaloisCategory.toAut (finiteArithmeticFiberFunctor K x)
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)

end AlgebraicGeometry.Scheme
