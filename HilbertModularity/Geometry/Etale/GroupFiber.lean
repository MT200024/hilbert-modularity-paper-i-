/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteProducts
public import HilbertModularity.Geometry.Etale.FiberGroupoid
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
public import Mathlib.CategoryTheory.Whiskering

/-! # Group structures on finite étale geometric fibres

Finite products are actual scheme fibre products. Consequently the geometric
fibre functor takes a commutative group object in finite étale covers to a
finite commutative group. Actual étale paths act by group isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory

local instance finiteEtaleBraidedCategory (S : Scheme.{u}) : BraidedCategory S.FiniteEtale :=
  .ofCartesianMonoidalCategory

variable (K : Type u) [Field K] {S : Scheme.{u}}

/-- The actual geometric fibre functor on finite étale covers, valued in types. -/
def finiteGeometricFiberFunctor (x : Spec (CommRingCat.of K) ⟶ S) :
    S.FiniteEtale ⥤ Type u :=
  finiteArithmeticFiberFunctor K x ⋙ CategoryTheory.forget FintypeCat

instance finiteGeometricFiberFunctor_preservesFiniteProducts
    (x : Spec (CommRingCat.of K) ⟶ S) :
    PreservesFiniteProducts (finiteGeometricFiberFunctor K x) :=
  inferInstanceAs (PreservesFiniteProducts
    (finiteArithmeticFiberFunctor K x ⋙ CategoryTheory.forget FintypeCat))

/-- The product comparison is the canonical braided structure on geometric fibres. -/
instance finiteGeometricFiberFunctor_braided (x : Spec (CommRingCat.of K) ⟶ S) :
    (finiteGeometricFiberFunctor K x).Braided :=
  Functor.Braided.ofChosenFiniteProducts _

/-- A finite étale commutative group object has its actual geometric group of points. -/
def finiteGroupFiberFunctor (x : Spec (CommRingCat.of K) ⟶ S) :
    CommGrp S.FiniteEtale ⥤ CommGrpCat :=
  (finiteGeometricFiberFunctor K x).mapCommGrp ⋙ commGrpTypeEquivalenceCommGrp.functor

/-- The group fibre has precisely the underlying geometric points of the finite cover. -/
def finiteGroupFiberEquiv (x : Spec (CommRingCat.of K) ⟶ S)
    (A : CommGrp S.FiniteEtale) :
    (finiteGroupFiberFunctor K x).obj A ≃ (finiteArithmeticFiberFunctor K x).obj A.X :=
  Equiv.refl _

instance finiteGroupFiber_finite (x : Spec (CommRingCat.of K) ⟶ S)
    (A : CommGrp S.FiniteEtale) : Finite ((finiteGroupFiberFunctor K x).obj A) :=
  Finite.of_equiv _ (finiteGroupFiberEquiv K x A).symm

/-- An actual étale path transports the group law, not only the underlying finite set. -/
def finiteGroupFiberPathIso {x y : Spec (CommRingCat.of K) ⟶ S}
    (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K y) :
    finiteGroupFiberFunctor K x ≅ finiteGroupFiberFunctor K y :=
  Functor.isoWhiskerRight
    (Functor.mapCommGrpNatIso (show finiteGeometricFiberFunctor K x ≅
      finiteGeometricFiberFunctor K y from
        Functor.isoWhiskerRight e (CategoryTheory.forget FintypeCat)))
    commGrpTypeEquivalenceCommGrp.functor

/-- Group transport evaluates to the original natural isomorphism on the actual cover. -/
@[simp]
theorem finiteGroupFiberPathIso_apply {x y : Spec (CommRingCat.of K) ⟶ S}
    (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K y)
    (A : CommGrp S.FiniteEtale) (v : (finiteGroupFiberFunctor K x).obj A) :
    (finiteGroupFiberPathIso K e).hom.app A v = e.hom.app A.X v := rfl

/-- One finite étale group object supplies compatible group fibres on the actual fibre groupoid. -/
def finiteGroupFiberLocalSystem (A : CommGrp S.FiniteEtale) :
    EtaleFiberGroupoid K S ⥤ CommGrpCat where
  obj x := (finiteGroupFiberFunctor K x).obj A
  map e := (finiteGroupFiberPathIso K e.hom.iso).hom.app A
  map_id x := by
    ext v
    rfl
  map_comp e f := by
    ext v
    rfl

/-- At an arithmetic loop the group-fibre action is the original Galois action on points. -/
@[simp]
theorem finiteGroupFiberLocalSystem_arithmetic (A : CommGrp S.FiniteEtale)
    (x : Spec (CommRingCat.of K) ⟶ S)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : (finiteGroupFiberFunctor K x).obj A) :
    (finiteGroupFiberLocalSystem K A).map (arithmeticFiberLoop K S x g) v =
      arithmeticFiberPointMap K x g ≫ v := rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory finiteEtaleBraidedCategory
variable (K : Type u) [Field K] (S : Scheme.{u})

/-- Actual group-fibre local systems are functorial in the finite étale group object. -/
def finiteGroupFiberLocalSystemFunctor :
    CommGrp S.FiniteEtale ⥤ (EtaleFiberGroupoid K S ⥤ CommGrpCat) where
  obj A := finiteGroupFiberLocalSystem K A
  map f := {
    app x := (finiteGroupFiberFunctor K x).map f
    naturality {x y} e := ((finiteGroupFiberPathIso K e.hom.iso).hom.naturality f).symm }
  map_id A := by
    apply NatTrans.ext
    funext x
    exact (finiteGroupFiberFunctor K x).map_id A
  map_comp f g := by
    apply NatTrans.ext
    funext x
    exact (finiteGroupFiberFunctor K x).map_comp f g

end AlgebraicGeometry.Scheme
