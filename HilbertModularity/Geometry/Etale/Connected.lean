/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteFiber
public import HilbertModularity.Geometry.FinitePointLifting
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Connected.Clopen

/-! # Nonempty finite étale fibres over a connected base

Finite étale images are open and closed. A nonempty cover of a preconnected
base is therefore surjective, so every geometric point has a lift.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry
universe u

/-- A nonempty finite étale cover reaches every point of a preconnected base. -/
theorem Scheme.Hom.surjective_of_finite_etale {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Etale f] [Nonempty X] [PreconnectedSpace Y] :
    Surjective f := by
  have h : IsClopen (Set.range f) := ⟨by
    simpa only [Set.image_univ] using f.isClosedMap Set.univ isClosed_univ, by
    simpa only [Set.image_univ] using f.isOpenMap Set.univ isOpen_univ⟩
  exact ⟨Set.range_eq_univ.mp (h.eq_univ (Set.range_nonempty f))⟩

namespace Scheme
variable (K : Type u) [Field K] {S : Scheme.{u}} [PreconnectedSpace S]
  (x : Spec (CommRingCat.of K) ⟶ S) (X : S.FiniteEtale)

/-- Every nonempty finite étale cover has a point above each chosen geometric point. -/
theorem finiteArithmeticFiber_nonempty [Nonempty X.obj.left] :
    Nonempty ((finiteArithmeticFiberFunctor K x).obj X) := by
  have : Surjective X.obj.hom :=
    Scheme.Hom.surjective_of_finite_etale (X := X.obj.left) (Y := S) X.obj.hom
  change Nonempty (Over.mk (geometricPointOver K x).hom ⟶ Over.mk X.obj.hom)
  exact RationalPoint.nonempty_geometricFiber (AlgebraicClosure K)
    X.obj.hom (geometricPointOver K x).hom

/-- At any geometric base point, nonemptiness of the finite fibre detects
nonemptiness of the actual finite étale cover. -/
theorem finiteArithmeticFiber_nonempty_iff :
    Nonempty ((finiteArithmeticFiberFunctor K x).obj X) ↔ Nonempty X.obj.left := by
  constructor
  · rintro ⟨y⟩
    change Over.mk (geometricPointOver K x).hom ⟶ Over.mk X.obj.hom at y
    exact ⟨y.left (IsLocalRing.closedPoint (AlgebraicClosure K))⟩
  · intro h
    have := h
    exact finiteArithmeticFiber_nonempty K x X

end Scheme
end AlgebraicGeometry
