/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Continuity
public import Mathlib.CategoryTheory.Core
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RepresentationTheory.Basic

/-! # Paths between actual étale fibre functors

Objects are rational points of the scheme, equipped with their geometric
fibre functors. A path is an actual natural isomorphism of these functors.
The induced category in the core is a groupoid, without assuming existence
of a path between distinct points.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u
variable (K : Type u) [Field K] (S : Scheme.{u})

/-- The actual étale fibre groupoid on geometric points above rational points. -/
def EtaleFiberGroupoid :=
  InducedCategory (Core (S.FiniteEtale ⥤ FintypeCat.{u}))
    (fun x : Spec (CommRingCat.of K) ⟶ S => Core.mk (finiteArithmeticFiberFunctor K x))

instance : Groupoid (EtaleFiberGroupoid K S) := inferInstanceAs
  (Groupoid (InducedCategory (Core (S.FiniteEtale ⥤ FintypeCat.{u}))
    (fun x : Spec (CommRingCat.of K) ⟶ S => Core.mk (finiteArithmeticFiberFunctor K x))))

/-- A rational point determines its actual geometric fibre functor object. -/
abbrev etaleFiberPoint (x : Spec (CommRingCat.of K) ⟶ S) : EtaleFiberGroupoid K S := x

/-- A natural isomorphism of fibres is an actual path in the fibre groupoid. -/
def etaleFiberPath {x y : Spec (CommRingCat.of K) ⟶ S}
    (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K y) :
    etaleFiberPoint K S x ⟶ etaleFiberPoint K S y :=
  InducedCategory.homMk (CoreHom.mk e)

/-- The underlying natural isomorphism of an actual étale path. -/
def etaleFiberPathIso {x y : Spec (CommRingCat.of K) ⟶ S}
    (e : etaleFiberPoint K S x ⟶ etaleFiberPoint K S y) :
    finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K y := e.hom.iso

/-- Arithmetic automorphisms give loops in the actual fibre groupoid. -/
def arithmeticFiberLoop (x : Spec (CommRingCat.of K) ⟶ S)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    etaleFiberPoint K S x ⟶ etaleFiberPoint K S x :=
  etaleFiberPath K S (galoisToEtaleFundamentalGroup K x g)

variable {R : Type*} [CommRing R]

/-- A module-valued functor on the actual fibre groupoid gives its monodromy representation. -/
def fiberMonodromy (L : EtaleFiberGroupoid K S ⥤ ModuleCat R)
    (x : Spec (CommRingCat.of K) ⟶ S) :
    Representation R (etaleFundamentalGroup K x) (L.obj (etaleFiberPoint K S x)) where
  toFun σ := (L.map (etaleFiberPath K S σ)).hom
  map_one' := by
    change (L.map (𝟙 (etaleFiberPoint K S x))).hom = _
    rw [L.map_id]
    rfl
  map_mul' σ τ := by
    change (L.map (etaleFiberPath K S τ ≫ etaleFiberPath K S σ)).hom = _
    rw [L.map_comp]
    rfl

/-- Pullback along a rational point is the action induced by its actual arithmetic loops.
All fibres use the same module-valued functor. -/
def arithmeticFiberRepresentation (L : EtaleFiberGroupoid K S ⥤ ModuleCat R)
    (x : Spec (CommRingCat.of K) ⟶ S) :
    Representation R (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (L.obj (etaleFiberPoint K S x)) :=
  (fiberMonodromy K S L x).comp (galoisToEtaleFundamentalGroup K x)

/-- Continuous monodromy gives a continuous specialized arithmetic action. -/
theorem continuous_arithmeticFiberRepresentation
    (L : EtaleFiberGroupoid K S ⥤ ModuleCat R)
    (x : Spec (CommRingCat.of K) ⟶ S)
    [TopologicalSpace (L.obj (etaleFiberPoint K S x))]
    (hL : ∀ v, Continuous (fun σ => fiberMonodromy K S L x σ v))
    (v : L.obj (etaleFiberPoint K S x)) :
    Continuous (fun g => arithmeticFiberRepresentation K S L x g v) :=
  (hL v).comp (continuous_galoisToEtaleFundamentalGroup K x)

end AlgebraicGeometry.Scheme
