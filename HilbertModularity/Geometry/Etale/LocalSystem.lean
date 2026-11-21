/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiberNaturality
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-! # Continuous finite-dimensional étale fibre families

We use finite-dimensional Hausdorff topological modules and continuous
monodromy on the actual groupoid of geometric fibre functors above rational
points. This records a single family and its arithmetic specializations.
The comparison with étale sheaves and the construction of a particular
hypergeometric realization are separate mathematical statements.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u v w

variable (K : Type u) [Field K] (S : Scheme.{u})
  (R : Type v) [Field R] [TopologicalSpace R]

/-- A continuous finite-dimensional family on the actual étale fibre groupoid.
Its data are one functor, with the usual finiteness, separation and continuity conditions. -/
structure EtaleLocalSystem where
  /-- The single module-valued family, including transport along actual paths. -/
  toFunctor : EtaleFiberGroupoid K S ⥤ TopModuleCat.{w} R
  /-- Every fibre is finite-dimensional over the coefficient field. -/
  finite : ∀ x, Module.Finite R (toFunctor.obj x)
  /-- Each fibre has a Hausdorff module topology. -/
  hausdorff : ∀ x, T2Space (toFunctor.obj x)
  /-- Monodromy orbit maps are continuous for the actual profinite fundamental group. -/
  continuous_monodromy : ∀ (x : Spec (CommRingCat.of K) ⟶ S)
    (v : toFunctor.obj (etaleFiberPoint K S x)),
    Continuous (fun σ : etaleFundamentalGroup K x =>
      (toFunctor.map (etaleFiberPath K S σ)).hom v)

namespace EtaleLocalSystem

variable {K S R} (L : EtaleLocalSystem K S R)

/-- The underlying module-valued family forgets only the topology. -/
def algebraicFunctor : EtaleFiberGroupoid K S ⥤ ModuleCat R :=
  L.toFunctor ⋙ forget₂ (TopModuleCat R) (ModuleCat R)

/-- Arithmetic specialization of the one continuous family at a rational point. -/
def arithmeticRepresentation (x : Spec (CommRingCat.of K) ⟶ S) :
    Representation R (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (L.toFunctor.obj (etaleFiberPoint K S x)) :=
  arithmeticFiberRepresentation K S L.algebraicFunctor x

/-- The specialized fibre is genuinely finite-dimensional. -/
instance arithmeticFiber_finite (x : Spec (CommRingCat.of K) ⟶ S) :
    Module.Finite R (L.toFunctor.obj (etaleFiberPoint K S x)) := L.finite _

/-- The specialized fibre retains its Hausdorff topology. -/
instance arithmeticFiber_t2 (x : Spec (CommRingCat.of K) ⟶ S) :
    T2Space (L.toFunctor.obj (etaleFiberPoint K S x)) := L.hausdorff _

/-- Pullback to a rational point gives a continuous arithmetic representation. -/
theorem continuous_arithmeticRepresentation (x : Spec (CommRingCat.of K) ⟶ S)
    (v : L.toFunctor.obj (etaleFiberPoint K S x)) :
    Continuous (fun g => L.arithmeticRepresentation x g v) :=
  (L.continuous_monodromy x v).comp (continuous_galoisToEtaleFundamentalGroup K x)

end EtaleLocalSystem
end AlgebraicGeometry.Scheme
