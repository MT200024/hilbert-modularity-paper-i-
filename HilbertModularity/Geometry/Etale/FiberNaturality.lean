/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiberGroupoid
public import Mathlib.RepresentationTheory.Intertwining

/-! # Naturality of arithmetic fibre representations

A morphism of module-valued functors induces equivariant maps at every rational
point. One isomorphism of such functors therefore compares all specialized
arithmetic representations simultaneously.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u
variable (K : Type u) [Field K] (S : Scheme.{u})
  {R : Type*} [CommRing R]
  {L M : EtaleFiberGroupoid K S ⥤ ModuleCat R}

/-- A natural transformation induces an intertwiner for the actual monodromy action. -/
def fiberMonodromyIntertwiner (η : L ⟶ M) (x : Spec (CommRingCat.of K) ⟶ S) :
    (fiberMonodromy K S L x).IntertwiningMap (fiberMonodromy K S M x) where
  toLinearMap := (η.app (etaleFiberPoint K S x)).hom
  isIntertwining' σ := congrArg ModuleCat.Hom.hom (η.naturality (etaleFiberPath K S σ))

/-- Specializing a natural transformation gives an actual arithmetic intertwiner. -/
def arithmeticFiberIntertwiner (η : L ⟶ M) (x : Spec (CommRingCat.of K) ⟶ S) :
    (arithmeticFiberRepresentation K S L x).IntertwiningMap
      (arithmeticFiberRepresentation K S M x) where
  toLinearMap := (η.app (etaleFiberPoint K S x)).hom
  isIntertwining' g :=
    (fiberMonodromyIntertwiner K S η x).isIntertwining' (galoisToEtaleFundamentalGroup K x g)

/-- One isomorphism of the module-valued families compares every specialized arithmetic representation. -/
def arithmeticFiberEquiv (e : L ≅ M) (x : Spec (CommRingCat.of K) ⟶ S) :
    (arithmeticFiberRepresentation K S L x).Equiv (arithmeticFiberRepresentation K S M x) :=
  .mk (e.app (etaleFiberPoint K S x)).toLinearEquiv
    (arithmeticFiberIntertwiner K S e.hom x).isIntertwining'

end AlgebraicGeometry.Scheme
