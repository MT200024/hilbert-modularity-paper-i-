/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Continuous coordinates for actual local-system fibres

Finite-dimensional Hausdorff fibres over a complete normed field have their
unique module topology. Coordinates therefore realize their existing monodromy
on a normed vector space, without a separate continuity hypothesis.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleLocalSystem

universe u v w
variable {K : Type u} [Field K] {S : Scheme.{u}}
  {L : Type v} [NontriviallyNormedField L] [CompleteSpace L]
  (F : EtaleLocalSystem.{u, v, w} K S L)
  (x : Spec (CommRingCat.of K) ⟶ S)

/-- Continuous coordinates on the actual fibre, with its original topology. -/
def fiberCoordinateEquiv :
    F.toFunctor.obj (etaleFiberPoint K S x) ≃L[L]
      (Fin (Module.finrank L (F.toFunctor.obj (etaleFiberPoint K S x))) → L) := by
  let M := F.toFunctor.obj (etaleFiberPoint K S x)
  haveI : Module.Finite L M := F.finite _
  haveI : T2Space M := F.hausdorff _
  haveI : IsModuleTopology L M := isModuleTopologyOfFiniteDimensional (𝕜 := L) (E := M)
  let e := (Module.finBasis L M).equivFun
  exact { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

/-- The actual fibre monodromy expressed in finite normed coordinates. -/
def coordinateMonodromy :
    Representation L (etaleFundamentalGroup K x)
      (Fin (Module.finrank L (F.toFunctor.obj (etaleFiberPoint K S x))) → L) :=
  (F.fiberCoordinateEquiv x).toLinearEquiv.conjRingEquiv.toMonoidHom.comp
    (fiberMonodromy K S F.algebraicFunctor x)

/-- Coordinates intertwine the native and coordinate monodromy actions. -/
def coordinateMonodromyEquiv :
    (fiberMonodromy K S F.algebraicFunctor x).Equiv (F.coordinateMonodromy x) :=
  .mk (F.fiberCoordinateEquiv x).toLinearEquiv (by
    intro g
    apply LinearMap.ext
    intro v
    change F.fiberCoordinateEquiv x (fiberMonodromy K S F.algebraicFunctor x g v) =
      F.fiberCoordinateEquiv x (fiberMonodromy K S F.algebraicFunctor x g
        ((F.fiberCoordinateEquiv x).symm (F.fiberCoordinateEquiv x v)))
    exact congrArg (fun z => F.fiberCoordinateEquiv x
      (fiberMonodromy K S F.algebraicFunctor x g z))
        ((F.fiberCoordinateEquiv x).symm_apply_apply v).symm)

/-- Continuity in coordinates follows from the original local system. -/
theorem continuous_coordinateMonodromy
    (v : Fin (Module.finrank L (F.toFunctor.obj (etaleFiberPoint K S x))) → L) :
    Continuous (fun g => F.coordinateMonodromy x g v) :=
  (F.fiberCoordinateEquiv x).continuous.comp
    (F.continuous_monodromy x ((F.fiberCoordinateEquiv x).symm v))

/-- The arithmetic specialization in the same continuous fibre coordinates. -/
def coordinateArithmeticRepresentation :
    Representation L (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (Fin (Module.finrank L (F.toFunctor.obj (etaleFiberPoint K S x))) → L) :=
  (F.fiberCoordinateEquiv x).toLinearEquiv.conjRingEquiv.toMonoidHom.comp
    (F.arithmeticRepresentation x)

/-- The coordinate action is equivariantly the original arithmetic fibre. -/
def coordinateArithmeticEquiv :
    (F.arithmeticRepresentation x).Equiv (F.coordinateArithmeticRepresentation x) :=
  .mk (F.fiberCoordinateEquiv x).toLinearEquiv (by
    intro g
    apply LinearMap.ext
    intro v
    change F.fiberCoordinateEquiv x (F.arithmeticRepresentation x g v) =
      F.fiberCoordinateEquiv x (F.arithmeticRepresentation x g
        ((F.fiberCoordinateEquiv x).symm (F.fiberCoordinateEquiv x v)))
    rw [ContinuousLinearEquiv.symm_apply_apply])

/-- Arithmetic orbit maps remain continuous in the finite coordinates. -/
theorem continuous_coordinateArithmeticRepresentation
    (v : Fin (Module.finrank L (F.toFunctor.obj (etaleFiberPoint K S x))) → L) :
    Continuous (fun g => F.coordinateArithmeticRepresentation x g v) :=
  (F.fiberCoordinateEquiv x).continuous.comp
    (F.continuous_arithmeticRepresentation x ((F.fiberCoordinateEquiv x).symm v))

/-- Every matrix entry of the arithmetic action is continuous. -/
theorem continuous_coordinateArithmeticRepresentation_entry
    (i j : Fin (Module.finrank L (F.toFunctor.obj (etaleFiberPoint K S x)))) :
    Continuous (fun g => F.coordinateArithmeticRepresentation x g (Pi.single j 1) i) :=
  (continuous_apply i).comp
    (F.continuous_coordinateArithmeticRepresentation x (Pi.single j 1))

/-- Coordinates with a prescribed rank, using the proved dimension equality. -/
def arithmeticRepresentationOfFinrankEq (n : ℕ)
    (h : Module.finrank L (F.toFunctor.obj (etaleFiberPoint K S x)) = n) :
    Representation L (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (Fin n → L) :=
  h ▸ F.coordinateArithmeticRepresentation x

/-- Prescribing the rank changes only coordinates, not the arithmetic action. -/
def arithmeticEquivOfFinrankEq (n : ℕ)
    (h : Module.finrank L (F.toFunctor.obj (etaleFiberPoint K S x)) = n) :
    (F.arithmeticRepresentation x).Equiv (F.arithmeticRepresentationOfFinrankEq x n h) := by
  subst n
  exact F.coordinateArithmeticEquiv x

/-- The prescribed-rank action has continuous matrix entries. -/
theorem continuous_arithmeticRepresentationOfFinrankEq_entry (n : ℕ)
    (h : Module.finrank L (F.toFunctor.obj (etaleFiberPoint K S x)) = n)
    (i j : Fin n) :
    Continuous (fun g => F.arithmeticRepresentationOfFinrankEq x n h g (Pi.single j 1) i) := by
  subst n
  exact F.continuous_coordinateArithmeticRepresentation_entry x i j

end AlgebraicGeometry.Scheme.EtaleLocalSystem
