/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.Category.ModuleCat.DualScalarExtension
public import HilbertModularity.Geometry.Etale.LocalSystem.Duality
public import HilbertModularity.Geometry.Etale.LocalSystem.ScalarExtension

/-! # Extending coefficients of a continuous cohomological family

The natural dual base-change comparison respects the canonical module
topologies and therefore all actual arithmetic fibres. It retains the one
chosen family when enlarging its local coefficient field as in
[TripathiGoswami, cohomological RM factor].
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.Scheme.EtaleLocalSystem
open CategoryTheory
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {R : Type v} [NontriviallyNormedField R] [CompleteSpace R]
  (V : EtaleLocalSystem.{u, v, v} K X R)
  (L : Type v) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra R L] [ContinuousSMul R L]

/-- Continuous cohomological duality commutes with extending the local coefficient field. -/
def cohDualExtendScalarsIso :
    (V.cohDual.extendScalars L).toFunctor ≅ (V.extendScalars L).cohDual.toFunctor := by
  letI : ∀ x, Module.Finite R (V.algebraicFunctor.obj x) := fun x => V.finite x
  change (ModuleCat.cohDual R V.algebraicFunctor ⋙ ModuleCat.extendScalars (algebraMap R L)) ⋙
      TopModuleCat.withModuleTopology L ≅
    ModuleCat.cohDual L (V.algebraicFunctor ⋙ ModuleCat.extendScalars (algebraMap R L)) ⋙
      TopModuleCat.withModuleTopology L
  exact Functor.isoWhiskerRight (ModuleCat.cohDualScalarExtensionIso R L V.algebraicFunctor)
    (TopModuleCat.withModuleTopology L)

/-- The coefficient-extension comparison is equivariant on every actual arithmetic fibre. -/
def cohDualExtendScalarsArithmeticEquiv (x : Spec (CommRingCat.of K) ⟶ X) :
    Representation.Equiv ((V.cohDual.extendScalars L).arithmeticRepresentation x)
      ((V.extendScalars L).cohDual.arithmeticRepresentation x) :=
  arithmeticFiberEquiv K X
    (Functor.isoWhiskerRight (V.cohDualExtendScalarsIso L) (forget₂ (TopModuleCat L) (ModuleCat L))) x

end AlgebraicGeometry.Scheme.EtaleLocalSystem
