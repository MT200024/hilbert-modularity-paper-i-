/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem
public import HilbertModularity.Geometry.Etale.FiberDuality
public import HilbertModularity.RepresentationTheory.DualContinuity

/-! # Cohomological duals of continuous étale fibre families

The algebraic contragredient family carries its canonical finite-dimensional
module topology. Its monodromy remains continuous, as required by the
cohomological factor convention in [TripathiGoswami].
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.Scheme.EtaleLocalSystem
open CategoryTheory
universe u v w
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {R : Type v} [NontriviallyNormedField R]
  (V : EtaleLocalSystem.{u, v, w} K X R)

/-- The dual fibre family with the canonical module topology on its linear duals. -/
def cohDualFunctor : EtaleFiberGroupoid K X ⥤ TopModuleCat R :=
  ModuleCat.cohDual R V.algebraicFunctor ⋙ TopModuleCat.withModuleTopology R

/-- Every fibre of the dual family is finite dimensional. -/
instance cohDualFunctor_finite (x : EtaleFiberGroupoid K X) :
    Module.Finite R (V.cohDualFunctor.obj x) := by
  have : Module.Finite R (V.toFunctor.obj x) := V.finite x
  change Module.Finite R (Module.Dual R (V.toFunctor.obj x))
  infer_instance

variable [CompleteSpace R]

/-- Actual profinite monodromy remains continuous after taking the cohomological dual. -/
theorem continuous_cohDualFunctor_loop (x : Spec (CommRingCat.of K) ⟶ X)
    (φ : V.cohDualFunctor.obj (etaleFiberPoint K X x)) :
    Continuous (fun g : etaleFundamentalGroup K x =>
      (V.cohDualFunctor.map (etaleFiberPath K X g)).hom φ) := by
  let M := V.toFunctor.obj (etaleFiberPoint K X x)
  have : Module.Finite R M := V.finite _
  have : T2Space M := V.hausdorff _
  have : IsModuleTopology R M := isModuleTopologyOfFiniteDimensional (𝕜 := R) (E := M)
  let : TopologicalSpace (Module.Dual R M) := moduleTopology R (Module.Dual R M)
  have : IsModuleTopology R (Module.Dual R M) := ⟨rfl⟩
  let ρ : Representation R (etaleFundamentalGroup K x) M :=
    fiberMonodromy K X V.algebraicFunctor x
  have hρ (v : M) : Continuous (fun g => ρ g v) := V.continuous_monodromy x v
  have h := Representation.continuous_dual_orbit ρ hρ φ
  let : TopologicalSpace ((ModuleCat.cohDual R V.algebraicFunctor).obj
      (etaleFiberPoint K X x)) := moduleTopology R _
  have he := fiberMonodromy_cohDual K X V.algebraicFunctor x
  change Continuous (fun g => fiberMonodromy K X (ModuleCat.cohDual R V.algebraicFunctor) x g φ)
  rw [he]
  exact h

/-- The continuous cohomological dual of one finite-dimensional étale fibre family. -/
def cohDual : EtaleLocalSystem K X R where
  toFunctor := V.cohDualFunctor
  finite x := V.cohDualFunctor_finite x
  hausdorff x := by
    let M := V.cohDualFunctor.obj x
    have : Module.Finite R M := V.cohDualFunctor_finite x
    have : IsModuleTopology R M := ⟨rfl⟩
    let e := (Module.finBasis R M).equivFun
    let eR : M ≃L[R] (Fin (Module.finrank R M) → R) :=
      { e with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
    exact eR.toHomeomorph.symm.t2Space
  continuous_monodromy x φ := V.continuous_cohDualFunctor_loop x φ

/-- Forgetting the topology of the dual retains exactly the algebraic dual family. -/
theorem cohDual_algebraicFunctor :
    V.cohDual.algebraicFunctor = ModuleCat.cohDual R V.algebraicFunctor := rfl

/-- Arithmetic specialization of a continuous dual family is the dual arithmetic representation. -/
theorem cohDual_arithmeticRepresentation (x : Spec (CommRingCat.of K) ⟶ X) :
    V.cohDual.arithmeticRepresentation x = (V.arithmeticRepresentation x).dual :=
  arithmeticFiberRepresentation_cohDual K X V.algebraicFunctor x

end AlgebraicGeometry.Scheme.EtaleLocalSystem
