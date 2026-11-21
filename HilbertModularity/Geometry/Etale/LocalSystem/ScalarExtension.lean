/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.Category.ModuleCat.ScalarExtensionTopology
public import HilbertModularity.Geometry.Etale.LocalSystem
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Extending the coefficients of a continuous fibre family

Scalar extension preserves finite-dimensional fibres and continuous monodromy.
The coefficient-module topology on every extended fibre is Hausdorff.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleLocalSystem
open CategoryTheory
universe u v w
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {R : Type v} [NontriviallyNormedField R]
  (V : EtaleLocalSystem K X R)
  (L : Type w) [NontriviallyNormedField L] [Algebra R L]

/-- Scalar extension of the one underlying fibre family, with the canonical module topology. -/
def extendScalarsFunctor : EtaleFiberGroupoid K X ⥤ TopModuleCat L :=
  V.algebraicFunctor ⋙ ModuleCat.extendScalars (algebraMap R L) ⋙ TopModuleCat.withModuleTopology L

/-- Extending a finite-dimensional family keeps every fibre finite dimensional. -/
instance extendScalarsFunctor_finite (x : EtaleFiberGroupoid K X) :
    Module.Finite L ((V.extendScalarsFunctor L).obj x) := by
  let M := V.toFunctor.obj x
  have : Module.Finite R M := V.finite x
  exact Module.Finite.equiv (ModuleCat.extendScalarsTensorIso R L (ModuleCat.of R M)).toLinearEquiv.symm

variable [CompleteSpace R] [ContinuousSMul R L]

/-- Continuous monodromy survives scalar extension with its canonical module topology. -/
theorem continuous_extendScalarsFunctor_loop (x : Spec (CommRingCat.of K) ⟶ X)
    (v : (V.extendScalarsFunctor L).obj (etaleFiberPoint K X x)) :
    Continuous (fun g : etaleFundamentalGroup K x =>
      ((V.extendScalarsFunctor L).map (etaleFiberPath K X g)).hom v) := by
  let M := V.toFunctor.obj (etaleFiberPoint K X x)
  have : Module.Finite R M := V.finite _
  have : T2Space M := V.hausdorff _
  have : IsModuleTopology R M := isModuleTopologyOfFiniteDimensional (𝕜 := R) (E := M)
  let Q := (ModuleCat.extendScalars (algebraMap R L)).obj (ModuleCat.of R M)
  let : TopologicalSpace Q := moduleTopology L Q
  have : IsModuleTopology L Q := ⟨rfl⟩
  let ρ : Representation R (etaleFundamentalGroup K x) M :=
    fiberMonodromy K X V.algebraicFunctor x
  have hρ (w : M) : Continuous (fun g => ρ g w) := V.continuous_monodromy x w
  exact ModuleCat.continuous_extendScalars_orbit L ρ hρ v

/-- Extension of coefficients of a continuous finite-dimensional étale fibre family. -/
def extendScalars : EtaleLocalSystem K X L where
  toFunctor := V.extendScalarsFunctor L
  finite x := V.extendScalarsFunctor_finite L x
  hausdorff x := by
    let M := (V.extendScalarsFunctor L).obj x
    have : Module.Finite L M := V.extendScalarsFunctor_finite L x
    have : IsModuleTopology L M := ⟨rfl⟩
    let e := (Module.finBasis L M).equivFun
    let eL : M ≃L[L] (Fin (Module.finrank L M) → L) :=
      { e with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
    exact eL.toHomeomorph.symm.t2Space
  continuous_monodromy x v := V.continuous_extendScalarsFunctor_loop L x v

end AlgebraicGeometry.Scheme.EtaleLocalSystem
