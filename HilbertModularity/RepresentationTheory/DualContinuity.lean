/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Continuous contragredient representations

For a finite-dimensional module with its module topology, continuous orbit
maps give continuous dual orbit maps. Inversion belongs to the group action;
coefficient endomorphisms are merely transposed, following the dual convention
of [TripathiGoswami].
-/

@[expose] public noncomputable section
namespace Representation
variable {R : Type*} [NontriviallyNormedField R]
  {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
  {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
  [TopologicalSpace V] [IsModuleTopology R V]
  [TopologicalSpace (Module.Dual R V)] [IsModuleTopology R (Module.Dual R V)]

/-- Continuous orbits on a finite-dimensional module give continuous contragredient orbits. -/
theorem continuous_dual_orbit (ρ : Representation R G V)
    (hρ : ∀ v : V, Continuous (fun g => ρ g v)) (φ : Module.Dual R V) :
    Continuous (fun g => ρ.dual g φ) := by
  let : ContinuousAdd (Module.Dual R V) := IsModuleTopology.toContinuousAdd R _
  let b := Module.finBasis R V
  let e := b.dualBasis.equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  have hc : Continuous (fun g => e (ρ.dual g φ)) := by
    apply continuous_pi
    intro i
    have h := hφ.comp ((hρ (b i)).comp continuous_inv)
    simpa only [Function.comp_def, e, Module.Basis.dualBasis_equivFun, dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply] using h
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using he.comp hc

end Representation
