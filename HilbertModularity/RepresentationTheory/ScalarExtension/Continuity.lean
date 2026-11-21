/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Algebra

/-! # Continuous orbits after extending representation coefficients -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation
universe u v w z
variable {R : Type u} [CommRing R] [TopologicalSpace R]
  (S : Type v) [CommRing S] [TopologicalSpace S] [Algebra R S] [ContinuousSMul R S]
  {G : Type w} [Monoid G] [TopologicalSpace G]
  {V : Type z} [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsModuleTopology R V]
  [TopologicalSpace (S ⊗[R] V)] [IsModuleTopology S (S ⊗[R] V)]

/-- Scalar extension preserves continuous representation orbits for the module topologies. -/
theorem continuous_baseChange_orbit (ρ : Representation R G V)
    (hρ : ∀ v : V, Continuous (fun g => ρ g v)) (v : S ⊗[R] V) :
    Continuous (fun g => ρ.baseChange S g v) := by
  let : ContinuousAdd (S ⊗[R] V) := IsModuleTopology.toContinuousAdd S _
  let : ContinuousSMul R (S ⊗[R] V) := ⟨by
    have h := ((continuous_algebraMap R S).comp
      (continuous_fst : Continuous (fun z : R × (S ⊗[R] V) => z.1))).smul continuous_snd
    change Continuous (fun z : R × (S ⊗[R] V) => algebraMap R S z.1 • z.2) at h
    apply h.congr
    intro z
    exact IsScalarTower.algebraMap_smul S z.1 z.2⟩
  induction v using TensorProduct.inductionOn with
  | add x y hx hy =>
    apply (hx.add hy).congr
    intro g
    exact (map_add (ρ.baseChange S g) x y).symm
  | tmul a x =>
    exact (IsModuleTopology.continuous_of_linearMap (TensorProduct.mk R S V a)).comp (hρ x)

end Representation
