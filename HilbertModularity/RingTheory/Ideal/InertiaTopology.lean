/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Order

/-! # Closed inertia subgroups for discrete rings

For a continuous action on a discrete ring, the congruences defining inertia
are closed conditions. No finiteness assumption on the ring is needed.
-/

@[expose] public section
namespace Ideal
variable {G R : Type*} [Group G] [Ring R] [MulSemiringAction G R]
  [TopologicalSpace G] [TopologicalSpace R] [DiscreteTopology R] [ContinuousSMul G R]

/-- Inertia for a continuous action on a discrete ring is a closed subgroup. -/
theorem isClosed_inertia (I : Ideal R) : IsClosed (I.inertia G : Set G) := by
  have h : (I.inertia G : Set G) = ⋂ x : R, (fun g : G => g • x - x) ⁻¹' (I : Set R) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, mem_inertia]
  rw [h]
  apply isClosed_iInter
  intro x
  apply (isClosed_discrete (I : Set R)).preimage
  exact (continuous_of_discreteTopology (f := fun y : R => y - x)).comp
    (continuous_id.smul continuous_const)

end Ideal
