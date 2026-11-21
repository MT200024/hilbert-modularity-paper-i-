/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.RatFunc.InertiaConjugacy
public import HilbertModularity.RingTheory.Ideal.InertiaTopology

/-! # Closedness of rational-function inertia -/

@[expose] public noncomputable section
namespace RatFunc
variable (K : Type*) [Field K] [CharZero K]

omit [CharZero K] in
/-- Finite-coordinate inertia is closed for the actual Krull topology. -/
theorem isClosed_affineInertia (a : K) : IsClosed (affineInertia K a : Set
    (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))) := by
  let : TopologicalSpace (affineIntegralClosure K) := ⊥
  have : DiscreteTopology (affineIntegralClosure K) := ⟨rfl⟩
  exact (affinePrimeAbove K a).isClosed_inertia

end RatFunc
