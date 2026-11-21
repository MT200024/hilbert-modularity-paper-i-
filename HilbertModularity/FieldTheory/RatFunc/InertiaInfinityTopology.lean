/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.RatFunc.InertiaInfinity
public import HilbertModularity.FieldTheory.RatFunc.InertiaTopology
public import HilbertModularity.Geometry.Etale.ArithmeticFieldTopology

/-! # Closed inertia at infinity -/

@[expose] public noncomputable section
namespace RatFunc
variable (K : Type*) [Field K] [CharZero K]

/-- Inertia at infinity is closed for the actual Krull topology. -/
theorem isClosed_infinityInertia : IsClosed (infinityInertia K : Set
    (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))) := by
  rw [infinityInertia, Subgroup.coe_map]
  exact ((isClosed_affineInertia K 0).isCompact.image
    (AlgebraicClosure.continuous_galoisFieldEquiv (RatFunc K) (RatFunc K)
      (reciprocalAlgEquiv K).toRingEquiv)).isClosed

end RatFunc
