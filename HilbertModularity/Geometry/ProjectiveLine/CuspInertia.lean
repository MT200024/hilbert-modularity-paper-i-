/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.Inertia
public import HilbertModularity.FieldTheory.RatFunc.InertiaInfinityTopology

/-! # Closed cusp inertia in the actual punctured-line fundamental group

Finite-coordinate inertia and the reciprocal-coordinate inertia at infinity
have closed images in the fundamental group based at the generic point.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.ProjectiveLine
universe u
variable (K : Type u) [Field K] [CharZero K]

/-- The generic fundamental-group image of actual inertia at infinity. -/
def puncturedInfinityInertia :
    Subgroup (Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K)) :=
  (RatFunc.infinityInertia K).map
    (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K))

/-- Finite-coordinate inertia has closed image in the actual fundamental group. -/
theorem isClosed_puncturedAffineInertia (a : K) : IsClosed
    (puncturedAffineInertia K a : Set
      (Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K))) := by
  rw [puncturedAffineInertia, Subgroup.coe_map]
  exact ((RatFunc.isClosed_affineInertia K a).isCompact.image
    (Scheme.continuous_galoisToEtaleFundamentalGroup (RatFunc K)
      (puncturedRationalPoint K))).isClosed

/-- Inertia at infinity has closed image in the actual fundamental group. -/
theorem isClosed_puncturedInfinityInertia : IsClosed
    (puncturedInfinityInertia K : Set
      (Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K))) := by
  rw [puncturedInfinityInertia, Subgroup.coe_map]
  exact ((RatFunc.isClosed_infinityInertia K).isCompact.image
    (Scheme.continuous_galoisToEtaleFundamentalGroup (RatFunc K)
      (puncturedRationalPoint K))).isClosed

end AlgebraicGeometry.ProjectiveLine
