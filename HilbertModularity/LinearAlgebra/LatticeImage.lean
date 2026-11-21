/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Module.Lattice

/-! # Images of full lattices

A surjective linear map carries a full lattice to a full lattice. Applied to
coefficient projectors this constructs integral lattices in the labelled
factors used in [TripathiGoswami, determinant rigidity].
-/

@[expose] public noncomputable section

namespace Submodule.IsLattice

variable {R K V W : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
  [AddCommMonoid W] [Module R W] [Module K W] [IsScalarTower R K W]

/-- The image of a full lattice under a surjective linear map is a full lattice. -/
theorem map_of_surjective (M : Submodule R V) [IsLattice K M]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    IsLattice K (M.map (f.restrictScalars R)) where
  fg := IsLattice.fg.map (f.restrictScalars R)
  span_eq_top := by
    rw [Submodule.map_coe]
    change Submodule.span K (f '' (M : Set V)) = ⊤
    rw [← Submodule.map_span, IsLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr hf]

end Submodule.IsLattice
