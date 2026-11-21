/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Units

/-! # Continuous determinant characters

The determinant of a group representation is canonically unit-valued.
For a finite basis with continuous coordinates, pointwise continuity of the
representation implies continuity of this character. These constructions give
the actual determinant-ratio character used in
[TripathiGoswami, determinant rigidity].
-/

@[expose] public noncomputable section

namespace Representation

variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- The unit-valued determinant character of a group representation. -/
def determinantCharacter (ρ : Representation R G V) : G →* Rˣ :=
  MonoidHom.toHomUnits (LinearMap.det.comp ρ)

@[simp]
theorem determinantCharacter_coe (ρ : Representation R G V) (g : G) :
    (determinantCharacter ρ g : R) = LinearMap.det (ρ g) := rfl

section Topological

variable [TopologicalSpace R] [IsTopologicalRing R]
  [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι R V)
  (hb : ∀ i, Continuous (b.coord i))
  (ρ : Representation R G V) (hρ : ∀ v, Continuous (fun g => ρ g v))

omit [ContinuousInv G] in
include b hb hρ in
/-- Continuity of matrix coefficients gives continuity of the determinant. -/
theorem continuous_determinant_of_basis : Continuous (fun g => LinearMap.det (ρ g)) := by
  have hm : Continuous (fun g => LinearMap.toMatrix b b (ρ g)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa only [LinearMap.toMatrix_apply, Module.Basis.coord_apply, Function.comp_def] using (hb i).comp (hρ (b j))
  simpa only [LinearMap.det_toMatrix] using hm.matrix_det

include b hb hρ in
/-- The canonical determinant character is continuous for a continuous finite-basis action. -/
theorem continuous_determinantCharacter_of_basis : Continuous (determinantCharacter ρ) := by
  apply Continuous.of_coeHom_comp
  exact continuous_determinant_of_basis b hb ρ hρ

/-- Bundle the actual determinant character with its proved continuity. -/
def continuousDeterminantCharacter : G →ₜ* Rˣ :=
  ⟨determinantCharacter ρ, continuous_determinantCharacter_of_basis b hb ρ hρ⟩

@[simp]
theorem continuousDeterminantCharacter_coe (g : G) :
    (continuousDeterminantCharacter b hb ρ hρ g : R) = LinearMap.det (ρ g) := rfl

end Topological

end Representation
