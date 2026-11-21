/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Character

/-! # Character values in a chosen RM factor basis -/

public noncomputable section

namespace HilbertModularity.Examples

/-- A representation's character is the trace of its matrix in any finite
basis, matching the trace used in the worked quadratic factors. -/
theorem representation_matrixTrace_eq_character
    {L G V ι : Type*} [Field L] [Group G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Fintype ι] [DecidableEq ι]
    (ρ : Representation L G V) (g : G)
    (b : Module.Basis ι L V) :
    (LinearMap.toMatrix b b (ρ g)).trace = ρ.character g := by
  change (LinearMap.toMatrix b b (ρ g)).trace = LinearMap.trace L V (ρ g)
  rw [LinearMap.trace_eq_matrix_trace L b]

end HilbertModularity.Examples
