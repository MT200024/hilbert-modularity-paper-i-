/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterComparison
public import HilbertModularity.RepresentationTheory.CharacterTwist
public import Mathlib.RepresentationTheory.Character

/-! # Trace of a fixed finite-character comparison -/

public noncomputable section

namespace HilbertModularity.Examples

/-- An actual equivalence between a character twist and an effective
representation gives the exact character-times-fixed-trace equality at each
group element. This is the trace step of the manuscript's finite comparison. -/
theorem trace_of_characterTensorEquiv
    {K G V W : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρRM : Representation K G V) (ρEff : Representation K G W)
    (ν : G →* Kˣ)
    (e : ((Representation.ofCharacter ν).tprod ρRM).Equiv ρEff)
    (g : G) :
    ρEff.character g = (ν g : K) * ρRM.character g := by
  let etwist := (Representation.characterTwistTensorEquiv ρRM ν).symm.trans e
  have h := congrArg (fun f : G → K => f g) (Representation.char_iso etwist)
  calc
    ρEff.character g = (Representation.characterTwist ρRM ν).character g := h.symm
    _ = (ν g : K) * ρRM.character g := by
      change LinearMap.trace K V ((ν g : K) • ρRM g) =
        (ν g : K) * LinearMap.trace K V (ρRM g)
      rw [map_smul]
      rfl

end HilbertModularity.Examples
