/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterTwist
public import HilbertModularity.RepresentationTheory.Duality

/-! # Duality and scalar character twists

Dualizing an inverse twist of a covariant representation gives the direct
twist of its cohomological dual. The inverse occurs because the dual action
uses the inverse group element. This is the convention used in
[TripathiGoswami, §3] after applying [SkinnerWiles, §4.5, Theorem A].
-/

public noncomputable section

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- Duality sends a scalar character twist to the inverse twist of the dual
representation. -/
def dualCharacterTwistEquiv (ρ : Representation K G V) (χ : G →* Kˣ) :
    (ρ.characterTwist χ).dual.Equiv (ρ.dual.characterTwist χ⁻¹) :=
  .mk (LinearEquiv.refl K (Module.Dual K V)) (by
    intro g
    ext φ v
    simp [Representation.dual_apply, Representation.characterTwist_apply,
      Module.Dual.transpose_apply])

/-- The form used after Skinner--Wiles: the dual of the inverse twist is the
direct twist of the cohomological dual. -/
def dualInverseCharacterTwistEquiv (ρ : Representation K G V) (χ : G →* Kˣ) :
    (ρ.characterTwist χ⁻¹).dual.Equiv (ρ.dual.characterTwist χ) :=
  .mk (LinearEquiv.refl K (Module.Dual K V)) (by
    intro g
    ext φ v
    simp [Representation.dual_apply, Representation.characterTwist_apply,
      Module.Dual.transpose_apply])

end Representation
