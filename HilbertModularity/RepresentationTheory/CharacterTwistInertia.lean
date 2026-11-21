/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterTwist
public import Mathlib.RingTheory.RamificationInertia.Inertia

/-! # Inertia of a comparison character

An intertwiner with a scalar twist detects the scalar at any element on which
both underlying representations act trivially.  The nonzero module hypothesis
is essential: every character twists the zero representation identically. -/

public section

namespace Representation

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [Nontrivial V]
  [AddCommGroup W] [Module K W]

/-- If two equivalent actions are trivial at one group element, their comparison
character is trivial there as well. -/
theorem character_eq_one_of_equiv_and_actions_eq_one
    (ρ : Representation K G W) (σ : Representation K G V)
    (ν : G →* Kˣ) (e : ρ.Equiv (σ.characterTwist ν))
    (g : G) (hρ : ρ g = 1) (hσ : σ g = 1) : ν g = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let w := e.toLinearEquiv.symm v
  have hw : e w = v := e.toLinearEquiv.apply_symm_apply v
  have he := congrArg (fun f : W →ₗ[K] V => f w) (e.isIntertwining' g)
  have hscalar : v = (ν g : K) • v := by
    simpa [hρ, hσ, characterTwist_apply, hw] using he
  apply Units.ext
  apply smul_left_injective K hv
  exact hscalar.symm.trans (one_smul K v).symm

variable {B : Type*} [CommRing B] [MulSemiringAction G B]

/-- Trivial inertia on both sides of a scalar-twist comparison forces trivial
inertia for the comparison character. -/
theorem character_inertia_trivial_of_equiv
    (ρ : Representation K G W) (σ : Representation K G V)
    (ν : G →* Kˣ) (e : ρ.Equiv (σ.characterTwist ν))
    (Q : Ideal B)
    (hρ : ∀ g ∈ Q.inertia G, ρ g = 1)
    (hσ : ∀ g ∈ Q.inertia G, σ g = 1) :
    ∀ g ∈ Q.inertia G, ν g = 1 := by
  intro g hg
  exact character_eq_one_of_equiv_and_actions_eq_one ρ σ ν e g
    (hρ g hg) (hσ g hg)

end Representation
