/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter
public import HilbertModularity.RepresentationTheory.CharacterTwistInertia

/-! # The exact ramification set of a comparison character

A finite character may be presented with an unnecessarily large exceptional set.
Its actual ramified primes form a finite subset. At any prime where a nonzero
twist comparison has unramified actions on both sides, the character is
unramified too. This is the good-prime argument needed in
[TripathiGoswamiRevised, Theorem `RMgeneral`].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.FiniteAlgebraicGaloisCharacter

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- Primes where some absolute inertia element has a nontrivial character value. -/
def ramifiedPrimes (χ : FiniteAlgebraicGaloisCharacter F E) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  {q | ∃ (Q : Ideal (𝓞 (AlgebraicClosure F))),
    Q.IsMaximal ∧ Q.LiesOver q.asIdeal ∧
      ∃ g : HilbertModularForms.AbsoluteGalois F,
        g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) ∧ χ.toMonoidHom g ≠ 1}

/-- Every actual ramified prime belongs to the originally supplied bad set. -/
theorem ramifiedPrimes_subset_bad (χ : FiniteAlgebraicGaloisCharacter F E) :
    χ.ramifiedPrimes ⊆ χ.bad := by
  intro q hq
  by_contra hgood
  obtain ⟨Q, hQ, hOver, g, hg, hχ⟩ := hq
  let := hQ
  let := hOver
  exact hχ (χ.unramified q hgood q.asIdeal rfl Q g hg)

theorem ramifiedPrimes_finite (χ : FiniteAlgebraicGaloisCharacter F E) :
    χ.ramifiedPrimes.Finite :=
  χ.bad_finite.subset χ.ramifiedPrimes_subset_bad

/-- The same algebraic character with precisely its actual ramification set. -/
def withExactRamification (χ : FiniteAlgebraicGaloisCharacter F E) :
    FiniteAlgebraicGaloisCharacter F E where
  toMonoidHom := χ.toMonoidHom
  finite_range := χ.finite_range
  local_continuous := χ.local_continuous
  bad := χ.ramifiedPrimes
  bad_finite := χ.ramifiedPrimes_finite
  unramified := by
    intro q hq P _ hP Q _ _ g hg
    subst P
    by_contra hχ
    exact hq ⟨Q, inferInstance, inferInstance, g, hg, hχ⟩

/-- Changing the exceptional-set certificate leaves every character value intact. -/
theorem withExactRamification_toMonoidHom (χ : FiniteAlgebraicGaloisCharacter F E) :
    χ.withExactRamification.toMonoidHom = χ.toMonoidHom := (rfl)

/-- The normalized bad set is the exact inertia-defined set. -/
theorem withExactRamification_bad (χ : FiniteAlgebraicGaloisCharacter F E) :
    χ.withExactRamification.bad = χ.ramifiedPrimes := (rfl)

/-- A local comparison of nonzero unramified representations rules out actual
character ramification. The coefficient map is injective because it is a field
homomorphism; one local realization suffices at the chosen prime. -/
theorem not_mem_ramifiedPrimes_of_unramified_comparison
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (q : HeightOneSpectrum (𝓞 F))
    {L V W : Type*} [Field L]
    [AddCommGroup V] [Module L V] [Nontrivial V]
    [AddCommGroup W] [Module L W]
    (j : E →+* L)
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois F) W)
    (σ : Representation L (HilbertModularForms.AbsoluteGalois F) V)
    (e : ρ.Equiv (σ.characterTwist
      ((Units.map j.toMonoidHom).comp χ.toMonoidHom)))
    (hρ : ∀ (Q : Ideal (𝓞 (AlgebraicClosure F)))
      [Q.IsMaximal] [Q.LiesOver q.asIdeal],
      ∀ g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F), ρ g = 1)
    (hσ : ∀ (Q : Ideal (𝓞 (AlgebraicClosure F)))
      [Q.IsMaximal] [Q.LiesOver q.asIdeal],
      ∀ g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F), σ g = 1) :
    q ∉ χ.ramifiedPrimes := by
  rintro ⟨Q, hQ, hOver, g, hg, hχ⟩
  let := hQ
  let := hOver
  have h := Representation.character_inertia_trivial_of_equiv
    ρ σ _ e Q (hρ Q) (hσ Q) g hg
  apply hχ
  apply Units.ext
  apply j.injective
  change j (χ.toMonoidHom g : E) = j 1
  rw [map_one]
  exact congrArg (fun u : Lˣ => (u : L)) h

end HilbertModularity.FiniteAlgebraicGaloisCharacter
