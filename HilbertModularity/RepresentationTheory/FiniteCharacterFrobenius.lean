/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter

/-! # Algebraic Frobenius values of a finite character

The finite image and local continuity give a finite abelian quotient. At a
prime where inertia acts trivially, Frobenius has one value in that quotient,
independent of the chosen prime of the algebraic closure.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.FiniteAlgebraicGaloisCharacter

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- Frobenius conjugacy and restriction in the finite abelian quotient cut out
by a continuous finite character: [MilneANT, §8.14–8.16, pp.141–142].
Finite range and continuity in any coefficient completion make the kernel open;
trivial inertia makes the corresponding finite extension unramified at `q`.
Milne's arithmetic Frobenius equality gives this geometric equality by inversion.
This input concerns only the character, not an RM or Euler representation. -/
theorem geometricFrobenius_eq
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ χ.bad)
    (Q Q' : Ideal (𝓞 (AlgebraicClosure F)))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    [Q'.IsMaximal] [Q'.LiesOver q.asIdeal] :
    χ.toMonoidHom (NumberField.geometricFrobenius F (AlgebraicClosure F) q.asIdeal Q) =
      χ.toMonoidHom (NumberField.geometricFrobenius F (AlgebraicClosure F) q.asIdeal Q') := by
  sorry

/-- At an unramified prime, one algebraic unit computes all the chosen lifts. -/
theorem exists_frobeniusValue
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ χ.bad) :
    ∃ c : Eˣ, ∀ (Q : Ideal (𝓞 (AlgebraicClosure F)))
      [Q.IsMaximal] [Q.LiesOver q.asIdeal],
      χ.toMonoidHom (NumberField.geometricFrobenius F (AlgebraicClosure F) q.asIdeal Q) = c := by
  obtain ⟨Q₀, hQ₀, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (AlgebraicClosure F)) q.asIdeal
  let := hQ₀
  let := hOver
  refine ⟨χ.toMonoidHom (NumberField.geometricFrobenius F (AlgebraicClosure F)
    q.asIdeal Q₀), ?_⟩
  intro Q _ _
  exact χ.geometricFrobenius_eq q hq Q Q₀

/-- The algebraic geometric-Frobenius value, extended by one at bad primes. -/
def frobeniusValue (χ : FiniteAlgebraicGaloisCharacter F E)
    (q : HeightOneSpectrum (𝓞 F)) : Eˣ := by
  classical
  exact if hq : q ∉ χ.bad then (χ.exists_frobeniusValue q hq).choose else 1

/-- At every good prime the algebraic value agrees with every absolute lift. -/
theorem frobeniusValue_eq (χ : FiniteAlgebraicGaloisCharacter F E)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ χ.bad)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    χ.frobeniusValue q =
      χ.toMonoidHom (NumberField.geometricFrobenius F (AlgebraicClosure F) q.asIdeal Q) := by
  dsimp only [frobeniusValue]
  rw [dite_eq_left hq]
  exact ((χ.exists_frobeniusValue q hq).choose_spec Q).symm

end HilbertModularity.FiniteAlgebraicGaloisCharacter
