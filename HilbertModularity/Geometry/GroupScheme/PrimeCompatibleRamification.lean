/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCompatibleSystem
public import HilbertModularity.Geometry.GroupScheme.PrimeCharacterRamification
public import HilbertModularity.Geometry.GroupScheme.PrimeGoodSpecialization
public import HilbertModularity.RepresentationTheory.CompatibleSystemTwist

/-! # No additional bad primes in the selected comparison system

The exact ramification set of the finite comparison character is controlled by
the Euler action and the selected plus Jacobian. Consequently the twisted system
has no exceptional primes beyond the manuscript's geometric exclusions.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

/-- An actual unramified comparison controls the whole twisted system's bad set.
The character is unchanged; only its exceptional-set certificate is made exact.
This proves the exceptional-set deduction used in
[TripathiGoswamiRevised, Theorem `RMgeneral` and Theorem `intro-main`].

The supplied set must contain the selected Jacobian's bad-reduction primes and
all primes over the chosen coefficient characteristic. The compared action must
be unramified outside that set. No separate character-ramification premise is
required. -/
theorem primePlusCompatibleSystem_twist_bad_subset_of_comparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type) [Field E] [NumberField E]
    (hE : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ E)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] E)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) E)
    (T : Set (HeightOneSpectrum (𝓞 (realCyclotomicField p))))
    (hgood : primePlusFiberBadPrimes p hp ξ ⊆ T)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ∀ P, P ∉ T → (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (j : E →ₐ[ℚ] L)
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois (realCyclotomicField p)) V)
    (e : ρ.Equiv ((primePlusCohomologicalAction p hp ξ ℓ L hL (j.comp σ)).characterTwist
      ((Units.map j.toRingHom.toMonoidHom).comp χ.toMonoidHom)))
    (hρ : ∀ P, P ∉ T →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P.asIdeal],
        ∀ g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois (realCyclotomicField p)),
          ρ g = 1) :
    ((primePlusCompatibleSystem p hp ξ E hE σ).characterTwist
      χ.withExactRamification).bad ⊆ T := by
  apply NumberFieldCompatibleSystem.characterTwist_bad_subset
  · simpa only [primePlusCompatibleSystem_bad] using hgood
  · rw [FiniteAlgebraicGaloisCharacter.withExactRamification_bad]
    intro P hP
    by_contra hPT
    exact (not_mem_ramifiedPrimes_of_primePlus_comparison p hp ξ E χ P
      (fun h => hPT (hgood h)) ℓ (hℓ P hPT) L hL (j.comp σ) j.toRingHom
      ρ e (hρ P hPT)) hP

/-- At a rational parameter the selected comparison system has no extra bad
primes. The selected Jacobian's good models and the exclusion of the coefficient
prime are derived from the canonical good-unit conditions. Only the actual
Euler-side comparison and its good-prime inertia property remain to be supplied.
This is the exceptional-set application in [TripathiGoswamiRevised,
Theorem `intro-main`]. -/
theorem primePlusCompatibleSystem_twist_bad_subset_of_rational_comparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (x : ℚ) (hx : ξ.val = algebraMap ℚ (realCyclotomicField p) x)
    (E : Type) [Field E] [NumberField E]
    (hE : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ E)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] E)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) E)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (j : E →ₐ[ℚ] L)
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois (realCyclotomicField p)) V)
    (e : ρ.Equiv ((primePlusCohomologicalAction p hp ξ p L hL (j.comp σ)).characterTwist
      ((Units.map j.toRingHom.toMonoidHom).comp χ.toMonoidHom)))
    (hρ : ∀ P : HeightOneSpectrum (𝓞 (realCyclotomicField p)),
      P.GoodUnit ξ.val → (p : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P.asIdeal],
        ∀ g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois (realCyclotomicField p)),
          ρ g = 1) :
    ((primePlusCompatibleSystem p hp ξ E hE σ).characterTwist
      χ.withExactRamification).bad ⊆ LocalSpecialization.badPrimesAbove ξ.val p := by
  apply primePlusCompatibleSystem_twist_bad_subset_of_comparison p hp ξ E hE σ χ
    (LocalSpecialization.badPrimesAbove ξ.val p)
    (primePlusFiberBadPrimes_subset_of_rational_parameter p hp ξ x hx) p
    (fun P hP => ((LocalSpecialization.not_mem_badPrimesAbove_iff ξ.val p P).mp hP).2)
    L hL j ρ e
  intro P hP Q _ _ g hg
  obtain ⟨hξ, hpP⟩ := (LocalSpecialization.not_mem_badPrimesAbove_iff ξ.val p P).mp hP
  exact hρ P hξ hpP Q g hg

end HilbertModularity.Hypergeometric
