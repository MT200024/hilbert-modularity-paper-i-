/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalGlobalInertia
public import HilbertModularity.RepresentationTheory.LocalCharacterInertia
public import HilbertModularity.RepresentationTheory.InertiaCharacterAlgebraization

/-! # Algebraization of characters with spanning weight-zero periods

For the actual completions of a number field, spanning weight-zero periods at
the coefficient prime give finite local inertia by [Caruso2019, Theorem 2.2.1].
Local reciprocity gives finite inertia elsewhere. Completion and conjugacy
supply one exponent valid at every global prime above each finite prime.
The global finite-order and coefficient-field constructions then apply.

This proves the finite-character conclusion used in [TripathiGoswami,
Lemma `lem:rankonezero`] with its p-adic Hodge hypothesis stated as spanning
fixed periods of the actual restricted character. No de Rham predicate or
translation from labelled Hodge–Tate weights is silently assumed here.
-/

public noncomputable section

open NumberField IsDedekindDomain
open NumberField.LocalGalois

attribute [local instance] completionPadicAlgebra completionPadicTower

namespace HilbertModularity

variable (ell : ℕ) [Fact ell.Prime]
  {F E₀ L : Type} [Field F] [NumberField F]
  [Field E₀] [NumberField E₀]
  [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra ℚ_[ell] L] [ContinuousSMul ℚ_[ell] L] [FiniteDimensional ℚ_[ell] L]

/-- Spanning fixed periods at the coefficient prime imply finite inertia at
every finite prime, using the actual local restrictions. -/
theorem finite_local_inertia_of_zeroWeightPeriods
    (χ : HilbertModularForms.AbsoluteGalois F →* Lˣ) (hc : Continuous χ)
    (hperiods : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(ell : ℤ)})],
      HodgeTate.zeroWeightSpan
        (ι := (AlgEquiv.restrictScalarsHom ℚ_[ell] :
          Gal(PadicAlgCl ell/q.adicCompletion F) →* Gal(PadicAlgCl ell/ℚ_[ell])))
        ((Representation.ofCharacter (χ.comp (localGaloisRestriction ell F q))).restrictScalars
          ℚ_[ell]) = ⊤)
    (q : HeightOneSpectrum (𝓞 F)) :
    (Set.range ((χ.comp (localGaloisRestriction (primeBelow F q) F q)).comp
      (PadicAlgCl.inertia (primeBelow F q) (q.adicCompletion F)).subtype)).Finite := by
  by_cases h : primeBelow F q = ell
  · subst ell
    exact HodgeTate.finite_inertia_of_character_zeroWeightSpan
      (primeBelow F q) (q.adicCompletion F) L _
      (hc.comp (continuous_localGaloisRestriction _ F q)) (hperiods q)
  · exact finite_inertia_of_character_ne_coefficient_prime
      (primeBelow F q) ell h (q.adicCompletion F) L _
      (hc.comp (continuous_localGaloisRestriction _ F q))

/-- A continuous finitely ramified character with spanning weight-zero periods
at every place above the coefficient prime is a finite algebraic character.
The actual number-field coefficient extension lies inside the original local
field and preserves the initial embedding. Finite Hecke realizations use the
existing arithmetic reciprocity normalization at every complex embedding. -/
theorem exists_finiteAlgebraicCharacter_of_zeroWeightPeriods
    (ι₀ : E₀ →+* L)
    (χ : HilbertModularForms.AbsoluteGalois F →* Lˣ) (hc : Continuous χ)
    (bad : Finset (HeightOneSpectrum (𝓞 F)))
    (hunram : ∀ (q : HeightOneSpectrum (𝓞 F))
      (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal →
      ∀ g : HilbertModularForms.AbsoluteGalois F,
        g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad → χ g = 1)
    (hperiods : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(ell : ℤ)})],
      HodgeTate.zeroWeightSpan
        (ι := (AlgEquiv.restrictScalarsHom ℚ_[ell] :
          Gal(PadicAlgCl ell/q.adicCompletion F) →* Gal(PadicAlgCl ell/ℚ_[ell])))
        ((Representation.ofCharacter (χ.comp (localGaloisRestriction ell F q))).restrictScalars
          ℚ_[ell]) = ⊤) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    ∃ E : IntermediateField E₀ L,
      E.subtype.comp (algebraMap E₀ E) = ι₀ ∧
      ∃ _ : NumberField E, ∃ η : FiniteAlgebraicGaloisCharacter F E,
        (Units.map E.subtype.toMonoidHom).comp η.toMonoidHom = χ ∧
        ∀ ι : E →+* ℂ,
          Nonempty (HilbertModularForms.ArithmeticIdeleRealization η ι) := by
  classical
  have hexp := fun q => exists_uniform_inertia_exponent (primeBelow F q) F q χ
    (finite_local_inertia_of_zeroWeightPeriods ell χ hc hperiods q)
  choose n hn hi using hexp
  apply exists_finiteAlgebraicCharacter_of_inertia_exponents ι₀ χ hc bad n
    (fun q _ => hn q)
  intro q Q hQ hOver g hg
  exact ⟨fun _ => hi q Q hQ hOver g hg, hunram q Q hQ hOver g hg⟩

end HilbertModularity
