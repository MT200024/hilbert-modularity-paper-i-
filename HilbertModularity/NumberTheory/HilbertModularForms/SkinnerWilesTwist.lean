/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWiles
public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesCharacterTwist
public import HilbertModularity.NumberTheory.HilbertModularForms.CharacterTwistDuality

/-! # Applying Skinner--Wiles after a finite character twist

The full weight-two lifting checklist is stable under an explicitly finitely
ramified finite integral character. Applying [SkinnerWiles, §4.5, Theorem A]
to that twisted covariant representation produces a genuine cuspidal Hilbert
eigenform for its cohomological dual. This gives the direct lifting route
without a separate level-changing automorphic twist input.
-/

public noncomputable section

open NumberField IsDedekindDomain
open scoped ValuativeRel

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- Apply [SkinnerWiles, §4.5, Theorem A] to the actual scalar twist.
The bounded adelic lift and finite-image central character are retained for
the all-place cohomological action construction. -/
theorem skinnerWiles_weightTwoEigenform_characterTwist_withAnalyticData
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (hu : (Set.range u).Finite) (huc : Continuous u)
    (ramified_u : Set (HeightOneSpectrum (𝓞 F)))
    (hru : ramified_u.Finite)
    (hunramified : ∀ q, q ∉ ramified_u →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois F, g ∈ Q.inertia (AbsoluteGalois F) → u g = 1) :
    ∃ (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F) (A : Type)
      (hA : Field A),
      letI : Field A := hA
      ∃ hN : NumberField A,
        letI : NumberField A := hN
        ∃ φ : AlgebraicGoodPrimeEigenform level μ A,
          ∃ r : CohomologicalRealization φ p E,
            (∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C) ∧
            (Set.range φ.form.central_character).Finite ∧
            Nonempty ((ρ.characterTwist (integralCharacterToField u)).dual.Equiv
              r.action) := by
  exact skinnerWiles_weightTwoEigenform_withAnalyticData p
    (ρ.characterTwist (integralCharacterToField u)) L
    (H.characterTwist p u hu huc ramified_u hru hunramified)

/-- The previous direct lifting API, projected from the stronger analytic
output of [SkinnerWiles, §4.5, Theorem A]. -/
theorem skinnerWiles_weightTwoEigenform_characterTwist
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (hu : (Set.range u).Finite) (huc : Continuous u)
    (ramified_u : Set (HeightOneSpectrum (𝓞 F)))
    (hru : ramified_u.Finite)
    (hunramified : ∀ q, q ∉ ramified_u →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois F, g ∈ Q.inertia (AbsoluteGalois F) → u g = 1) :
    ∃ (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F) (A : Type)
      (hA : Field A),
      letI : Field A := hA
      ∃ hN : NumberField A,
        letI : NumberField A := hN
        ∃ φ : AlgebraicGoodPrimeEigenform level μ A,
          ∃ r : CohomologicalRealization φ p E,
            Nonempty ((ρ.characterTwist (integralCharacterToField u)).dual.Equiv
              r.action) := by
  obtain ⟨level, μ, A, hA, hN, φ, r, _, _, hequiv⟩ :=
    skinnerWiles_weightTwoEigenform_characterTwist_withAnalyticData
      p ρ L H u hu huc ramified_u hru hunramified
  exact ⟨level, μ, A, hA, hN, φ, r, hequiv⟩

/-- The same direct lifting consequence expressed as a twist of the
cohomological dual. The inverse character records the covariant-to-cohomological
duality in [SkinnerWiles, §4.5, Theorem A]; no extra automorphic twisting theorem
is used. -/
theorem skinnerWiles_cohomologicalCharacterTwist
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (hu : (Set.range u).Finite) (huc : Continuous u)
    (ramified_u : Set (HeightOneSpectrum (𝓞 F)))
    (hru : ramified_u.Finite)
    (hunramified : ∀ q, q ∉ ramified_u →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois F, g ∈ Q.inertia (AbsoluteGalois F) → u g = 1) :
    ∃ (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F) (A : Type)
      (hA : Field A),
      letI : Field A := hA
      ∃ hN : NumberField A,
        letI : NumberField A := hN
        ∃ φ : AlgebraicGoodPrimeEigenform level μ A,
          ∃ r : CohomologicalRealization φ p E,
            Nonempty ((ρ.dual.characterTwist (integralCharacterToField u)⁻¹).Equiv
              r.action) := by
  obtain ⟨level, μ, A, hA, hN, φ, r, ⟨e⟩⟩ :=
    skinnerWiles_weightTwoEigenform_characterTwist p ρ L H u hu huc
      ramified_u hru hunramified
  exact ⟨level, μ, A, hA, hN, φ, r,
    ⟨(ρ.dualCharacterTwistEquiv (integralCharacterToField u)).symm.trans e⟩⟩

end HilbertModularity.HilbertModularForms
