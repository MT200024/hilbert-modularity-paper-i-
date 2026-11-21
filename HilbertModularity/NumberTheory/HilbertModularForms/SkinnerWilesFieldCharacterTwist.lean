/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.IntegralFiniteCharacter
public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesTwist

/-! # Skinner--Wiles after a field-valued finite character twist

The finite character in the manuscript's comparison is initially valued in a
`p`-adic coefficient field. Its finite image makes it integral, after which
the full [SkinnerWiles, §4.5, Theorem A] checklist transports by the proved
integral character twist. Finite ramification remains an explicit hypothesis.
-/

public noncomputable section

open NumberField IsDedekindDomain
open scoped ValuativeRel

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- Direct weight-two lifting for a finite field-valued twist. The resulting
cohomological realization has the inverse twist required by duality between
the covariant Skinner--Wiles representation and the manuscript's chosen
cohomological representation. No separate automorphic twist admission is used.
-/
theorem skinnerWiles_cohomologicalFiniteCharacterTwist
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    (ν : AbsoluteGalois F →* Eˣ)
    (hν : (Set.range ν).Finite) (hνc : Continuous ν)
    (ramified_ν : Set (HeightOneSpectrum (𝓞 F)))
    (hrν : ramified_ν.Finite)
    (hunramified : ∀ q, q ∉ ramified_ν →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois F, g ∈ Q.inertia (AbsoluteGalois F) → ν g = 1) :
    ∃ (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F) (A : Type)
      (hA : Field A),
      letI : Field A := hA
      ∃ hN : NumberField A,
        letI : NumberField A := hN
        ∃ φ : AlgebraicGoodPrimeEigenform level μ A,
          ∃ r : CohomologicalRealization φ p E,
            Nonempty ((ρ.dual.characterTwist ν⁻¹).Equiv r.action) := by
  let u := finiteCharacterIntegralLift ν hν
  have hu : (Set.range u).Finite :=
    finiteCharacterIntegralLift_finite_range ν hν
  have huc : Continuous u :=
    continuous_finiteCharacterIntegralLift ν hν hνc
  have hunramified_u : ∀ q, q ∉ ramified_ν →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois F, g ∈ Q.inertia (AbsoluteGalois F) → u g = 1 := by
    intro q hq P _ hP Q _ _ g hg
    exact (finiteCharacterIntegralLift_apply_eq_one_iff ν hν g).2
      (hunramified q hq P hP Q g hg)
  have heq : integralCharacterToField u = ν := by
    ext g
    have h := congrArg (fun x : Eˣ => (x : E))
      (finiteCharacterIntegralLift_toField ν hν g)
    simpa only [integralCharacterToField_apply, u] using h
  have h := skinnerWiles_cohomologicalCharacterTwist p ρ L H u hu huc
    ramified_ν hrν hunramified_u
  simpa only [heq] using h

/-- Apply the direct lifting route with the inverse of a finite comparison
character. The resulting cohomological realization carries the original
character, as required by the manuscript's effective-representation
comparison. Finite ramification is supplied explicitly. -/
theorem skinnerWiles_cohomologicalFiniteCharacterTwist_inverse
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    (ν : AbsoluteGalois F →* Eˣ)
    (hν : (Set.range ν).Finite) (hνc : Continuous ν)
    (ramified_ν : Set (HeightOneSpectrum (𝓞 F)))
    (hrν : ramified_ν.Finite)
    (hunramified : ∀ q, q ∉ ramified_ν →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois F, g ∈ Q.inertia (AbsoluteGalois F) → ν g = 1) :
    ∃ (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F) (A : Type)
      (hA : Field A),
      letI : Field A := hA
      ∃ hN : NumberField A,
        letI : NumberField A := hN
        ∃ φ : AlgebraicGoodPrimeEigenform level μ A,
          ∃ r : CohomologicalRealization φ p E,
            Nonempty ((ρ.dual.characterTwist ν).Equiv r.action) := by
  have hνinv : (Set.range ν⁻¹).Finite :=
    finiteCharacter_inverse_finite_range ν hν
  have hνinvc : Continuous ν⁻¹ :=
    continuous_finiteCharacter_inverse ν hνc
  have hunramified_inv : ∀ q, q ∉ ramified_ν →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois F, g ∈ Q.inertia (AbsoluteGalois F) → ν⁻¹ g = 1 := by
    intro q hq P _ hP Q _ _ g hg
    change (ν g)⁻¹ = 1
    simp [hunramified q hq P hP Q g hg]
  have hinv : (ν⁻¹)⁻¹ = ν := by
    ext g
    simp
  simpa only [hinv] using
    skinnerWiles_cohomologicalFiniteCharacterTwist p ρ L H ν⁻¹ hνinv hνinvc
      ramified_ν hrν hunramified_inv

end HilbertModularity.HilbertModularForms
