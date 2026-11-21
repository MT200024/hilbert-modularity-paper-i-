/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesTwist
public import HilbertModularity.NumberTheory.HilbertModularForms.EigenformCohomologicalExistence

/-! # Compatible eigenform actions after Skinner--Wiles

The classical cusp-form output of Skinner--Wiles supplies the analytic
hypotheses for the cited all-place Galois construction. This module applies
that construction to the actual eigenform obtained after an integral
character twist. The one-place realization is retained separately; comparing
it with a canonical completion requires a specified coefficient-field map.
-/

public noncomputable section

open NumberField IsDedekindDomain
open scoped ValuativeRel

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- The direct twisted Skinner--Wiles route yields an actual eigenform and
its cohomological actions over all places of one coefficient number field.
Their shared Frobenius polynomial is derived by
`EigenformCohomologicalActions.toCompatibleSystem`; the cohomological
realization at the original lifting prime remains part of the output. -/
theorem skinnerWiles_weightTwoCompatibleSystem_characterTwist
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
          ∃ _D : EigenformCohomologicalActions φ,
            ∃ r : CohomologicalRealization φ p E,
              Nonempty (((ρ.characterTwist (integralCharacterToField u)).dual).Equiv
                r.action) := by
  obtain ⟨level, μ, A, hA, hN, φ, r, hbounded, hcentral, hequiv⟩ :=
    skinnerWiles_weightTwoEigenform_characterTwist_withAnalyticData
      p ρ L H u hu huc ramified_u hru hunramified
  let : NumberField.IsTotallyReal F := H.totally_real
  exact ⟨level, μ, A, hA, hN, φ,
    (exists_eigenformCohomologicalActions φ hbounded hcentral).some,
    r, hequiv⟩

end HilbertModularity.HilbertModularForms
