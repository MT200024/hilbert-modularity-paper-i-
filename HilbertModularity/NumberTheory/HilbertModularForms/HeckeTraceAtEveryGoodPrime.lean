/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalHeckeTracePromotion
public import HilbertModularity.RepresentationTheory.CompatibleSystemPlaces

/-! # Choosing a coefficient place away from a geometric prime

The all-place comparison allows the coefficient place to be chosen after the
geometric prime. Places above two and three suffice: a proper prime ideal
cannot contain both rational integers. This removes a fixed coefficient-
characteristic exclusion from the good-prime Hecke trace consequence.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- A coefficient place above each rational prime is available for the
supplied eigenform actions. -/
theorem EigenformCohomologicalActions.exists_place_of_prime
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 E), D.residueCharacteristic w = p := by
  simpa only [D.toCompatibleSystem_residueCharacteristic] using
    D.toCompatibleSystem.system.exists_place_of_prime p hp

/-- One of two fixed coefficient places lies away from any geometric prime. -/
theorem EigenformCohomologicalActions.exists_place_away_from_prime
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (P : Ideal (𝓞 F)) [P.IsMaximal] :
    ∃ w : HeightOneSpectrum (𝓞 E),
      (D.residueCharacteristic w : 𝓞 F) ∉ P := by
  simpa only [D.toCompatibleSystem_residueCharacteristic] using
    D.toCompatibleSystem.system.exists_place_away_from_prime P

/-- For every good geometric prime there is a coefficient completion where
the promoted cohomological Hecke trace formula applies. -/
theorem EigenformCohomologicalActions.exists_heckeTrace_of_promotedComparison
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (D.action w₀)))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 E),
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
          (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
        (χ.toMonoidHom
          (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
            w.adicCompletion E) *
          algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq) := by
  obtain ⟨w, hw⟩ := D.exists_place_away_from_prime P
  exact ⟨w, fun Q _ _ =>
    D.heckeTrace_of_promotedComparison ρ χ w₀ e₀ w q hq P hP hw Q⟩

end HilbertModularity.HilbertModularForms
