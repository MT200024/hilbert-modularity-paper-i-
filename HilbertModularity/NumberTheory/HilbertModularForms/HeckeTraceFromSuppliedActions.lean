/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalOnePlaceUniqueness
public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTraceAtEveryGoodPrime

/-! # Hecke traces from a supplied eigenform action family

An independently constructed cohomological action family and a one-place
realization are compared at the same canonical coefficient completion. The
single-place arithmetic comparison then promotes to all coefficient places.
The action family and the arithmetic comparison are explicit inputs here.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- A cohomological one-place realization of an actual eigenform identifies
the selected action in an independently supplied all-place family. Promotion
then gives the finite-character Hecke trace at every good geometric prime,
using a coefficient place away from that prime. The only unproved input in
the resulting cone is the cited Frobenius semisimple detector. -/
theorem EigenformCohomologicalActions.promotedComparison_and_heckeTrace
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] (w₀.adicCompletion E)]
    (r : CohomologicalRealization φ p (w₀.adicCompletion E))
    (hp : p = D.residueCharacteristic w₀)
    (hι : r.coefficientEmbedding = algebraMap E (w₀.adicCompletion E))
    (hrs : r.action.IsSemisimpleRepresentation)
    (hcompare : Nonempty ((ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod r.action))) :
    (∀ w : HeightOneSpectrum (𝓞 E),
      Nonempty ((ρ.action w).Equiv
        ((Representation.ofCharacter (χ.local w)).tprod (D.action w)))) ∧
      ∀ (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
        (P : Ideal (𝓞 F)) [P.IsMaximal] (_hP : P = q.asIdeal),
        ∃ w : HeightOneSpectrum (𝓞 E),
          ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
            LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
              (ρ.action w
                (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
              (χ.toMonoidHom
                (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
                  w.adicCompletion E) *
                algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq) := by
  let e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (D.action w₀)) :=
    hcompare.some.trans
      (r.characterTensorEquiv_eigenformActions_at_place D w₀ p hp hι hrs (χ.local w₀))
  refine ⟨?_, ?_⟩
  · intro w
    have he₀ : (ρ.action w₀).Equiv
        ((Representation.ofCharacter (χ.local w₀)).tprod
          ((D.toCompatibleSystem).system.action w₀)) := by
      simpa only [D.toCompatibleSystem_action] using e₀
    simpa only [D.toCompatibleSystem_action] using
      ρ.promote_characterComparison (D.toCompatibleSystem).system χ w₀ he₀ w
  · intro q hq P _ hP
    exact D.exists_heckeTrace_of_promotedComparison ρ χ w₀ e₀ q hq P hP

/-- The same coefficient completion gives both Frobenius power traces needed
for residue degrees one and two. Its characteristic is chosen after the
geometric prime, while the eigenform and comparison character stay fixed. -/
theorem EigenformCohomologicalActions.exists_heckePowerTraces_of_onePlaceComparison
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] (w₀.adicCompletion E)]
    (r : CohomologicalRealization φ p (w₀.adicCompletion E))
    (hp : p = D.residueCharacteristic w₀)
    (hι : r.coefficientEmbedding = algebraMap E (w₀.adicCompletion E))
    (hrs : r.action.IsSemisimpleRepresentation)
    (hcompare : Nonempty ((ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod r.action)))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 E),
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
            (ρ.action w
              (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
          (χ.toMonoidHom
            (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
              w.adicCompletion E) *
            algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq) ∧
        LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
            ((ρ.action w
              (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) ^ 2) =
          (χ.toMonoidHom
            (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
              w.adicCompletion E) ^ 2 *
            ((algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq)) ^ 2 -
              2 * ((Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion E) *
                algebraMap E (w.adicCompletion E) (φ.centralCoefficient q hq))) := by
  let e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (D.action w₀)) :=
    hcompare.some.trans
      (r.characterTensorEquiv_eigenformActions_at_place D w₀ p hp hι hrs (χ.local w₀))
  obtain ⟨w, hw⟩ := D.exists_place_away_from_prime P
  refine ⟨w, ?_⟩
  intro Q _ _
  exact ⟨D.heckeTrace_of_promotedComparison ρ χ w₀ e₀ w q hq P hP hw Q,
    D.heckeTrace_sq_of_promotedComparison ρ χ w₀ e₀ w q hq P hP hw Q⟩

end HilbertModularity.HilbertModularForms
