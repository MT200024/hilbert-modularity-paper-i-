/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.EigenformCohomologicalExistence
public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTraceFromSuppliedActions
public import HilbertModularity.NumberTheory.HilbertModularForms.AlgebraicHeckePolynomialAfterPromotion

/-! # From a Hilbert eigenform to promoted Hecke traces

The cited all-place cohomological construction supplies actions for one actual
eigenform. At a fixed coefficient place, the place's rational residue prime
identifies the characteristic of an independent one-place realization with the
characteristic recorded by those actions. One comparison there then promotes to
all places and gives the first two Frobenius power traces at every good prime.
The one-place arithmetic comparison and its coefficient embedding remain
explicit inputs.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
  [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The independently constructed cohomological actions of an actual bounded
weight-two Hilbert eigenform give a compatible system and promoted comparison.
At each good geometric prime the same coefficient place, chosen away from its
residue characteristic, records both degree-one and degree-two Hecke traces.
The only literature admissions in this deduction are
`exists_eigenformCohomologicalActions` and the named Frobenius detector. -/
theorem AlgebraicGoodPrimeEigenform.exists_promotedHeckePowerTraces
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (hbounded : ∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C)
    (hcentral : (Set.range φ.form.central_character).Finite)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime]
    (hwp : w₀.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
    [NormedAlgebra ℚ_[p] (w₀.adicCompletion E)]
    (r : CohomologicalRealization φ p (w₀.adicCompletion E))
    (hι : r.coefficientEmbedding = algebraMap E (w₀.adicCompletion E))
    (hrs : r.action.IsSemisimpleRepresentation)
    (hcompare : Nonempty ((ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod r.action))) :
    ∃ D : EigenformCohomologicalActions φ,
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
  let D := (exists_eigenformCohomologicalActions φ hbounded hcentral).some
  have hp : p = D.residueCharacteristic w₀ :=
    residueCharacteristic_eq_of_same_coefficientPlace w₀ p
      (D.residueCharacteristic w₀) Fact.out
      (D.residueCharacteristic_prime w₀) hwp (D.coefficientPrime w₀)
  obtain ⟨hall, _⟩ :=
    D.promotedComparison_and_heckeTrace ρ χ w₀ p r hp hι hrs hcompare
  refine ⟨D, hall, ?_⟩
  intro q hq P _ hP
  exact D.exists_heckePowerTraces_of_onePlaceComparison
    ρ χ w₀ p r hp hι hrs hcompare q hq P hP

/-- The independently constructed eigenform system also identifies the
manuscript system's algebraic Frobenius polynomial with the character-scaled
Hecke polynomial. Both polynomials live in the fixed coefficient field `E`;
the canonical coefficient completion is used only for the one-place
comparison. -/
theorem AlgebraicGoodPrimeEigenform.algebraic_heckePolynomial_of_onePlaceComparison
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (hbounded : ∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C)
    (hcentral : (Set.range φ.form.central_character).Finite)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime]
    (hwp : w₀.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
    [NormedAlgebra ℚ_[p] (w₀.adicCompletion E)]
    (r : CohomologicalRealization φ p (w₀.adicCompletion E))
    (hι : r.coefficientEmbedding = algebraMap E (w₀.adicCompletion E))
    (hrs : r.action.IsSemisimpleRepresentation)
    (hcompare : Nonempty ((ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod r.action)))
    (q : HeightOneSpectrum (𝓞 F)) (hρ : q ∉ ρ.bad) (hφ : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    ρ.polynomial q = (φ.heckePolynomial q hφ).scaleRoots
      (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) := by
  let D := (exists_eigenformCohomologicalActions φ hbounded hcentral).some
  have hp : p = D.residueCharacteristic w₀ :=
    residueCharacteristic_eq_of_same_coefficientPlace w₀ p
      (D.residueCharacteristic w₀) Fact.out
      (D.residueCharacteristic_prime w₀) hwp (D.coefficientPrime w₀)
  let e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (D.action w₀)) :=
    hcompare.some.trans
      (r.characterTensorEquiv_eigenformActions_at_place D w₀ p hp hι hrs (χ.local w₀))
  exact D.algebraic_heckePolynomial_of_promotedComparison
    ρ χ w₀ e₀ q hρ hφ P hP Q

end HilbertModularity.HilbertModularForms
