/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalCompatibleSystem
public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTraceAfterPromotion

/-! # Hecke traces from independently constructed cohomological actions

The cohomological actions supply Hecke trace and determinant identities at every
coefficient place. Their compatible polynomial is derived in
`CohomologicalCompatibleSystem`. A comparison at one place then gives the
geometric-Frobenius traces at every other place by the promotion theorem.
The actions themselves are independent inputs, not constructed here.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The trace at a good prime equals the actual adelic Hecke eigenvalue,
scaled by the same finite algebraic character used in the one-place
comparison. The coefficient characteristic is excluded at the target place. -/
theorem EigenformCohomologicalActions.heckeTrace_of_promotedComparison
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (D.action w₀)))
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (D.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
          w.adicCompletion E) *
        algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq) := by
  let S := D.toCompatibleSystem
  have he : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (S.system.action w₀)) := by
    simpa only [S, D.toCompatibleSystem_action] using e₀
  have hpS : (S.system.residueCharacteristic w : 𝓞 F) ∉ P := by
    simpa only [S, D.toCompatibleSystem_residueCharacteristic] using hp
  exact S.heckeTrace_of_promotedComparison φ ρ χ w₀ he w q hq P hP hpS Q

/-- At residue degree two the same comparison gives the second Frobenius
power trace `χ(Frob)² (a_q² - 2 Nq ω_q)`, with the determinant coming from
the form's independent central Hecke coefficient. -/
theorem EigenformCohomologicalActions.heckeTrace_sq_of_promotedComparison
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (D.action w₀)))
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (D.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        ((ρ.action w
          (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) ^ 2) =
      (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
          w.adicCompletion E) ^ 2 *
        ((algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq)) ^ 2 -
          2 * ((Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion E) *
            algebraMap E (w.adicCompletion E) (φ.centralCoefficient q hq))) := by
  let S := D.toCompatibleSystem
  have he : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (S.system.action w₀)) := by
    simpa only [S, D.toCompatibleSystem_action] using e₀
  have hpS : (S.system.residueCharacteristic w : 𝓞 F) ∉ P := by
    simpa only [S, D.toCompatibleSystem_residueCharacteristic] using hp
  exact S.heckeTrace_sq_of_promotedComparison φ ρ χ w₀ he w q hq P hP hpS Q

end HilbertModularity.HilbertModularForms
