/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.PromotedPowerTrace
public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTracePower

/-! # Hecke traces after representation promotion

Once one-place equivariance has been promoted to every coefficient completion,
the final trace formula at a target place only requires that the chosen
geometric prime be good for the target realization and the fixed eigenform.
There is no residual exclusion from the original comparison place. The same
actual Hilbert eigenform and algebraic character occur at every place.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- Every target good prime has the Hecke trace of the fixed eigenform,
scaled by the same algebraic comparison character. -/
theorem EigenformCompatibleSystem.heckeTrace_of_promotedComparison
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (S : EigenformCompatibleSystem φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (S.system.action w₀)))
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (S.system.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
          w.adicCompletion E) *
        algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq) := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  have h := ρ.powerTrace_of_promotedComparison S.system χ w₀ e₀ w g 1
  dsimp only [g] at h
  simp only [pow_one] at h
  rw [S.frobenius_trace w q hq P hP hp Q] at h
  exact h

/-- For residue degree two, the transported trace is the second Frobenius
power trace `χ(Frob)^2 (a_q^2 - 2 Nq ω_q)`. -/
theorem EigenformCompatibleSystem.heckeTrace_sq_of_promotedComparison
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (S : EigenformCompatibleSystem φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (S.system.action w₀)))
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (S.system.residueCharacteristic w : 𝓞 F) ∉ P)
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
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  have h := ρ.powerTrace_of_promotedComparison S.system χ w₀ e₀ w g 2
  dsimp only [g] at h
  rw [S.frobenius_trace_sq w q hq P hP hp Q] at h
  exact h

end HilbertModularity.HilbertModularForms
