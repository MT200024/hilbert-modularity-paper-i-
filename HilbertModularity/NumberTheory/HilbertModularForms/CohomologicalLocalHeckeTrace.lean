/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalActionUniqueness
public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalLocalPromotion
public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTracePower
public import HilbertModularity.RepresentationTheory.CompatibleSystemPlaces

/-! # Good-prime traces from an arbitrary local comparison

After absorbing the finite character in the actual eigenform, promotion gives
the degree-one and degree-two Hecke power traces at every good geometric prime.
The coefficient place is chosen after that prime, as in the final argument of
[TripathiGoswamiRevised, proof of `thm:intro-main`]. The effective compatible system and its
comparison to the local cohomological realization remain explicit inputs.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F A E : Type*} [Field F] [NumberField F] [Field A] [NumberField A]
  [NormedField E] {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] E]
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  {φ : AlgebraicGoodPrimeEigenform level μ A}
  {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- Every good geometric prime admits a coefficient completion where both
Hecke power-trace identities hold for the promoted system. In particular,
the residue characteristic of the initial local comparison is not excluded. -/
theorem CohomologicalRealization.exists_heckePowerTraces_of_localComparison
    (r : CohomologicalRealization φ p E)
    (S : NumberFieldCompatibleSystem F A) (T : EigenformCompatibleSystem φ)
    (σ : Representation E (AbsoluteGalois F) V) (e : σ.Equiv r.action)
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (S.polynomial q).map r.coefficientEmbedding)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 A),
      (T.system.residueCharacteristic w : 𝓞 F) ∉ P ∧
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
          (S.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
          algebraMap A (w.adicCompletion A) (φ.heckeCoefficient q hq) ∧
        LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
          ((S.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) ^ 2) =
          (algebraMap A (w.adicCompletion A) (φ.heckeCoefficient q hq)) ^ 2 -
            2 * ((Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion A) *
              algebraMap A (w.adicCompletion A) (φ.centralCoefficient q hq)) := by
  obtain ⟨w, hw⟩ := T.system.exists_place_away_from_prime P
  obtain ⟨ew⟩ := r.promote_localComparison S T σ e hlocal w
  refine ⟨w, hw, ?_⟩
  intro Q _ _
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  have htrace (n : ℕ) :
      LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
        ((S.action w g) ^ n) =
      LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
        ((T.system.action w g) ^ n) :=
    linearMap_trace_pow_eq_of_charpoly_eq
      (Pi.basisFun (w.adicCompletion A) (Fin 2))
      (S.action w g) (T.system.action w g) (ew.charpoly_eq g) n
  constructor
  · have ht := htrace 1
    simp only [pow_one] at ht
    exact ht.trans (T.frobenius_trace w q hq P hP hw Q)
  · exact (htrace 2).trans (T.frobenius_trace_sq w q hq P hP hw Q)

/-- Replacing the original vector by an eigenform with matching Hecke polynomials
preserves the promoted trace formulas at every good prime of the replacement.
The original vector's exceptional primes impose no restriction here. Existence
of such a replacement, and which primes it makes good, are separate obligations. -/
theorem CohomologicalRealization.exists_heckePowerTraces_of_matchingEigenform
    (r : CohomologicalRealization φ p E)
    {level' : FiniteLevel F} {μ' : AdditiveQuotientMeasure F}
    {ψ : AlgebraicGoodPrimeEigenform level' μ' A}
    (S : NumberFieldCompatibleSystem F A)
    (D : EigenformCohomologicalActions φ) (D' : EigenformCohomologicalActions ψ)
    (hhecke : ∀ q (hφ : q ∉ φ.form.bad) (hψ : q ∉ ψ.form.bad),
      φ.heckePolynomial q hφ = ψ.heckePolynomial q hψ)
    (σ : Representation E (AbsoluteGalois F) V) (e : σ.Equiv r.action)
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (S.polynomial q).map r.coefficientEmbedding)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ ψ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 A),
      (D'.residueCharacteristic w : 𝓞 F) ∉ P ∧
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
          (S.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
          algebraMap A (w.adicCompletion A) (ψ.heckeCoefficient q hq) ∧
        LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
          ((S.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) ^ 2) =
          (algebraMap A (w.adicCompletion A) (ψ.heckeCoefficient q hq)) ^ 2 -
            2 * ((Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion A) *
              algebraMap A (w.adicCompletion A) (ψ.centralCoefficient q hq)) := by
  let T := D'.toCompatibleSystem
  obtain ⟨w, hw⟩ := T.system.exists_place_away_from_prime P
  obtain ⟨eφ⟩ := r.promote_localComparison S D.toCompatibleSystem σ e hlocal w
  obtain ⟨eψ⟩ := D.equiv_of_heckePolynomial_eq D' hhecke w
  rw [D.toCompatibleSystem_action] at eφ
  let ew := eφ.trans eψ
  refine ⟨w, by simpa only [T, D'.toCompatibleSystem_residueCharacteristic] using hw, ?_⟩
  intro Q _ _
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  have htrace (n : ℕ) :
      LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
        ((S.action w g) ^ n) =
      LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
        ((T.system.action w g) ^ n) :=
    linearMap_trace_pow_eq_of_charpoly_eq
      (Pi.basisFun (w.adicCompletion A) (Fin 2))
      (S.action w g) (T.system.action w g)
      (by simpa only [T, D'.toCompatibleSystem_action] using ew.charpoly_eq g) n
  constructor
  · have ht := htrace 1
    simp only [pow_one] at ht
    exact ht.trans (T.frobenius_trace w q hq P hP hw Q)
  · exact (htrace 2).trans (T.frobenius_trace_sq w q hq P hP hw Q)

end HilbertModularity.HilbertModularForms
