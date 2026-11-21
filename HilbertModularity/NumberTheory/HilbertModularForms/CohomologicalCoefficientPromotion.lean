/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalLocalHeckeTrace

/-! # Promotion when the replacement eigenform enlarges coefficients

The local comparison first identifies polynomials in the original number field.
Mapping those polynomials into the replacement field then permits semisimple
comparison at every new coefficient place. No embedding of the replacement
field into the original local field is required. This is the coefficient step
in the good-prime replacement used in [TripathiGoswamiRevised,
proof of `thm:intro-main`].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F A E : Type*} [Field F] [NumberField F] [Field A] [NumberField A]
  [NormedField E] {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] E]
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  {φ : AlgebraicGoodPrimeEigenform level μ A}
  {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- Compare an independently given system over the enlarged coefficient field
with a replacement eigenform. Its good-prime polynomials must be the images
of the original algebraic polynomials verified by the local comparison.
This retains a substantive compatibility premise on the new system; it does
not construct that system or assume an embedding into the original local field. -/
theorem CohomologicalRealization.promote_matchingEigenform_coefficients
    (r : CohomologicalRealization φ p E)
    {B : Type*} [Field B] [NumberField B]
    {level' : FiniteLevel F} {μ' : AdditiveQuotientMeasure F}
    {ψ : AlgebraicGoodPrimeEigenform level' μ' B}
    (i : A →+* B) (S : NumberFieldCompatibleSystem F B)
    (T : EigenformCompatibleSystem ψ)
    (f : HeightOneSpectrum (𝓞 F) → Polynomial A)
    (hcoeff : ∀ q, q ∉ S.bad → S.polynomial q = (f q).map i)
    (hhecke : ∀ q (hφ : q ∉ φ.form.bad) (hψ : q ∉ ψ.form.bad),
      (φ.heckePolynomial q hφ).map i = ψ.heckePolynomial q hψ)
    (σ : Representation E (AbsoluteGalois F) V) (e : σ.Equiv r.action)
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (f q).map r.coefficientEmbedding)
    (w : HeightOneSpectrum (𝓞 B)) :
    Nonempty ((S.action w).Equiv (T.system.action w)) := by
  let bad := ((S.badAt w ∪ T.system.badAt w) ∪ φ.form.bad) ∪
    {q | (p : 𝓞 F) ∈ q.asIdeal}
  have hpfin : Set.Finite {q : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ q.asIdeal} := by
    apply HeightOneSpectrum.finite_primes_containing
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hbad : bad.Finite := (((S.badAt_finite w).union (T.system.badAt_finite w)).union
    φ.form.bad_finite).union hpfin
  have hgood (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ bad) :
      q ∉ S.bad ∧ q ∉ ψ.form.bad ∧ q ∉ φ.form.bad ∧
      (S.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal ∧
      (T.system.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal ∧
      (p : 𝓞 F) ∉ q.asIdeal := by
    have hs : q ∉ S.badAt w := fun h => hq (Or.inl (Or.inl (Or.inl h)))
    have ht : q ∉ T.system.badAt w := fun h => hq (Or.inl (Or.inl (Or.inr h)))
    obtain ⟨hs, hsp⟩ := S.good_of_not_mem_badAt w q hs
    obtain ⟨ht, htp⟩ := T.system.good_of_not_mem_badAt w q ht
    exact ⟨hs, T.bad_eq ▸ ht, fun h => hq (Or.inl (Or.inr h)),
      hsp, htp, fun h => hq (Or.inr h)⟩
  apply frobenius_semisimple_detection w (S.residueCharacteristic w)
    (S.residueCharacteristic_prime w) (S.coefficientPrime w)
    (S.action w) (T.system.action w) (S.continuous w) (T.system.continuous w)
    (S.semisimple w) (T.system.semisimple w) bad hbad
  · intro q hq P _ hP hp Q _ _ g hg
    exact S.unramified w q (hgood q hq).1 P hP hp Q g hg
  · intro q hq P _ hP _ Q _ _ g hg
    obtain ⟨_, ht, _, _, htp, _⟩ := hgood q hq
    exact T.system.unramified w q (T.bad_eq ▸ ht) P hP (hP.symm ▸ htp) Q g hg
  · intro q hq P _ hP hp Q _ _
    obtain ⟨hs, ht, hφ, _, htp, hpp⟩ := hgood q hq
    have hf := r.polynomial_eq_of_localComparison σ e (f q) q hφ
      P hP (hP.symm ▸ hpp) Q (hlocal q hs P hP (hP.symm ▸ hpp) Q)
    rw [S.frobenius_charpoly w q hs P hP hp Q, hcoeff q hs, hf, hhecke q hφ ht]
    exact (T.frobenius_charpoly w q ht P hP (hP.symm ▸ htp) Q).symm


/-- After changing coefficient fields, the local comparison still gives both
power-trace formulas at every good prime of the replacement. The coefficient
place can be chosen after the geometric prime; the original local field and
its residue characteristic impose no exclusion on that geometric prime. -/
theorem CohomologicalRealization.exists_heckePowerTraces_of_coefficientExtension
    (r : CohomologicalRealization φ p E)
    {B : Type*} [Field B] [NumberField B]
    {level' : FiniteLevel F} {μ' : AdditiveQuotientMeasure F}
    {ψ : AlgebraicGoodPrimeEigenform level' μ' B}
    (i : A →+* B) (S : NumberFieldCompatibleSystem F B)
    (T : EigenformCompatibleSystem ψ)
    (f : HeightOneSpectrum (𝓞 F) → Polynomial A)
    (hcoeff : ∀ q, q ∉ S.bad → S.polynomial q = (f q).map i)
    (hhecke : ∀ q (hφ : q ∉ φ.form.bad) (hψ : q ∉ ψ.form.bad),
      (φ.heckePolynomial q hφ).map i = ψ.heckePolynomial q hψ)
    (σ : Representation E (AbsoluteGalois F) V) (e : σ.Equiv r.action)
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (f q).map r.coefficientEmbedding)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ ψ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 B),
      (T.system.residueCharacteristic w : 𝓞 F) ∉ P ∧
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        LinearMap.trace (w.adicCompletion B) (Fin 2 → w.adicCompletion B)
          (S.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
          algebraMap B (w.adicCompletion B) (ψ.heckeCoefficient q hq) ∧
        LinearMap.trace (w.adicCompletion B) (Fin 2 → w.adicCompletion B)
          ((S.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) ^ 2) =
          (algebraMap B (w.adicCompletion B) (ψ.heckeCoefficient q hq)) ^ 2 -
            2 * ((Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion B) *
              algebraMap B (w.adicCompletion B) (ψ.centralCoefficient q hq)) := by
  obtain ⟨w, hw⟩ := T.system.exists_place_away_from_prime P
  obtain ⟨ew⟩ := r.promote_matchingEigenform_coefficients i S T f hcoeff hhecke σ e hlocal w
  refine ⟨w, hw, ?_⟩
  intro Q _ _
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  have htrace (n : ℕ) :
      LinearMap.trace (w.adicCompletion B) (Fin 2 → w.adicCompletion B)
        ((S.action w g) ^ n) =
      LinearMap.trace (w.adicCompletion B) (Fin 2 → w.adicCompletion B)
        ((T.system.action w g) ^ n) :=
    linearMap_trace_pow_eq_of_charpoly_eq
      (Pi.basisFun (w.adicCompletion B) (Fin 2))
      (S.action w g) (T.system.action w g) (ew.charpoly_eq g) n
  constructor
  · have ht := htrace 1
    simp only [pow_one] at ht
    exact ht.trans (T.frobenius_trace w q hq P hP hw Q)
  · exact (htrace 2).trans (T.frobenius_trace_sq w q hq P hP hw Q)

end HilbertModularity.HilbertModularForms
