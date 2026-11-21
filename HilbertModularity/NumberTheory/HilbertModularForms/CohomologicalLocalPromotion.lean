/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalFrobeniusPolynomial
public import HilbertModularity.RepresentationTheory.FrobeniusSemisimpleDetection

/-! # Promotion from an arbitrary local realization

The comparison field in [TripathiGoswami, `lem:promotion` and the final
paragraph of `thm:prime`] need not be a canonical coefficient completion.
Injectivity of its coefficient embedding first identifies algebraic Frobenius
polynomials. The existing Chebotarev--Brauer--Nesbitt input then identifies the
semisimple actions at every completion. All coefficient labels and finite
exceptional sets are retained.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F A E : Type*} [Field F] [NumberField F] [Field A] [NumberField A]
  [NormedField E] {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] E]
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  {φ : AlgebraicGoodPrimeEigenform level μ A}
  {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- A local equivalence identifies an independently specified algebraic
Frobenius polynomial with the eigenform's Hecke polynomial. -/
theorem CohomologicalRealization.polynomial_eq_of_localComparison
    (r : CohomologicalRealization φ p E)
    (σ : Representation E (AbsoluteGalois F) V) (e : σ.Equiv r.action)
    (f : Polynomial A) (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (hf : (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      f.map r.coefficientEmbedding) :
    f = φ.heckePolynomial q hq := by
  apply Polynomial.map_injective r.coefficientEmbedding r.coefficientEmbedding.injective
  exact hf.symm.trans ((e.charpoly_eq _).trans (r.frobenius_charpoly q hq P hP hp Q))

/-- A compatible system identified with an eigenform over any supplied local
field agrees with that eigenform's system at every coefficient place. The
local compatibility premise uses the same algebraic polynomials and the exact
embedding belonging to the supplied cohomological realization. -/
theorem CohomologicalRealization.promote_localComparison
    (r : CohomologicalRealization φ p E)
    (S : NumberFieldCompatibleSystem F A) (T : EigenformCompatibleSystem φ)
    (σ : Representation E (AbsoluteGalois F) V) (e : σ.Equiv r.action)
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (S.polynomial q).map r.coefficientEmbedding)
    (w : HeightOneSpectrum (𝓞 A)) :
    Nonempty ((S.action w).Equiv (T.system.action w)) := by
  let bad := (S.badAt w ∪ T.system.badAt w) ∪ {q | (p : 𝓞 F) ∈ q.asIdeal}
  have hpfin : Set.Finite {q : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ q.asIdeal} := by
    apply HeightOneSpectrum.finite_primes_containing
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hbad : bad.Finite := ((S.badAt_finite w).union (T.system.badAt_finite w)).union hpfin
  have hgood (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ bad) :
      q ∉ S.bad ∧ q ∉ φ.form.bad ∧
      (S.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal ∧
      (T.system.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal ∧
      (p : 𝓞 F) ∉ q.asIdeal := by
    have hs : q ∉ S.badAt w := fun h => hq (Or.inl (Or.inl h))
    have ht : q ∉ T.system.badAt w := fun h => hq (Or.inl (Or.inr h))
    obtain ⟨hs, hsp⟩ := S.good_of_not_mem_badAt w q hs
    obtain ⟨ht, htp⟩ := T.system.good_of_not_mem_badAt w q ht
    exact ⟨hs, T.bad_eq ▸ ht, hsp, htp, fun h => hq (Or.inr h)⟩
  apply frobenius_semisimple_detection w (S.residueCharacteristic w)
    (S.residueCharacteristic_prime w) (S.coefficientPrime w)
    (S.action w) (T.system.action w) (S.continuous w) (T.system.continuous w)
    (S.semisimple w) (T.system.semisimple w) bad hbad
  · intro q hq P _ hP hp Q _ _ g hg
    exact S.unramified w q (hgood q hq).1 P hP hp Q g hg
  · intro q hq P _ hP _ Q _ _ g hg
    obtain ⟨_, ht, _, htp, _⟩ := hgood q hq
    exact T.system.unramified w q (T.bad_eq ▸ ht) P hP (hP.symm ▸ htp) Q g hg
  · intro q hq P _ hP hp Q _ _
    obtain ⟨hs, ht, _, htp, hpp⟩ := hgood q hq
    have hf := r.polynomial_eq_of_localComparison σ e (S.polynomial q) q ht
      P hP (hP.symm ▸ hpp) Q (hlocal q hs P hP (hP.symm ▸ hpp) Q)
    rw [S.frobenius_charpoly w q hs P hP hp Q, hf]
    exact (T.frobenius_charpoly w q ht P hP (hP.symm ▸ htp) Q).symm

end HilbertModularity.HilbertModularForms
