/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CompatibleSystemPromotion

/-! # Comparing compatible systems outside additional finitely many primes

A one-place calculation may exclude its own residue characteristic. Such
finite exclusions do not affect the semisimple comparison at any target place.
This is the finite-exception step of [TripathiGoswamiRevised,
Lemma `lem:promotion`].
-/

public noncomputable section
open NumberField IsDedekindDomain

namespace HilbertModularity
variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- Equality of common polynomials outside any additional finite exceptional
set identifies the actual semisimple systems at every coefficient place. -/
theorem NumberFieldCompatibleSystem.equiv_of_polynomial_eq_outside
    (S T : NumberFieldCompatibleSystem F E)
    (extra : Set (HeightOneSpectrum (𝓞 F))) (hextra : extra.Finite)
    (hpoly : ∀ q, q ∉ S.bad → q ∉ T.bad → q ∉ extra →
      S.polynomial q = T.polynomial q)
    (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((S.action w).Equiv (T.action w)) := by
  let bad := (S.badAt w ∪ T.badAt w) ∪ extra
  have hgood (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ bad) :
      q ∉ S.bad ∧ q ∉ T.bad ∧
      (T.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal ∧ q ∉ extra := by
    obtain ⟨hs, _⟩ := S.good_of_not_mem_badAt w q (fun h => hq (Or.inl (Or.inl h)))
    obtain ⟨ht, htp⟩ := T.good_of_not_mem_badAt w q (fun h => hq (Or.inl (Or.inr h)))
    exact ⟨hs, ht, htp, fun h => hq (Or.inr h)⟩
  apply frobenius_semisimple_detection w (S.residueCharacteristic w)
    (S.residueCharacteristic_prime w) (S.coefficientPrime w)
    (S.action w) (T.action w) (S.continuous w) (T.continuous w)
    (S.semisimple w) (T.semisimple w) bad
    (((S.badAt_finite w).union (T.badAt_finite w)).union hextra)
  · intro q hq P _ hP hp Q _ _ g hg
    exact S.unramified w q (hgood q hq).1 P hP hp Q g hg
  · intro q hq P _ hP _ Q _ _ g hg
    obtain ⟨_, ht, htp, _⟩ := hgood q hq
    exact T.unramified w q ht P hP (hP.symm ▸ htp) Q g hg
  · intro q hq P _ hP hp Q _ _
    obtain ⟨hs, ht, htp, he⟩ := hgood q hq
    rw [S.frobenius_charpoly w q hs P hP hp Q, hpoly q hs ht he]
    exact (T.frobenius_charpoly w q ht P hP (hP.symm ▸ htp) Q).symm

end HilbertModularity
