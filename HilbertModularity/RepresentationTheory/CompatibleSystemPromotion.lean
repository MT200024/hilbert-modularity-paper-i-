/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FrobeniusSemisimpleDetection

/-! # Promotion of a one-place comparison

The one-place equivalence first identifies algebraic Frobenius polynomials by
injectivity of the coefficient embedding. The common polynomials and the same
finite-order algebraic character then give equality at every completion.
Outside one finite set containing both ramification sets, the character's
ramification set, and both coefficient characteristics, [MilneAV, Chapter IV,
§3, Lemmas 3.8–3.9] detects an equivalence of the semisimple representations.
This is the manuscript-specific argument of [TripathiGoswami, Lemma
“Promotion from one realization”].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- Equality of the algebraic polynomials at common good primes identifies
the two semisimple systems at every coefficient place. The exceptional set
includes both coefficient characteristics, which need not be chosen equally. -/
theorem NumberFieldCompatibleSystem.equiv_of_polynomial_eq
    (S T : NumberFieldCompatibleSystem F E)
    (hpoly : ∀ q, q ∉ S.bad → q ∉ T.bad → S.polynomial q = T.polynomial q)
    (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((S.action w).Equiv (T.action w)) := by
  let bad := S.badAt w ∪ T.badAt w
  have hgood (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ bad) :
      q ∉ S.bad ∧ q ∉ T.bad ∧
      (T.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal := by
    obtain ⟨hs, _⟩ := S.good_of_not_mem_badAt w q (fun h => hq (Or.inl h))
    obtain ⟨ht, htp⟩ := T.good_of_not_mem_badAt w q (fun h => hq (Or.inr h))
    exact ⟨hs, ht, htp⟩
  apply frobenius_semisimple_detection w (S.residueCharacteristic w)
    (S.residueCharacteristic_prime w) (S.coefficientPrime w)
    (S.action w) (T.action w) (S.continuous w) (T.continuous w)
    (S.semisimple w) (T.semisimple w) bad
    ((S.badAt_finite w).union (T.badAt_finite w))
  · intro q hq P _ hP hp Q _ _ g hg
    exact S.unramified w q (hgood q hq).1 P hP hp Q g hg
  · intro q hq P _ hP _ Q _ _ g hg
    obtain ⟨_, ht, htp⟩ := hgood q hq
    exact T.unramified w q ht P hP (hP.symm ▸ htp) Q g hg
  · intro q hq P _ hP hp Q _ _
    obtain ⟨hs, ht, htp⟩ := hgood q hq
    rw [S.frobenius_charpoly w q hs P hP hp Q, hpoly q hs ht]
    exact (T.frobenius_charpoly w q ht P hP (hP.symm ▸ htp) Q).symm

/-- A comparison at one completion of a common number field, by one
finite-order algebraic character, promotes to every completion. Both systems
are actual continuous semisimple rank-two Galois actions with common algebraic
geometric-Frobenius polynomials and finite ramification. The only literature
input in this proof is `frobenius_semisimple_detection`. -/
theorem NumberFieldCompatibleSystem.promote_characterComparison
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (σ.action w₀)))
    (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((ρ.action w).Equiv
      ((Representation.ofCharacter (χ.local w)).tprod (σ.action w))) := by
  let bad := ρ.characterComparisonBad σ χ w₀ w
  have hρu : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (ρ.residueCharacteristic w : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : HilbertModularForms.AbsoluteGalois F,
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ρ.action w g = 1 := by
    intro q hq P _ hP _ Q _ _ g hg
    obtain ⟨hρ, _, _, _, _, hpρ, _⟩ :=
      ρ.good_of_not_mem_characterComparisonBad σ χ w₀ w q hq
    exact ρ.unramified w q hρ P hP (hP.symm ▸ hpρ) Q g hg
  have hσu : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (ρ.residueCharacteristic w : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : HilbertModularForms.AbsoluteGalois F,
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) →
            (σ.action w).characterTwist (χ.local w) g = 1 := by
    intro q hq P _ hP _ Q _ _ g hg
    exact ρ.characterTwist_unramified_of_comparisonGood σ χ w₀ w
      q hq P hP Q g hg
  have hpoly : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (ρ.residueCharacteristic w : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          ((σ.action w).characterTwist (χ.local w)
            (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly := by
    intro q hq P _ hP _ Q _ _
    exact ρ.charpoly_characterTwist_eq_of_good σ χ w₀ w e₀ q hq P hP Q
  obtain ⟨e⟩ := frobenius_semisimple_detection w
    (ρ.residueCharacteristic w) (ρ.residueCharacteristic_prime w)
    (ρ.coefficientPrime w) (ρ.action w) ((σ.action w).characterTwist (χ.local w))
    (ρ.continuous w) (σ.characterTwist_continuous χ w)
    (ρ.semisimple w) (σ.characterTwist_semisimple χ w)
    bad (ρ.characterComparisonBad_finite σ χ w₀ w) hρu hσu hpoly
  exact ⟨e.trans (Representation.characterTwistTensorEquiv (σ.action w) (χ.local w)).symm⟩

end HilbertModularity
