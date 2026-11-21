/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacteristicPolynomialDescent
public import HilbertModularity.RepresentationTheory.CompatibleSystemPromotion

/-! # Promotion after a coefficient extension at one place

A comparison obtained over a larger local coefficient field first descends to
equality of characteristic polynomials over the canonical coefficient
completion. Frobenius detection recovers the equivalence at that completion;
the ordinary compatible-system promotion then applies at every place.
The extension and its algebra structure are explicit inputs.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- An equivalence after a specified scalar extension of the initial
coefficient completion suffices to promote one finite algebraic character
comparison to all canonical completions. Both invocations of semisimple
Frobenius detection depend on [MilneAV, Chapter IV, §3, Lemmas 3.8–3.9]. -/
theorem NumberFieldCompatibleSystem.promote_baseChanged_characterComparison
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (L : Type*) [Field L] [Algebra (w₀.adicCompletion E) L]
    (e : ((ρ.action w₀).baseChange L).Equiv
      (((Representation.ofCharacter (χ.local w₀)).tprod (σ.action w₀)).baseChange L))
    (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((ρ.action w).Equiv
      ((Representation.ofCharacter (χ.local w)).tprod (σ.action w))) := by
  let bad := ρ.characterComparisonBad σ χ w₀ w₀
  have hρu : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (ρ.residueCharacteristic w₀ : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : HilbertModularForms.AbsoluteGalois F,
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ρ.action w₀ g = 1 := by
    intro q hq P _ hP _ Q _ _ g hg
    obtain ⟨hρ, _, _, _, _, hpρ, _⟩ :=
      ρ.good_of_not_mem_characterComparisonBad σ χ w₀ w₀ q hq
    exact ρ.unramified w₀ q hρ P hP (hP.symm ▸ hpρ) Q g hg
  have hσu : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (ρ.residueCharacteristic w₀ : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : HilbertModularForms.AbsoluteGalois F,
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) →
            (σ.action w₀).characterTwist (χ.local w₀) g = 1 := by
    intro q hq P _ hP _ Q _ _ g hg
    exact ρ.characterTwist_unramified_of_comparisonGood σ χ w₀ w₀
      q hq P hP Q g hg
  have hpoly : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (ρ.residueCharacteristic w₀ : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (ρ.action w₀
          (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          ((σ.action w₀).characterTwist (χ.local w₀)
            (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly := by
    intro q hq P _ hP _ Q _ _
    let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
    exact (e.charpoly_eq_of_baseChange g).trans
      ((Representation.characterTwistTensorEquiv (σ.action w₀) (χ.local w₀)).charpoly_eq g)
  obtain ⟨e₀⟩ := frobenius_semisimple_detection w₀
    (ρ.residueCharacteristic w₀) (ρ.residueCharacteristic_prime w₀)
    (ρ.coefficientPrime w₀) (ρ.action w₀)
    ((σ.action w₀).characterTwist (χ.local w₀))
    (ρ.continuous w₀) (σ.characterTwist_continuous χ w₀)
    (ρ.semisimple w₀) (σ.characterTwist_semisimple χ w₀)
    bad (ρ.characterComparisonBad_finite σ χ w₀ w₀) hρu hσu hpoly
  let e₀' : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (σ.action w₀)) :=
    e₀.trans (Representation.characterTwistTensorEquiv (σ.action w₀) (χ.local w₀)).symm
  exact ρ.promote_characterComparison σ χ w₀ e₀' w

end HilbertModularity
