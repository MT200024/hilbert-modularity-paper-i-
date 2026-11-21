/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteExceptionalPrimes

/-! # Frobenius comparison outside a single finite set

The coefficient comparison of [TripathiGoswami, Lemma “Promotion from one
realization”] is applied after deleting one finite set of geometric primes.
Its complement simultaneously satisfies the ramification and residue
characteristic conditions at the original and target coefficient places.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- The one-place equivalence gives equality of actual Frobenius polynomials
at another completion outside the explicitly finite comparison set. -/
theorem NumberFieldCompatibleSystem.charpoly_characterTensor_eq_of_good
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : HilbertModularForms.AbsoluteGalois F →* Eˣ)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter
        ((Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom).comp χ)).tprod
          (σ.action w₀)))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ ρ.comparisonBad σ w₀ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      (((Representation.ofCharacter
        ((Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom).comp χ)).tprod
          (σ.action w))
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly := by
  obtain ⟨hρ, hσ, hpρ₀, hpσ₀, hpρ, hpσ⟩ :=
    ρ.good_of_not_mem_comparisonBad σ w₀ w q hq
  exact ρ.charpoly_characterTensor_eq_of_onePlace σ χ w₀ w e q hρ hσ P hP
    (hP.symm ▸ hpρ₀) (hP.symm ▸ hpσ₀)
    (hP.symm ▸ hpρ) (hP.symm ▸ hpσ) Q

end HilbertModularity
