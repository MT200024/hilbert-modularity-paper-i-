/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CompatibleSystemPromotion
public import HilbertModularity.RepresentationTheory.PromotionPowerTrace

/-! # Power traces after semisimple promotion

The promoted equivalence compares every Galois element, hence every power of
geometric Frobenius without retaining the coefficient characteristic of the
original comparison place in the final good-prime hypotheses. The conditional
input is the named Chebotarev–Brauer–Nesbitt detector in
`FrobeniusSemisimpleDetection`. See [TripathiGoswami, Lemma “Promotion from
one realization”].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- An actual one-place equivariance with one finite algebraic character
identifies every power trace at every coefficient completion. -/
theorem NumberFieldCompatibleSystem.powerTrace_of_promotedComparison
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (σ.action w₀)))
    (w : HeightOneSpectrum (𝓞 E))
    (g : HilbertModularForms.AbsoluteGalois F) (n : ℕ) :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        ((ρ.action w g) ^ n) =
      (χ.toMonoidHom g : w.adicCompletion E) ^ n *
        LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
          ((σ.action w g) ^ n) := by
  obtain ⟨e⟩ := ρ.promote_characterComparison σ χ w₀ e₀ w
  have hpoly : (ρ.action w g).charpoly =
      ((σ.action w).characterTwist (χ.local w) g).charpoly :=
    (e.charpoly_eq g).trans
      ((Representation.characterTwistTensorEquiv (σ.action w) (χ.local w)).charpoly_eq g)
  exact (linearMap_trace_pow_eq_of_charpoly_eq
    (Pi.basisFun (w.adicCompletion E) (Fin 2))
    (ρ.action w g) ((σ.action w).characterTwist (χ.local w) g) hpoly n).trans
      (σ.characterTwist_trace_pow χ w g n)

end HilbertModularity
