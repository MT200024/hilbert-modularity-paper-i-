/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.PromotionFiniteSet
public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTracePromotion

/-! # Hecke traces away from one finite exceptional set

For a fixed pair of coefficient places, the Hecke trace comparison holds away
from a finite geometric set. The eigenvalue is the one defined by the actual
adelic Hecke action of [TripathiGoswami, prime-level proof].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The finite set excludes ramification and both coefficient characteristics
at the original and target realizations. -/
theorem EigenformCompatibleSystem.heckeTrace_of_good
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (S : EigenformCompatibleSystem φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : AbsoluteGalois F →* Eˣ)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter
        ((Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom).comp χ)).tprod
          (S.system.action w₀)))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.comparisonBad S.system w₀ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      (χ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
        w.adicCompletion E) *
        algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q (by
          have h := ρ.good_of_not_mem_comparisonBad S.system w₀ w q hq
          rw [← S.bad_eq]
          exact h.2.1)) := by
  obtain ⟨hρ, hS, hpρ₀, hpS₀, hpρ, hpS⟩ :=
    ρ.good_of_not_mem_comparisonBad S.system w₀ w q hq
  have hφ : q ∉ φ.form.bad := S.bad_eq ▸ hS
  simpa only using S.heckeTrace_of_onePlace φ ρ χ w₀ w e q hρ hφ P hP
    (hP.symm ▸ hpρ₀) (hP.symm ▸ hpS₀)
    (hP.symm ▸ hpρ) (hP.symm ▸ hpS) Q

end HilbertModularity.HilbertModularForms
