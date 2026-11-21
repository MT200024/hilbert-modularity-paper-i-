/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter
public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTraceFiniteSet

/-! # Hecke traces after a finite algebraic character twist

The same algebraic character is realized at every coefficient completion. The
trace identity is valid outside one finite set that also excludes the
character's ramification, as required for the promotion argument of
[TripathiGoswami, Lemma “Promotion from one realization”].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- A one-place equivalence identifies the actual geometric-Frobenius trace
at every completion with the independently defined Hecke eigenvalue times
the realization of one algebraic character. -/
theorem EigenformCompatibleSystem.heckeTrace_of_characterComparisonGood
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (S : EigenformCompatibleSystem φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (S.system.action w₀)))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.characterComparisonBad S.system χ w₀ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
          w.adicCompletion E) *
        algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q (by
          have h := ρ.good_of_not_mem_characterComparisonBad S.system χ w₀ w q hq
          rw [← S.bad_eq]
          exact h.2.1)) := by
  have hq' : q ∉ ρ.comparisonBad S.system w₀ w := by
    exact ρ.not_mem_comparisonBad_of_characterGood S.system χ w₀ w q hq
  exact S.heckeTrace_of_good φ ρ χ.toMonoidHom w₀ w
    (by simpa only [χ.local_eq_composition] using e)
    q hq' P hP Q

end HilbertModularity.HilbertModularForms
