/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CompatibleSystem

/-! # Hecke traces after one-place comparison

An equivariant comparison at one coefficient place identifies the algebraic
Frobenius polynomials. The resulting trace identity at any other place uses the
Hecke eigenvalue defined by the adelic Hecke action, with geometric Frobenius
and every residue-characteristic exclusion explicit. This is the trace step in
[TripathiGoswami, Lemma “Promotion from one realization”].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- A one-place character-twisted comparison with a fixed eigenform system
gives the geometric-Frobenius Hecke trace at every coefficient completion. -/
theorem EigenformCompatibleSystem.heckeTrace_of_onePlace
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (S : EigenformCompatibleSystem φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : AbsoluteGalois F →* Eˣ)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter
        ((Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom).comp χ)).tprod
          (S.system.action w₀)))
    (q : HeightOneSpectrum (𝓞 F)) (hρ : q ∉ ρ.bad)
    (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hpρ₀ : (ρ.residueCharacteristic w₀ : 𝓞 F) ∉ P)
    (hpS₀ : (S.system.residueCharacteristic w₀ : 𝓞 F) ∉ P)
    (hpρ : (ρ.residueCharacteristic w : 𝓞 F) ∉ P)
    (hpS : (S.system.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      (χ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
        w.adicCompletion E) *
        algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq) := by
  rw [ρ.frobenius_trace_characterTwist_eq_of_onePlace S.system χ w₀ w e q hρ
    (S.bad_eq ▸ hq) P hP hpρ₀ hpS₀ hpρ hpS Q,
    S.frobenius_trace w q hq P hP hpS Q]

end HilbertModularity.HilbertModularForms
