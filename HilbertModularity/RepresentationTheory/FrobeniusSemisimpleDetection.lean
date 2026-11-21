/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter

/-! # Frobenius detection of semisimple Galois representations

The named input below is the Chebotarev–Brauer–Nesbitt step of [MilneAV,
Chapter IV, §3, Lemma 3.8 and its proof on printed pp. 142–143; Lemma 3.9].
Milne states it over `ℚ_[ℓ]` and uses arithmetic Frobenius. The same proof
works over the finite extension `w.adicCompletion E`: replace `ℤ_[ℓ]` by its
valuation ring in the lattice and Nakayama argument, and apply Lemma 3.9 over
the characteristic-zero coefficient field. Equality at geometric Frobenius
gives equality at its inverse, the arithmetic Frobenius, since the matrices are
invertible. The characteristic polynomial hypothesis is imposed away from a
finite set containing ramification and the coefficient characteristic.

This literature theorem remains an open `sorry` obligation. It detects two
independently supplied continuous semisimple representations; its conclusion
does not contain any compatible-system promotion or character comparison.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

/-- Chebotarev density and Brauer–Nesbitt identify continuous semisimple
representations from their good geometric-Frobenius polynomials. The explicitly
finite exceptional set and coefficient-characteristic exclusion are part of
the signature. This is the local-field form of [MilneAV, Chapter IV, §3,
Lemmas 3.8–3.9, printed pp. 142–143]. -/
theorem frobenius_semisimple_detection
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E))
    (p : ℕ) (hp : p.Prime)
    (hwp : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
    (ρ σ : Representation (w.adicCompletion E)
      (HilbertModularForms.AbsoluteGalois F) (Fin 2 → w.adicCompletion E))
    (hρc : ∀ i j : Fin 2, Continuous (fun g => ρ g (Pi.single j 1) i))
    (hσc : ∀ i j : Fin 2, Continuous (fun g => σ g (Pi.single j 1) i))
    (hρs : ρ.IsSemisimpleRepresentation)
    (hσs : σ.IsSemisimpleRepresentation)
    (bad : Set (HeightOneSpectrum (𝓞 F))) (hbad : bad.Finite)
    (hρu : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : HilbertModularForms.AbsoluteGalois F,
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ρ g = 1)
    (hσu : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : HilbertModularForms.AbsoluteGalois F,
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → σ g = 1)
    (hpoly : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (ρ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly) :
    Nonempty (ρ.Equiv σ) := by
  sorry

end HilbertModularity
