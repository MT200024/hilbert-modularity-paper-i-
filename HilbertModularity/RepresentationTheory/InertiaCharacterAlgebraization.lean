/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.UnramifiedAbelianQuotient
public import HilbertModularity.RepresentationTheory.FiniteCharacterAlgebraization
public import HilbertModularity.NumberTheory.HilbertModularForms.FiniteCharacterReciprocity

/-! # Algebraization from bounded finite inertia

This is the global finite-order step in [TripathiGoswami,
Lemma `lem:rankonezero`]. The local zero-weight comparison is kept explicit:
at each ramified prime a single positive exponent must kill all inertia images.
The proof then constructs the actual number-field-valued character and applies
the existing arithmetic-normalized finite-character reciprocity input.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F E₀ L : Type*} [Field F] [NumberField F]
  [Field E₀] [NumberField E₀] [Field L] [TopologicalSpace L]
  [IsTopologicalRing L] [T2Space L]

/-- A continuous finitely ramified character with bounded finite inertia is
realized by a finite algebraic character over a number field inside its given
coefficient field. The embedding of the original number field is preserved,
and every complex embedding gives an arithmetic-normalized finite Hecke
character by the existing reciprocity theorem. No global finite-image premise
is assumed. -/
theorem exists_finiteAlgebraicCharacter_of_inertia_exponents
    (ι₀ : E₀ →+* L)
    (χ : HilbertModularForms.AbsoluteGalois F →* Lˣ) (hc : Continuous χ)
    (bad : Finset (HeightOneSpectrum (𝓞 F)))
    (n : HeightOneSpectrum (𝓞 F) → ℕ) (hn : ∀ q ∈ bad, 0 < n q)
    (hi : ∀ (q : HeightOneSpectrum (𝓞 F))
      (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal →
      ∀ g : HilbertModularForms.AbsoluteGalois F,
        g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) →
        (q ∈ bad → χ g ^ n q = 1) ∧ (q ∉ bad → χ g = 1)) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    ∃ E : IntermediateField E₀ L,
      E.subtype.comp (algebraMap E₀ E) = ι₀ ∧
      ∃ _ : NumberField E, ∃ η : FiniteAlgebraicGaloisCharacter F E,
        (Units.map E.subtype.toMonoidHom).comp η.toMonoidHom = χ ∧
        ∀ ι : E →+* ℂ,
          Nonempty (HilbertModularForms.ArithmeticIdeleRealization η ι) := by
  classical
  obtain ⟨m, hm, hχ⟩ := finite_order_of_inertia_exponents χ hc bad n hn hi
  have hfin := finite_range_of_character_exponent χ hm hχ
  let : Algebra E₀ L := ι₀.toAlgebra
  let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) χ
  let : NumberField E :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField χ hfin
  have hunram : ∀ q, q ∉ (bad : Set (HeightOneSpectrum (𝓞 F))) →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → χ g = 1 := by
    intro q hq P instP hP Q instQ instOver g hg
    subst P
    exact (hi q Q instQ instOver g hg).2 hq
  let η := finiteAlgebraicGaloisCharacterOfLocal ι₀ χ hfin hc
    (bad : Set _) bad.finite_toSet hunram
  refine ⟨E, finiteAlgebraicGaloisCharacterOfLocal_groundEmbedding ι₀ χ,
    inferInstance, η, ?_, ?_⟩
  · exact finiteAlgebraicGaloisCharacterOfLocal_inclusion ι₀ χ hfin hc
      (bad : Set _) bad.finite_toSet hunram
  · exact fun ι => HilbertModularForms.nonempty_arithmeticIdeleRealization η ι

end HilbertModularity
