/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.DeRhamComparison
public import HilbertModularity.RepresentationTheory.LabelledCharacterAlgebraization

/-! # Algebraization of de Rham characters with zero labelled weights

The de Rham premise refers to invariants of the actual Fontaine period ring.
The cited de Rham-to-Hodge--Tate comparison supplies the input to the existing
proved finite-inertia and global class-field argument. This proves the
rank-one deduction of [TripathiGoswamiRevised, Lemma `lem:rankonezero`].
The conclusion holds without its additional total-reality and purity hypotheses.
-/

public noncomputable section

open NumberField IsDedekindDomain
open NumberField.LocalGalois

attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

namespace HilbertModularity

variable (ell : ℕ) [Fact ell.Prime]
  {F E₀ L : Type} [Field F] [NumberField F]
  [Field E₀] [NumberField E₀]
  [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra ℚ_[ell] L] [ContinuousSMul ℚ_[ell] L] [FiniteDimensional ℚ_[ell] L]

/-- A finitely ramified continuous character, de Rham at every place over
`ell` and of weight zero at every local-field label, is the realization of
one finite algebraic Hecke character. Its coefficient number field is
constructed inside the original local field and retains the initial embedding. -/
theorem exists_finiteAlgebraicCharacter_of_deRham_zero_weights
    (ι₀ : E₀ →+* L)
    (χ : HilbertModularForms.AbsoluteGalois F →* Lˣ) (hc : Continuous χ)
    (bad : Finset (HeightOneSpectrum (𝓞 F)))
    (hunram : ∀ (q : HeightOneSpectrum (𝓞 F))
      (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal →
      ∀ g : HilbertModularForms.AbsoluteGalois F,
        g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad → χ g = 1)
    (hdeRham : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(ell : ℤ)})],
      DeRham.IsDeRham ell (q.adicCompletion F)
        ((Representation.ofCharacter (χ.comp (localGaloisRestriction ell F q))).restrictScalars
          ℚ_[ell]))
    (hweights : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(ell : ℤ)})],
      ∀ τ : q.adicCompletion F →ₐ[ℚ_[ell]] AlgebraicClosure L,
      ∀ n : ℤ, n ≠ 0 → HodgeTate.labelledWeightSpace ell
        (AlgEquiv.restrictScalarsHom ℚ_[ell])
        (PadicComplex.localGalois_fixes_base ell (K := q.adicCompletion F))
        (Representation.ofCharacter (χ.comp (localGaloisRestriction ell F q))) n τ = ⊥) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    ∃ E : IntermediateField E₀ L,
      E.subtype.comp (algebraMap E₀ E) = ι₀ ∧
      ∃ _ : NumberField E, ∃ η : FiniteAlgebraicGaloisCharacter F E,
        (Units.map E.subtype.toMonoidHom).comp η.toMonoidHom = χ ∧
        ∀ ι : E →+* ℂ,
          Nonempty (HilbertModularForms.ArithmeticIdeleRealization η ι) := by
  apply exists_finiteAlgebraicCharacter_of_labelledHodgeTate ell ι₀ χ hc bad hunram ?_ hweights
  intro q hq
  apply DeRham.comparison_bijective_of_isDeRham ell (q.adicCompletion F) L
    ((Representation.ofCharacter (χ.comp (localGaloisRestriction ell F q))).restrictScalars
      ℚ_[ell]) ?_ (hdeRham q)
  intro v
  change Continuous (fun g => (χ (localGaloisRestriction ell F q g) : L) * v)
  exact (Units.continuous_val.comp
    (hc.comp (continuous_localGaloisRestriction ell F q))).mul_const v

end HilbertModularity
