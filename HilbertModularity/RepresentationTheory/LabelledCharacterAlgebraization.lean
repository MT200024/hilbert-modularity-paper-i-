/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ZeroWeightCharacterAlgebraization
public import HilbertModularity.RepresentationTheory.HodgeTateInjectivity

/-! # Finite algebraization from labelled Hodge–Tate weights

This applies the actual local-field-labelled comparison to the global character
of [TripathiGoswami, Lemma `lem:rankonezero`]. Bijectivity of the Hodge–Tate
comparison and vanishing at every nonzero labelled weight give spanning fixed
periods; the finite-inertia and class-field arguments then construct the finite
algebraic Hecke realization. Neither total reality nor purity is needed for
this stronger Hodge–Tate formulation. The separate standard implication from
de Rham to Hodge–Tate is not encoded as a new predicate or assumed conclusion.
-/

public noncomputable section

open NumberField IsDedekindDomain
open NumberField.LocalGalois

attribute [local instance] completionPadicAlgebra completionPadicTower

namespace NumberField.LocalGalois

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F]
  (q : HeightOneSpectrum (𝓞 F)) [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]

/-- The actual completion embeds in `Cp` through the chosen algebraic closure. -/
@[instance_reducible] def completionComplexAlgebra : Algebra (q.adicCompletion F) ℂ_[p] :=
  ((algebraMap (PadicAlgCl p) ℂ_[p]).comp
    (algebraMap (q.adicCompletion F) (PadicAlgCl p))).toAlgebra

attribute [local instance] completionComplexAlgebra

/-- The completion's `Cp` embedding factors through the chosen algebraic closure. -/
theorem completionComplexTower :
    @IsScalarTower (q.adicCompletion F) (PadicAlgCl p) ℂ_[p]
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] completionComplexTower

/-- The chosen `Cp` embedding preserves rational p-adic scalars. -/
theorem completionComplexRationalTower :
    @IsScalarTower ℚ_[p] (q.adicCompletion F) ℂ_[p]
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap ℚ_[p] ℂ_[p] a =
    algebraMap (PadicAlgCl p) ℂ_[p] (algebraMap (q.adicCompletion F)
      (PadicAlgCl p) (algebraMap ℚ_[p] (q.adicCompletion F) a))
  rw [← IsScalarTower.algebraMap_apply ℚ_[p] (q.adicCompletion F) (PadicAlgCl p),
    ← IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]

end NumberField.LocalGalois

attribute [local instance] completionComplexAlgebra completionComplexTower
  completionComplexRationalTower

namespace HilbertModularity

variable (ell : ℕ) [Fact ell.Prime]
  {F E₀ L : Type} [Field F] [NumberField F]
  [Field E₀] [NumberField E₀]
  [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra ℚ_[ell] L] [ContinuousSMul ℚ_[ell] L] [FiniteDimensional ℚ_[ell] L]

/-- A finitely ramified continuous character that is Hodge–Tate with only
weight zero at every local-field label has a finite algebraic Hecke realization.
The coefficient extension is constructed inside the original local field and
preserves the initial embedding. The comparison is the actual completed period
map, and labels range over embeddings of the actual completion into the
algebraic closure of the coefficient field. -/
theorem exists_finiteAlgebraicCharacter_of_labelledHodgeTate
    (ι₀ : E₀ →+* L)
    (χ : HilbertModularForms.AbsoluteGalois F →* Lˣ) (hc : Continuous χ)
    (bad : Finset (HeightOneSpectrum (𝓞 F)))
    (hunram : ∀ (q : HeightOneSpectrum (𝓞 F))
      (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal →
      ∀ g : HilbertModularForms.AbsoluteGalois F,
        g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad → χ g = 1)
    (hHT : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(ell : ℤ)})],
      Function.Bijective (HodgeTate.comparison ell
        (AlgEquiv.restrictScalarsHom ℚ_[ell])
        (PadicComplex.localGalois_fixes_base ell (K := q.adicCompletion F))
        ((Representation.ofCharacter (χ.comp (localGaloisRestriction ell F q))).restrictScalars
          ℚ_[ell])))
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
  apply exists_finiteAlgebraicCharacter_of_zeroWeightPeriods ell ι₀ χ hc bad hunram
  intro q hq
  apply HodgeTate.zeroWeightSpan_eq_top_of_surjective_comparison ell
    (AlgEquiv.restrictScalarsHom ℚ_[ell])
    (PadicComplex.localGalois_fixes_base ell (K := q.adicCompletion F)) _ (hHT q).2
  exact (HodgeTate.all_labelled_weights_zero_iff ell
    (AlgEquiv.restrictScalarsHom ℚ_[ell])
    (PadicComplex.localGalois_fixes_base ell (K := q.adicCompletion F)) _).mp (hweights q)

/-- Zero labelled weights give a single positive exponent killing every value.
This is the finite-order conclusion needed for the normalized determinant in
[TripathiGoswami, Proposition `prop:gprv` and Theorem RMgeneral]. -/
theorem finite_order_of_labelledHodgeTate
    (ι₀ : E₀ →+* L)
    (χ : HilbertModularForms.AbsoluteGalois F →* Lˣ) (hc : Continuous χ)
    (bad : Finset (HeightOneSpectrum (𝓞 F)))
    (hunram : ∀ (q : HeightOneSpectrum (𝓞 F))
      (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal →
      ∀ g : HilbertModularForms.AbsoluteGalois F,
        g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad → χ g = 1)
    (hHT : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(ell : ℤ)})],
      Function.Bijective (HodgeTate.comparison ell
        (AlgEquiv.restrictScalarsHom ℚ_[ell])
        (PadicComplex.localGalois_fixes_base ell (K := q.adicCompletion F))
        ((Representation.ofCharacter (χ.comp (localGaloisRestriction ell F q))).restrictScalars
          ℚ_[ell])))
    (hweights : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(ell : ℤ)})],
      ∀ τ : q.adicCompletion F →ₐ[ℚ_[ell]] AlgebraicClosure L,
      ∀ n : ℤ, n ≠ 0 → HodgeTate.labelledWeightSpace ell
        (AlgEquiv.restrictScalarsHom ℚ_[ell])
        (PadicComplex.localGalois_fixes_base ell (K := q.adicCompletion F))
        (Representation.ofCharacter (χ.comp (localGaloisRestriction ell F q))) n τ = ⊥) :
    ∃ n : ℕ, 0 < n ∧ ∀ g, χ g ^ n = 1 := by
  obtain ⟨E, _, hE, η, hη, _⟩ :=
    exists_finiteAlgebraicCharacter_of_labelledHodgeTate ell
      ι₀ χ hc bad hunram hHT hweights
  have hfin : (Set.range χ).Finite := by
    rw [← hη, MonoidHom.coe_comp, Set.range_comp]
    exact η.finite_range.image _
  let : Finite χ.range := hfin.to_subtype
  refine ⟨Nat.card χ.range, Nat.card_pos, fun g => ?_⟩
  have h : χ.rangeRestrict g ^ Nat.card χ.range = 1 := pow_card_eq_one'
  exact congrArg Subtype.val h

end HilbertModularity
