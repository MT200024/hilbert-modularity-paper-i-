/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteCharacterCoefficientField
public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter
public import HilbertModularity.RepresentationTheory.CharacterTwistInertia

/-! # Algebraizing a finite local comparison character

A finite-image local character takes values in a finite number-field extension
inside its local coefficient field. An explicit finite ramification premise, or
triviality deduced from a comparison of unramified actions, turns its
corestriction into one algebraic Galois character. -/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F E₀ L : Type*} [Field F] [NumberField F]
  [Field E₀] [NumberField E₀] [Field L] [TopologicalSpace L] [T2Space L]

/-- Package a continuous finite-image local character with an explicitly
supplied finite ramification set. The coefficient number field is generated
inside `L`, retaining the original embedding of `E₀`. -/
def finiteAlgebraicGaloisCharacterOfLocal
    (ι₀ : E₀ →+* L)
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ)
    (hν : (Set.range ν).Finite) (hc : Continuous ν)
    (bad : Set (HeightOneSpectrum (𝓞 F))) (hbad : bad.Finite)
    (hunram : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ν g = 1) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
    letI : NumberField E :=
      RepresentationTheory.numberField_finiteCharacterCoefficientField ν hν
    FiniteAlgebraicGaloisCharacter F E := by
  letI : Algebra E₀ L := ι₀.toAlgebra
  let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
  letI : NumberField E :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hν
  let η := RepresentationTheory.finiteCharacterCorestrict (E₀ := E₀) ν
  refine {
    toMonoidHom := η
    finite_range := RepresentationTheory.finiteCharacterCorestrict_finite_range ν hν
    local_continuous := ?_
    bad := bad
    bad_finite := hbad
    unramified := ?_
  }
  · intro w
    exact Units.continuous_val.comp
      (RepresentationTheory.finiteCharacterRealization_continuous
        (E₀ := E₀) ν hν hc (algebraMap E (w.adicCompletion E)))
  · intro q hq P instP hP Q instQ instOver g hg
    have hinj : Function.Injective (Units.map E.subtype.toMonoidHom) :=
      Units.map_injective (fun _ _ h => Subtype.ext h)
    apply hinj
    have hmap := congrArg (fun χ : HilbertModularForms.AbsoluteGalois F →* Lˣ => χ g)
      (RepresentationTheory.finiteCharacterCorestrict_map (E₀ := E₀) ν)
    simpa [hunram q hq P hP Q g hg] using hmap

/-- The local character is recovered by inclusion of its generated coefficient
number field into the originally given local coefficient field. -/
theorem finiteAlgebraicGaloisCharacterOfLocal_inclusion
    (ι₀ : E₀ →+* L)
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ)
    (hν : (Set.range ν).Finite) (hc : Continuous ν)
    (bad : Set (HeightOneSpectrum (𝓞 F))) (hbad : bad.Finite)
    (hunram : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ν g = 1) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
    letI : NumberField E :=
      RepresentationTheory.numberField_finiteCharacterCoefficientField ν hν
    (Units.map E.subtype.toMonoidHom).comp
      (finiteAlgebraicGaloisCharacterOfLocal ι₀ ν hν hc bad hbad hunram).toMonoidHom = ν := by
  exact @RepresentationTheory.finiteCharacterCorestrict_map
    (HilbertModularForms.AbsoluteGalois F) E₀ L _ _ _ ι₀.toAlgebra ν

omit [NumberField F] [NumberField E₀] [TopologicalSpace L] [T2Space L] in
/-- The original coefficient embedding is the composite through the generated
number field, so the tower used for this algebraic character is fixed. -/
theorem finiteAlgebraicGaloisCharacterOfLocal_groundEmbedding
    (ι₀ : E₀ →+* L)
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
    E.subtype.comp (algebraMap E₀ E) = ι₀ := by
  exact @RepresentationTheory.finiteCharacterCoefficientField_subtype_comp_algebraMap
    (HilbertModularForms.AbsoluteGalois F) E₀ L _ _ _ ι₀.toAlgebra ν

variable {V W : Type*} [AddCommGroup V] [Module L V] [Nontrivial V]
  [AddCommGroup W] [Module L W]

omit [NumberField F] [TopologicalSpace L] [T2Space L] in
/-- If two equivalent actions are trivial on inertia outside respective bad
sets, their finite comparison character is trivial outside the union. The
nonzero representation hypothesis prevents a scalar from disappearing on the
zero module. -/
theorem comparisonCharacter_unramified_of_equiv
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois F) W)
    (σ : Representation L (HilbertModularForms.AbsoluteGalois F) V)
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ)
    (e : ρ.Equiv (σ.characterTwist ν))
    (badρ badσ : Set (HeightOneSpectrum (𝓞 F)))
    (hρ : ∀ q, q ∉ badρ →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ρ g = 1)
    (hσ : ∀ q, q ∉ badσ →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → σ g = 1) :
    ∀ q, q ∉ badρ ∪ badσ →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ν g = 1 := by
  intro q hq P instP hP Q instQ instOver g hg
  have hgood : q ∉ badρ ∧ q ∉ badσ := by simpa only [Set.mem_union, not_or] using hq
  exact Representation.character_eq_one_of_equiv_and_actions_eq_one ρ σ ν e g
    (hρ q hgood.1 P hP Q g hg) (hσ q hgood.2 P hP Q g hg)

/-- The bad sets of the two actions give the finite ramification premise for
the generated-field algebraic comparison character. -/
def finiteAlgebraicGaloisCharacterOfComparison
    (ι₀ : E₀ →+* L)
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois F) W)
    (σ : Representation L (HilbertModularForms.AbsoluteGalois F) V)
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ)
    (e : ρ.Equiv (σ.characterTwist ν))
    (hν : (Set.range ν).Finite) (hc : Continuous ν)
    (badρ badσ : Set (HeightOneSpectrum (𝓞 F)))
    (hbadρ : badρ.Finite) (hbadσ : badσ.Finite)
    (hρ : ∀ q, q ∉ badρ →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ρ g = 1)
    (hσ : ∀ q, q ∉ badσ →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → σ g = 1) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
    letI : NumberField E :=
      RepresentationTheory.numberField_finiteCharacterCoefficientField ν hν
    FiniteAlgebraicGaloisCharacter F E :=
  finiteAlgebraicGaloisCharacterOfLocal ι₀ ν hν hc (badρ ∪ badσ)
    (hbadρ.union hbadσ)
    (comparisonCharacter_unramified_of_equiv ρ σ ν e badρ badσ hρ hσ)

/-- The comparison construction uses exactly the union of the two supplied
finite ramification sets. -/
theorem finiteAlgebraicGaloisCharacterOfComparison_bad
    (ι₀ : E₀ →+* L)
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois F) W)
    (σ : Representation L (HilbertModularForms.AbsoluteGalois F) V)
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ)
    (e : ρ.Equiv (σ.characterTwist ν))
    (hν : (Set.range ν).Finite) (hc : Continuous ν)
    (badρ badσ : Set (HeightOneSpectrum (𝓞 F)))
    (hbadρ : badρ.Finite) (hbadσ : badσ.Finite)
    (hρ : ∀ q, q ∉ badρ →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ρ g = 1)
    (hσ : ∀ q, q ∉ badσ →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → σ g = 1) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
    letI : NumberField E :=
      RepresentationTheory.numberField_finiteCharacterCoefficientField ν hν
    (finiteAlgebraicGaloisCharacterOfComparison ι₀ ρ σ ν e hν hc
      badρ badσ hbadρ hbadσ hρ hσ).bad = badρ ∪ badσ := by
  exact (rfl)

/-- Inclusion of the generated number field recovers the original local
comparison character exactly. -/
theorem finiteAlgebraicGaloisCharacterOfComparison_inclusion
    (ι₀ : E₀ →+* L)
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois F) W)
    (σ : Representation L (HilbertModularForms.AbsoluteGalois F) V)
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ)
    (e : ρ.Equiv (σ.characterTwist ν))
    (hν : (Set.range ν).Finite) (hc : Continuous ν)
    (badρ badσ : Set (HeightOneSpectrum (𝓞 F)))
    (hbadρ : badρ.Finite) (hbadσ : badσ.Finite)
    (hρ : ∀ q, q ∉ badρ →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ρ g = 1)
    (hσ : ∀ q, q ∉ badσ →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → σ g = 1) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
    letI : NumberField E :=
      RepresentationTheory.numberField_finiteCharacterCoefficientField ν hν
    (Units.map E.subtype.toMonoidHom).comp
      (finiteAlgebraicGaloisCharacterOfComparison ι₀ ρ σ ν e hν hc
        badρ badσ hbadρ hbadσ hρ hσ).toMonoidHom = ν := by
  exact finiteAlgebraicGaloisCharacterOfLocal_inclusion ι₀ ν hν hc
    (badρ ∪ badσ) (hbadρ.union hbadσ)
    (comparisonCharacter_unramified_of_equiv ρ σ ν e badρ badσ hρ hσ)

end HilbertModularity
