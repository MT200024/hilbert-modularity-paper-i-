/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.RMComparisonFiniteSpecialization
public import HilbertModularity.Hypergeometric.RMComparisonFinitePaths
public import HilbertModularity.RepresentationTheory.FiniteCharacterRamification
public import HilbertModularity.RepresentationTheory.FiniteCharacterAlgebraization

/-! # Algebraic comparison character for one pair of arithmetic families

A generic finite comparison character takes values in a finite number field
inside its local coefficient field. Ramification is checked at one rational
fibre: where both arithmetic actions are trivial on inertia, their scalar
quotient is trivial too. The resulting algebraic character is the same one
in the comparison at every rational fibre of these families. -/

public noncomputable section

open AlgebraicGeometry NumberField IsDedekindDomain

namespace HilbertModularity.Hypergeometric

/-- Algebraize a fixed finite generic comparison character using the two
arithmetic actions at one base fibre. The coefficient field retains the
specified embedding of `E₀`, and inclusion recovers exactly the original
local character. The same included algebraic character compares every fibre.
This is the finite ramification and specialization deduction in
[TripathiGoswamiRevised, Theorem RMgeneral, steps 4--5]. -/
theorem algebraic_comparison_character_at_all_punctured_fibers
    (K E₀ L : Type*) [Field K] [NumberField K]
    [Field E₀] [NumberField E₀]
    [Field L] [TopologicalSpace L] [T2Space L]
    (ι₀ : E₀ →+* L) (ξ₀ : ProjectiveLine.Parameter K)
    (F_RM F_eff : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    [Nontrivial (F_RM.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K)
        (ProjectiveLine.puncturedPoint K ξ₀)))]
    (ν : HilbertModularForms.AbsoluteGalois K →* Lˣ)
    (hνc : Continuous ν) (hνfin : (Set.range ν).Finite)
    (hgeneric : ((Representation.ofCharacter
      (ν.comp (puncturedArithmeticProjectionHom K ξ₀))).tprod
        (puncturedFiberMonodromy K ξ₀ F_RM)).Equiv
          (puncturedFiberMonodromy K ξ₀ F_eff))
    (badRM badEff : Set (HeightOneSpectrum (𝓞 K)))
    (hbadRM : badRM.Finite) (hbadEff : badEff.Finite)
    (hRM : ∀ q, q ∉ badRM →
      ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois K,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois K) →
              puncturedFiberArithmeticRepresentation K ξ₀ F_RM g = 1)
    (hEff : ∀ q, q ∉ badEff →
      ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois K,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois K) →
              puncturedFiberArithmeticRepresentation K ξ₀ F_eff g = 1) :
    letI : Algebra E₀ L := ι₀.toAlgebra
    let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
    letI : NumberField E :=
      RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
    ∃ χ : FiniteAlgebraicGaloisCharacter K E,
      χ.bad = badRM ∪ badEff ∧
      (Units.map E.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
      E.subtype.comp (algebraMap E₀ E) = ι₀ ∧
      ∀ ξ : ProjectiveLine.Parameter K,
        Nonempty (((Representation.ofCharacter
          ((Units.map E.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
            (puncturedFiberArithmeticRepresentation K ξ F_RM)).Equiv
              (puncturedFiberArithmeticRepresentation K ξ F_eff)) := by
  dsimp only
  let : Algebra E₀ L := ι₀.toAlgebra
  let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
  let : NumberField E :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
  let ρRM := puncturedFiberArithmeticRepresentation K ξ₀ F_RM
  let ρEff := puncturedFiberArithmeticRepresentation K ξ₀ F_eff
  let e₀ := puncturedComparisonAllFibers K ξ₀ F_RM F_eff ν hgeneric ξ₀
  let eScalar : ρEff.Equiv (ρRM.characterTwist ν) :=
    e₀.symm.trans (Representation.characterTwistTensorEquiv ρRM ν)
  let χ : FiniteAlgebraicGaloisCharacter K E :=
    finiteAlgebraicGaloisCharacterOfComparison ι₀ ρEff ρRM ν eScalar
      hνfin hνc badEff badRM hbadEff hbadRM hEff hRM
  have hinclusion : (Units.map E.subtype.toMonoidHom).comp χ.toMonoidHom = ν := by
    exact finiteAlgebraicGaloisCharacterOfComparison_inclusion
      ι₀ ρEff ρRM ν eScalar hνfin hνc
      badEff badRM hbadEff hbadRM hEff hRM
  have hground : E.subtype.comp (algebraMap E₀ E) = ι₀ :=
    finiteAlgebraicGaloisCharacterOfLocal_groundEmbedding ι₀ ν
  refine ⟨χ, ?_, hinclusion, hground, ?_⟩
  · calc
      χ.bad = badEff ∪ badRM :=
        finiteAlgebraicGaloisCharacterOfComparison_bad
          ι₀ ρEff ρRM ν eScalar hνfin hνc
          badEff badRM hbadEff hbadRM hEff hRM
      _ = badRM ∪ badEff := Set.union_comm badEff badRM
  · intro ξ
    have hξ := (finite_comparison_character_at_all_punctured_fibers
      K ξ₀ F_RM F_eff ν hνc hνfin hgeneric).2.2 ξ
    rw [hinclusion]
    exact hξ

/-- Algebraize the finite comparison using finite ramification of the character
itself [MilneFT, Theorem 7.13; MilneANT, Remark 3.39(b)]. No ramification
hypothesis on either family is needed. The character and coefficient embedding
are unchanged at every fibre. -/
theorem algebraic_comparison_character_of_finite_image
    (K E₀ L : Type*) [Field K] [NumberField K]
    [Field E₀] [NumberField E₀]
    [Field L] [TopologicalSpace L] [T2Space L]
    (ι₀ : E₀ →+* L) (ξ₀ : ProjectiveLine.Parameter K)
    (F_RM F_eff : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    (ν : HilbertModularForms.AbsoluteGalois K →* Lˣ)
    (hνc : Continuous ν) (hνfin : (Set.range ν).Finite)
    (hgeneric : ((Representation.ofCharacter
      (ν.comp (puncturedArithmeticProjectionHom K ξ₀))).tprod
        (puncturedFiberMonodromy K ξ₀ F_RM)).Equiv
          (puncturedFiberMonodromy K ξ₀ F_eff))
    : letI : Algebra E₀ L := ι₀.toAlgebra
    let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
    letI : NumberField E :=
      RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
    ∃ χ : FiniteAlgebraicGaloisCharacter K E,
      (Units.map E.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
      E.subtype.comp (algebraMap E₀ E) = ι₀ ∧
      ∀ ξ : ProjectiveLine.Parameter K,
        Nonempty (((Representation.ofCharacter
          ((Units.map E.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
            (puncturedFiberArithmeticRepresentation K ξ F_RM)).Equiv
              (puncturedFiberArithmeticRepresentation K ξ F_eff)) := by
  dsimp only
  let : Algebra E₀ L := ι₀.toAlgebra
  let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
  let : NumberField E :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
  obtain ⟨bad, hbad, hunram⟩ := finiteCharacter_unramifiedOutsideFinite ν hνc hνfin
  let χ : FiniteAlgebraicGaloisCharacter K E :=
    finiteAlgebraicGaloisCharacterOfLocal ι₀ ν hνfin hνc bad hbad hunram
  have hinclusion : (Units.map E.subtype.toMonoidHom).comp χ.toMonoidHom = ν :=
    finiteAlgebraicGaloisCharacterOfLocal_inclusion ι₀ ν hνfin hνc bad hbad hunram
  refine ⟨χ, hinclusion, finiteAlgebraicGaloisCharacterOfLocal_groundEmbedding ι₀ ν, ?_⟩
  intro ξ
  rw [hinclusion]
  exact (finite_comparison_character_at_all_punctured_fibers
    K ξ₀ F_RM F_eff ν hνc hνfin hgeneric).2.2 ξ

end HilbertModularity.Hypergeometric
