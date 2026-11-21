/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.CoprimeEulerDarmonComparison
public import HilbertModularity.Hypergeometric.EffectiveEulerRealization

/-! # The generic arithmetic comparison for every coprime conductor

The raw Euler comparison character is multiplied by the single finite
κ_N^m character from [GPRV, Definition 8.8 and Lemma 9.4]. This gives the
manuscript's effective normalization, uniformly before all nonsingular fibres.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

/-- Scalar twisting a comparison multiplies its character. -/
private def tensorComparisonTwist
    {L G V W : Type*} [Field L] [Group G]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L G V) (σ : Representation L G W)
    (ν κ : G →* Lˣ)
    (e : ((Representation.ofCharacter ν).tprod ρ).Equiv σ) :
    ((Representation.ofCharacter (κ * ν)).tprod ρ).Equiv (σ.characterTwist κ) := by
  let eRaw := (Representation.characterTwistTensorEquiv ρ ν).symm.trans e
  apply Representation.characterTensorEquiv ρ (σ.characterTwist κ) (κ * ν)
    eRaw.toLinearEquiv
  intro g v
  have he := congrArg (fun f : V →ₗ[L] W => f v) (eRaw.isIntertwining' g)
  change eRaw ((ν g : L) • ρ g v) = σ g (eRaw v) at he
  change (κ g : L) • σ g (eRaw v) = ((κ * ν) g : L) • eRaw (ρ g v)
  rw [← he, map_smul]
  simp only [MonoidHom.mul_apply, Units.val_mul, mul_smul]

/-- The actual effective Euler realization and the fixed-labelled Darmon
cohomological family differ by one finite algebraic character, for every
coprime N≥3 and every coefficient prime, including two. No family comparison,
determinant, Hodge or ramification premise is supplied. This proves the
arithmetic deduction of [TripathiGoswamiRevised, Theorem `thm:RMgeneral`]
from the named realization and rigidity literature inputs. -/
theorem exists_algebraic_character_comparing_chosenEffectiveEuler
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [ContinuousSMul (w.adicCompletion (cyclotomicField N)) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion (cyclotomicField N)) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ ℚ_[p] L] :
    let E := cyclotomicField N
    let hE := realCyclotomicNormalClosure_le_full_of_neZero N
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField N) →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        let : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
          (algebraMap E (w.adicCompletion E))).toAlgebra
        let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
        let : NumberField E' :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField N) E',
          (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          E'.subtype.comp (algebraMap E E') = (algebraMap (w.adicCompletion E) L).comp
            (algebraMap E (w.adicCompletion E)) ∧
          ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
            Nonempty (((Representation.ofCharacter
              ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
                (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
                  (darmonCohomologicalFamily (realCyclotomicField N)
                    N h3 p m hcop E hE w L))).Equiv
                  (chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L
                    (coprimeEulerCoefficientMap N w L) ξ)) := by
  let K := realCyclotomicField N
  let E := cyclotomicField N
  let ι := coprimeEulerCoefficientMap N w L
  let ι₀ := (algebraMap (w.adicCompletion E) L).comp
    (algebraMap E (w.adicCompletion E))
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hmPos hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hmPos hmN hcop
  let D := R.placeDescent N m 𝒞 p L ι
  obtain ⟨ν, hνc, hνfin, χraw, hχraw, hground, hcompare⟩ :=
    exists_algebraic_character_comparing_chosenCoprimeRawEuler
      N m p h3 hmPos hmN hcop w L
  let κ := gprvKappaLocal N h3 m L
  let η := κ * ν
  have hηc : Continuous η := (continuous_gprvKappaLocal N h3 m L).mul hνc
  have hηfin : (Set.range η).Finite :=
    ((finite_gprvKappaLocal N h3 m L).mul hνfin).subset (by
      rintro _ ⟨g, rfl⟩
      exact Set.mul_mem_mul (Set.mem_range_self g) (Set.mem_range_self g))
  obtain ⟨bad, hbad, hunram⟩ :=
    finiteCharacter_unramifiedOutsideFinite η hηc hηfin
  let : Algebra E L := ι₀.toAlgebra
  let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) η
  let : NumberField E' :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField η hηfin
  let χ := finiteAlgebraicGaloisCharacterOfLocal ι₀ η hηfin hηc bad hbad hunram
  have hχ : (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = η :=
    finiteAlgebraicGaloisCharacterOfLocal_inclusion ι₀ η hηfin hηc bad hbad hunram
  refine ⟨η, hηc, hηfin, χ, hχ, ?_, ?_⟩
  · exact finiteAlgebraicGaloisCharacterOfLocal_groundEmbedding ι₀ η
  · intro ξ
    obtain ⟨e⟩ := hcompare ξ
    rw [hχraw] at e
    rw [hχ]
    have heff : chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι ξ =
        (puncturedFiberArithmeticRepresentation K ξ D.localSystem).characterTwist κ := by
      ext g v
      exact chosenEffectiveEulerAction_apply N m p h3 hmPos hmN hcop L ι ξ g v
    rw [heff]
    exact ⟨tensorComparisonTwist _ _ ν κ e⟩

end HilbertModularity.Hypergeometric
