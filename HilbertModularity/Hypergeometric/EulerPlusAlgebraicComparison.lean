/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerPlusCompatibleComparison
public import HilbertModularity.Hypergeometric.PrimePlusConductorSpectralCoordinates
public import HilbertModularity.Hypergeometric.EulerPlusCohomologicalCoordinates
public import HilbertModularity.RepresentationTheory.FiniteCharacterCoefficientField
public import HilbertModularity.NumberTheory.PrimeBelowComparison
public import HilbertModularity.Geometry.Etale.ParameterInvolution

/-! # One algebraic coefficient field for the selected Euler–plus comparison

The finite comparison character is chosen at one conductor completion before
specializing the family. Its values generate a number field containing the
cyclotomic coefficient field. The fixed exponent label extends to that field
and agrees with the original completed Darmon label.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic HilbertModularForms

/-- Every extension of the full cyclotomic field splits the real cyclotomic
coefficient polynomials. The fixed RM embedding can therefore be used in the
selected plus compatible system over that extension. -/
theorem realCyclotomic_minpoly_splits_in_cyclotomic_extension
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (A : Type) [Field A] [Algebra (cyclotomicField p) A]
    [Algebra ℚ A] [IsScalarTower ℚ (cyclotomicField p) A]
    (a : realCyclotomicField p) :
    ((minpoly ℚ a).map (algebraMap ℚ A)).Splits := by
  have hs := IntermediateField.splits_minpoly_of_normalClosure_le
    (realCyclotomicField p) (cyclotomicField p)
    (realCyclotomicNormalClosure_le_full p) a
  simpa only [Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq ℚ (cyclotomicField p) A] using
    hs.map (algebraMap (cyclotomicField p) A)

/-- The global exponent label, extended through a coefficient number field,
recovers the completed Darmon label at the chosen coefficient place. -/
theorem globalEulerPlusLabel_comp_localEmbedding
    (p m : ℕ) [NeZero p] (hm : m.Coprime p)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    (A : Type) [Field A] [Algebra E A] [Algebra ℚ A]
    [IsScalarTower ℚ E A]
    (L : Type) [Field L] [Algebra (w.adicCompletion E) L] [Algebra ℚ L]
    [IsScalarTower ℚ (w.adicCompletion E) L]
    (j : A →ₐ[ℚ] L)
    (hcoeff : j.toRingHom.comp (algebraMap E A) =
      (algebraMap (w.adicCompletion E) L).comp
        (algebraMap E (w.adicCompletion E))) :
    j.comp ((Algebra.algHom ℚ E A).comp
      (coefficientEmbedding p m hm E
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE))) =
      coefficientEmbeddingAbovePrime p m hm E
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
        w L := by
  ext a
  change j (algebraMap E A (coefficientEmbedding p m hm E
    ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE) a)) =
    algebraMap (w.adicCompletion E) L
      (algebraMap E (w.adicCompletion E) (coefficientEmbedding p m hm E
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE) a))
  exact congrArg (fun f : E →+* L =>
    f (coefficientEmbedding p m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE) a)) hcoeff

/-- The same-family cohomological coordinate equivalence converts the
algebraic Darmon comparison to the selected plus twist at one realization.
The finite character remains the one supplied by the generic comparison. -/
theorem eulerLocal_equiv_twistedPlus_of_darmonComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[p] L]
    (F : Scheme.EtaleLocalSystem (realCyclotomicField p)
      (ProjectiveLine.punctured (realCyclotomicField p)) L)
    (ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField p) →* Lˣ)
    (ec : Nonempty (((Representation.ofCharacter ν).tprod
      (puncturedFiberArithmeticRepresentation (realCyclotomicField p) ξ
        (darmonCohomologicalFamily (realCyclotomicField p) p
          (three_le_of_five_le hp) p m hm E hE w L))).Equiv
      (puncturedFiberArithmeticRepresentation (realCyclotomicField p) ξ F))) :
    Nonempty ((puncturedFiberArithmeticRepresentation (realCyclotomicField p)
      ξ F).Equiv
      ((primePlusCohomologicalAction p hp ξ p L
        (splits_minpoly_above_coefficientPrime p E w L hE)
        (coefficientEmbeddingAbovePrime p m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
          w L)).characterTwist ν)) := by
  obtain ⟨e⟩ := ec
  let ed := darmonPrimeCohomologicalEquivPlus p hp m hm ξ E hE w L
  exact ⟨e.symm.trans ((Representation.characterTensorEquivCongr ν ed).trans
    (Representation.characterTwistTensorEquiv _ ν))⟩

/-- All-place comparison of the actual chosen Euler compatible system with
one finite twist of the selected plus compatible system. The quantifier over
places includes primes above two. -/
def EulerPlusCompatibleAtAllPlaces
    (p m : ℕ) [NeZero p] [Fact p.Prime]
    (hN : p.Prime) (hp : 5 ≤ p) (hmPos : 0 < m) (hmLt : m < p)
    (A : Type) [Field A] [NumberField A] [Algebra (cyclotomicField p) A]
    (hA : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ A)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] A)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) A) : Prop :=
  ∀ (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (v : HeightOneSpectrum (𝓞 A)),
    Nonempty ((((chosenCommonEulerCompatibleSystem p m hN hp hmPos hmLt ξ
      ).extendCoefficients (L := A)).action v).Equiv
      (((primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ).action v))

/-- Transport the coefficient-prime typeclass data along the specified
prime-below equality before invoking the all-place polynomial bridge. -/
private theorem promote_eulerPlusComparison_at_specifiedPrime
    (N m ℓ : ℕ) [NeZero N] [Fact N.Prime] [Fact ℓ.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (A : Type) [Field A] [NumberField A] [Algebra (cyclotomicField N) A]
    (hA : ∀ a : realCyclotomicField N,
      ((minpoly ℚ a).map (algebraMap ℚ A)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] A)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField N) A)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [w.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[ℓ] L] [FiniteDimensional ℚ_[ℓ] L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ_[ℓ] (w.adicCompletion (cyclotomicField N)) L]
    [Algebra ℚ L] [IsScalarTower ℚ ℚ_[ℓ] L]
    (j : A →ₐ[ℚ] L)
    (hcoeff : j.toRingHom.comp (algebraMap (cyclotomicField N) A) =
      (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
        (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))))
    (hL : ∀ a : realCyclotomicField N,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (e : let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hmPos hmN
      let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hmPos hmN
      let ι := j.toRingHom.comp (algebraMap (cyclotomicField N) A)
      ((R.placeDescent N m 𝒞 ℓ L ι).localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)).Equiv
        ((primePlusCohomologicalAction N h5 ξ ℓ L hL (j.comp σ)).characterTwist
          ((Units.map j.toRingHom.toMonoidHom).comp χ.toMonoidHom)))
    (hbelow : NumberField.primeBelow (cyclotomicField N) w = ℓ)
    (v : HeightOneSpectrum (𝓞 A)) :
    Nonempty ((((chosenCommonEulerCompatibleSystem N m hN h5 hmPos hmN ξ
      ).extendCoefficients (L := A)).action v).Equiv
      (((primePlusCompatibleSystem N h5 ξ A hA σ).characterTwist χ).action v)) := by
  subst ℓ
  exact chosenEuler_equiv_twistedPlus_at_all_places_of_localComparison
    N m hN h5 hmPos hmN ξ A hA σ χ w L j hcoeff hL e v

/-- Apply the actual same-family Darmon coordinate comparison at one fibre,
then use compatible polynomials to reach an arbitrary target place. -/
private theorem chosenEuler_twistedPlus_at_place_of_darmonComparison
    (p m : ℕ) [NeZero p] [Fact p.Prime]
    (hN : p.Prime) (hp : 5 ≤ p) (hmPos : 0 < m) (hmLt : m < p)
    (hm : m.Coprime p)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField p)))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion (cyclotomicField p)) L]
    [ContinuousSMul (w.adicCompletion (cyclotomicField p)) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion (cyclotomicField p)) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField p)) L]
    [IsScalarTower ℚ ℚ_[p] L]
    (A : Type) [Field A] [NumberField A] [Algebra (cyclotomicField p) A]
    (hA : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ A)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] A)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) A)
    (j : A →ₐ[ℚ] L)
    (hcoeff : j.toRingHom.comp (algebraMap (cyclotomicField p) A) =
      (algebraMap (w.adicCompletion (cyclotomicField p)) L).comp
        (algebraMap (cyclotomicField p)
          (w.adicCompletion (cyclotomicField p))))
    (hσ : j.comp σ =
      coefficientEmbeddingAbovePrime p m hm (cyclotomicField p)
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans
          (realCyclotomicNormalClosure_le_full p)) w L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ec : let 𝒞 := chosenSmoothProperEulerFamily p m hN hp hmPos hmLt
      let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN hp hmPos hmLt
      let ι := j.toRingHom.comp (algebraMap (cyclotomicField p) A)
      Nonempty (((Representation.ofCharacter
        ((Units.map j.toRingHom.toMonoidHom).comp χ.toMonoidHom)).tprod
        (puncturedFiberArithmeticRepresentation (realCyclotomicField p) ξ
          (darmonCohomologicalFamily (realCyclotomicField p) p
            (three_le_of_five_le hp) p m hm (cyclotomicField p)
            (realCyclotomicNormalClosure_le_full p) w L))).Equiv
        (puncturedFiberArithmeticRepresentation (realCyclotomicField p) ξ
          (R.placeDescent p m 𝒞 p L ι).localSystem)))
    (v : HeightOneSpectrum (𝓞 A)) :
    Nonempty ((((chosenCommonEulerCompatibleSystem p m hN hp hmPos hmLt ξ
      ).extendCoefficients (L := A)).action v).Equiv
      (((primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ).action v)) := by
  let E := cyclotomicField p
  let hE := realCyclotomicNormalClosure_le_full p
  let 𝒞 := chosenSmoothProperEulerFamily p m hN hp hmPos hmLt
  let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN hp hmPos hmLt
  let ι := j.toRingHom.comp (algebraMap E A)
  let χL := (Units.map j.toRingHom.toMonoidHom).comp χ.toMonoidHom
  let hL := splits_minpoly_above_coefficientPrime p E w L hE
  have eLocal :
      ((R.placeDescent p m 𝒞 p L ι).localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).Equiv
        ((primePlusCohomologicalAction p hp ξ p L hL
          (coefficientEmbeddingAbovePrime p m hm E
            ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
            w L)).characterTwist χL) := by
    exact (eulerLocal_equiv_twistedPlus_of_darmonComparison
      p hp m hm ξ E hE w L (R.placeDescent p m 𝒞 p L ι).localSystem χL ec).some
  have hbelow : NumberField.primeBelow E w = p :=
    NumberField.primeBelow_eq_of_liesOver E w p
  have eBridge :
      let 𝒞 := chosenSmoothProperEulerFamily p m hN hp hmPos hmLt
      let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN hp hmPos hmLt
      let ι := j.toRingHom.comp (algebraMap E A)
      ((R.placeDescent p m 𝒞 p L ι).localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)).Equiv
          ((primePlusCohomologicalAction p hp ξ p L hL (j.comp σ)).characterTwist χL) := by
    have hAction := congrArg (fun s : realCyclotomicField p →ₐ[ℚ] L =>
      primePlusCohomologicalAction p hp ξ p L hL s) hσ
    exact hAction.symm ▸ eLocal
  exact promote_eulerPlusComparison_at_specifiedPrime
    p m p hN hp hmPos hmLt ξ A hA σ χ w L j hcoeff hL eBridge hbelow v


section ChosenConductor

variable (p : ℕ) [Fact p.Prime]

/-- One finite algebraic character and one fixed coefficient label identify
all nonsingular chosen Euler fibres with the twist of the selected plus
compatible system at every coefficient place, including dyadic places.
This is the selected prime-conductor application of
[TripathiGoswamiRevised, Theorem `thm:RMgeneral`]. -/
theorem exists_chosenEuler_twistedPlus_at_all_places
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField p)))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion (cyclotomicField p)) L]
    [ContinuousSMul (w.adicCompletion (cyclotomicField p)) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion (cyclotomicField p)) L]
    [Algebra ℚ L]
    [IsScalarTower ℚ (w.adicCompletion (cyclotomicField p)) L]
    [IsScalarTower ℚ ℚ_[p] L]
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    let E := cyclotomicField p
    let : Algebra E L :=
      ((algebraMap (w.adicCompletion E) L).comp
        (algebraMap E (w.adicCompletion E))).toAlgebra
    ∃ ν : AbsoluteGalois (realCyclotomicField p) →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        let A := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
        let : NumberField A :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ (σ : realCyclotomicField p →ₐ[ℚ] A)
          (hA : ∀ a : realCyclotomicField p,
            ((minpoly ℚ a).map (algebraMap ℚ A)).Splits)
          (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) A),
          σ = (Algebra.algHom ℚ E A).comp
            (coefficientEmbedding p m
              (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt) E
              ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans
                (realCyclotomicNormalClosure_le_full p))) ∧
          (Units.map A.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          EulerPlusCompatibleAtAllPlaces p m (Fact.out : p.Prime)
            hp hmPos hmLt A hA σ χ := by
  let E := cyclotomicField p
  let hN : p.Prime := Fact.out
  let hm := eulerExponent_coprime_of_prime p m hN hmPos hmLt
  let hE := realCyclotomicNormalClosure_le_full p
  let : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
    (algebraMap E (w.adicCompletion E))).toAlgebra
  let ι : E →+* L := algebraMap E L
  have hι : coefficientEmbeddingAbovePrime p m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
      w L (tau p 1) = ι ((root p) ^ m + (root p)⁻¹ ^ m) := by
    rw [coefficientEmbeddingAbovePrime_tau_one]
    have hv : IntermediateField.inclusion
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
        (tau p m) = (root p) ^ m + (root p)⁻¹ ^ m := by
      apply Subtype.ext
      rfl
    rw [hv]
    rfl
  obtain ⟨ν, hν, hνfin, χ, hχ, hcoeff, hcomparison⟩ :=
    exists_algebraic_character_comparing_chosenEuler_realization
      p m hN hp hmPos hmLt E hE w L ι hι ξ₀
  let A := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
  let : NumberField A :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
  let σ : realCyclotomicField p →ₐ[ℚ] A :=
    (Algebra.algHom ℚ E A).comp (coefficientEmbedding p m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE))
  let j : A →ₐ[ℚ] L := {
    toRingHom := A.subtype
    commutes' := by
      intro q
      simp
  }
  have hcoeff' : j.toRingHom.comp (algebraMap E A) =
      (algebraMap (w.adicCompletion E) L).comp
        (algebraMap E (w.adicCompletion E)) := hcoeff
  have hιglobal : j.toRingHom.comp (algebraMap E A) = ι := by
    rfl
  have hσ : j.comp σ = coefficientEmbeddingAbovePrime p m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
      w L := globalEulerPlusLabel_comp_localEmbedding
        p m hm E hE w A L j hcoeff'
  refine ⟨ν, hν, hνfin, σ,
    realCyclotomic_minpoly_splits_in_cyclotomic_extension p A, χ, rfl, hχ, ?_⟩
  unfold EulerPlusCompatibleAtAllPlaces
  intro ξ v
  exact chosenEuler_twistedPlus_at_place_of_darmonComparison
    p m hN hp hmPos hmLt hm w L A
      (realCyclotomic_minpoly_splits_in_cyclotomic_extension p A)
      σ χ j hcoeff' hσ ξ (by exact hcomparison ξ) v

end ChosenConductor

section CanonicalConductor

variable (p : ℕ) [Fact p.Prime]

local instance eulerPlusConductorNormedField : NormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNormedField p
local instance eulerPlusConductorNontriviallyNormedField : NontriviallyNormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNontriviallyNormedField p
local instance eulerPlusConductorNormedAlgebra : NormedAlgebra ℚ_[p] (FullConductorCompletion p) :=
  fullConductorCanonicalNormedAlgebra p
local instance eulerPlusConductorCompleteSpace : CompleteSpace (FullConductorCompletion p) := inferInstance
local instance eulerPlusConductorLocalField : IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

/-- The all-place comparison is obtained at the actual conductor completion.
One finite algebraic character and one RM embedding are chosen before all
fibres and all target places. -/
theorem exists_chosenEuler_twistedPlus_at_all_places_conductor
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p) :
    let E := cyclotomicField p
    let L := FullConductorCompletion p
    let : Algebra E L :=
      ((algebraMap ((primeAboveConductor p).adicCompletion E) L).comp
        (algebraMap E ((primeAboveConductor p).adicCompletion E))).toAlgebra
    ∃ ν : AbsoluteGalois (realCyclotomicField p) →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        let A := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
        let : NumberField A :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ (σ : realCyclotomicField p →ₐ[ℚ] A)
          (hA : ∀ a : realCyclotomicField p,
            ((minpoly ℚ a).map (algebraMap ℚ A)).Splits)
          (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) A),
          σ = (Algebra.algHom ℚ E A).comp
            (coefficientEmbedding p m
              (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt) E
              ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans
                (realCyclotomicNormalClosure_le_full p))) ∧
          (Units.map A.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          ∀ (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
            (v : HeightOneSpectrum (𝓞 A)),
            Nonempty ((((chosenCommonEulerCompatibleSystem p m
              (Fact.out : p.Prime) hp hmPos hmLt ξ
              ).extendCoefficients (L := A)).action v).Equiv
              (((primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ).action v)) := by
  simpa only [EulerPlusCompatibleAtAllPlaces] using
    (exists_chosenEuler_twistedPlus_at_all_places p hp m hmPos hmLt
      (primeAboveConductor p) (FullConductorCompletion p)
      (ProjectiveLine.midpointParameter (realCyclotomicField p)))

end CanonicalConductor

end HilbertModularity.Hypergeometric
