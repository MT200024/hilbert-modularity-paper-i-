/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationGenericMonodromy
public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesFiniteComparison

/-! # Automorphy of the chosen Euler realization at the conductor prime

The finite comparison character is constructed from the selected quotient's
geometric and Hodge inputs. Cohomological duality then connects that comparison
to the covariant Skinner–Wiles theorem. This is the chosen-prime deduction of
[TripathiGoswamiRevised, Theorem `thm:prime`].
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- The actual chosen prime-level Euler realization is realized by a cuspidal
weight-two eigenform at the conductor prime. The Skinner–Wiles checklist is
for the covariant action of the same chosen Darmon family in supplied coordinates.
The finite Euler comparison character is constructed in the proof. The original
algebraic coefficient field embeds into the eigenform field compatibly with
the supplied local completion; this embedding is retained for promotion. Establishing
the checklist from DO and promoting the Euler system to all coefficient places
are separate manuscript applications. -/
theorem exists_chosenEuler_eigenform_withCoefficientEmbedding_of_skinnerWiles
    (N m : ℕ) [NeZero N] [Fact N.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(N : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[N] L] [FiniteDimensional ℚ_[N] L]
    [IsScalarTower ℚ_[N] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[N] L]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [CharP (𝒪[L] ⧸ 𝓂[L]) N]
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ρ : Representation L (AbsoluteGalois (realCyclotomicField N)) (Fin 2 → L))
    (e : ρ.Equiv (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
      (darmonLabelledTateFamily (realCyclotomicField N)
        N (le_trans (by decide : 3 ≤ 5) h5) N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E hE w L)))
    (M : Type*) [Field M] [NumberField M] [Algebra (realCyclotomicField N) M]
    (H : SkinnerWilesWeightTwoInput N ρ M) :
    let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hmPos hmN
    let D := R.placeDescent N m 𝒞 N L ι
    ∃ (level : FiniteLevel (realCyclotomicField N))
      (μ : AdditiveQuotientMeasure (realCyclotomicField N))
      (C : Type) (hC : Field C),
      letI := hC
      ∃ hCnf : NumberField C,
        letI := hCnf
        ∃ ψ : AlgebraicGoodPrimeEigenform level μ C,
          ∃ (r : CohomologicalRealization ψ N L) (iE : E →+* C),
            r.coefficientEmbedding.comp iE =
              (algebraMap (w.adicCompletion E) L).comp
                (algebraMap E (w.adicCompletion E)) ∧
            (∃ B : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ B) ∧
            (Set.range ψ.form.central_character).Finite ∧
            Nonempty (EigenformCompatibleSystem ψ) ∧
            Nonempty ((puncturedFiberArithmeticRepresentation
              (realCyclotomicField N) ξ D.localSystem).Equiv r.action) := by
  obtain ⟨ν, _hν, hνfin, χ, _hχ, _hcoeff, hcomparison⟩ :=
    exists_algebraic_character_comparing_chosenEuler_realization
      N m hN h5 hmPos hmN E hE w L ι hι ξ
  let : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
    (algebraMap E (w.adicCompletion E))).toAlgebra
  let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
  let : NumberField E' :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
  have eDual : ρ.dual.Equiv
      (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
        (darmonCohomologicalFamily (realCyclotomicField N)
          N (le_trans (by decide : 3 ≤ 5) h5) N m
          (eulerExponent_coprime_of_prime N m hN hmPos hmN) E hE w L)) := by
    unfold puncturedFiberArithmeticRepresentation darmonCohomologicalFamily
    rw [Scheme.EtaleLocalSystem.cohDual_arithmeticRepresentation]
    exact representationDualEquiv e
  obtain ⟨ec⟩ := hcomparison ξ
  let et := Representation.characterTensorEquivCongr
    ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom) eDual
  obtain ⟨level, μ, C, hC, hCnf, ψ, r, i, hi, hb, hz, hsys, he⟩ :=
    exists_eigenform_of_skinnerWiles_finiteComparison_withAnalyticData
      N ρ M H χ E'.subtype _ ⟨et.trans ec⟩
  refine ⟨level, μ, C, hC, hCnf, ψ, r,
    i.comp (algebraMap E E'), ?_, hb, hz, hsys, he⟩
  rw [← RingHom.comp_assoc, hi]
  exact RepresentationTheory.finiteCharacterCoefficientField_subtype_comp_algebraMap ν

/-- The actual chosen prime-level Euler realization is realized by a cuspidal
weight-two eigenform at the conductor prime. The Skinner–Wiles checklist is
for the covariant action of the same chosen Darmon family in supplied coordinates.
The finite Euler comparison character is constructed in the proof. Establishing
the checklist from DO and promoting the Euler system to all coefficient places
are separate manuscript applications. -/
theorem exists_chosenEuler_eigenform_of_skinnerWiles
    (N m : ℕ) [NeZero N] [Fact N.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(N : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[N] L] [FiniteDimensional ℚ_[N] L]
    [IsScalarTower ℚ_[N] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[N] L]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [CharP (𝒪[L] ⧸ 𝓂[L]) N]
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ρ : Representation L (AbsoluteGalois (realCyclotomicField N)) (Fin 2 → L))
    (e : ρ.Equiv (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
      (darmonLabelledTateFamily (realCyclotomicField N)
        N (le_trans (by decide : 3 ≤ 5) h5) N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E hE w L)))
    (M : Type*) [Field M] [NumberField M] [Algebra (realCyclotomicField N) M]
    (H : SkinnerWilesWeightTwoInput N ρ M) :
    let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hmPos hmN
    let D := R.placeDescent N m 𝒞 N L ι
    ∃ (level : FiniteLevel (realCyclotomicField N))
      (μ : AdditiveQuotientMeasure (realCyclotomicField N))
      (C : Type) (hC : Field C),
      letI := hC
      ∃ hCnf : NumberField C,
        letI := hCnf
        ∃ ψ : AlgebraicGoodPrimeEigenform level μ C,
          ∃ r : CohomologicalRealization ψ N L,
            (∃ B : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ B) ∧
            (Set.range ψ.form.central_character).Finite ∧
            Nonempty (EigenformCompatibleSystem ψ) ∧
            Nonempty ((puncturedFiberArithmeticRepresentation
              (realCyclotomicField N) ξ D.localSystem).Equiv r.action) := by
  obtain ⟨level, μ, C, hC, hCnf, ψ, r, _iE, _hiE, hb, hz, hsys, he⟩ :=
    exists_chosenEuler_eigenform_withCoefficientEmbedding_of_skinnerWiles
      N m hN h5 hmPos hmN E hE w L ι hι ξ ρ e M H
  exact ⟨level, μ, C, hC, hCnf, ψ, r, hb, hz, hsys, he⟩

end HilbertModularity.Hypergeometric
