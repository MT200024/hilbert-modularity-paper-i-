/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationSamePlaceComparison
public import HilbertModularity.NumberTheory.HilbertModularForms.SphericalEigenformComparison
public import HilbertModularity.RepresentationTheory.CompatibleSystemPromotion
public import HilbertModularity.NumberTheory.PrimeBelowComparison

/-! # Promotion of the chosen Euler realization

The local polynomial comparison is derived from the same chosen Euler quotient.
One local eigenform realization therefore yields one spherical eigenform at
all coefficient places, with the original algebraic embedding retained, as in
[TripathiGoswamiRevised, Lemma `lem:promotion` and Theorem `thm:prime`].
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

local instance eulerPromotionCompletionNorm (N : ℕ) [NeZero N]
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField N)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField N))
    (WithZero (Multiplicative ℤ))

/-- A local eigenform realization of the actual chosen Euler descent gives
one spherical eigenform realizing its compatible system at every coefficient
place. The good primes are the canonical Euler primes. No local polynomial
comparison or separate all-place Euler comparison is assumed. -/
theorem exists_chosenEuler_allPlaceEigenform_of_localRealization
    (N m : ℕ) [NeZero N] (hN : N.Prime) (h5 : 5 ≤ N)
    (hm : 0 < m) (hmN : m < N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (ℓ : ℕ) [Fact ℓ.Prime]
    [w.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ_[ℓ]
      (w.adicCompletion (cyclotomicField N)) L]
    (ι : cyclotomicField N →+* L)
    (hι : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    (C : Type) [Field C] [NumberField C]
    (level : FiniteLevel (realCyclotomicField N))
    (μ : AdditiveQuotientMeasure (realCyclotomicField N))
    (φ : AlgebraicGoodPrimeEigenform level μ C)
    (r : CohomologicalRealization φ ℓ L)
    (iF : cyclotomicField N →+* C) (hiF : r.coefficientEmbedding.comp iF = ι)
    (hb : ∃ B : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ B)
    (hz : (Set.range φ.form.central_character).Finite)
    (e : let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hm hmN
      let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hm hmN
      let D := R.placeDescent N m 𝒞 ℓ L ι
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)).Equiv r.action) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (i : C →+* B) (level' : FiniteLevel (realCyclotomicField N))
        (ψ : AlgebraicGoodPrimeEigenform level' μ B),
        letI : Algebra (cyclotomicField N) B := (i.comp iF).toAlgebra
        ∃ T : EigenformCohomologicalActions ψ,
          ψ.complexEmbedding = B.val.toRingHom ∧
          (∃ b : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ b) ∧
          (Set.range ψ.form.central_character).Finite ∧
          (∀ q, q ∉ (chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).bad →
            ∃ hψ : q ∉ ψ.form.bad,
              ((chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).polynomial q).map
                (i.comp iF) = ψ.heckePolynomial q hψ) ∧
          ∀ v : HeightOneSpectrum (𝓞 B),
            Nonempty ((((chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ
              ).extendCoefficients (L := B)).action v).Equiv (T.action v)) := by
  have hℓ := NumberField.primeBelow_eq_of_liesOver (cyclotomicField N) w ℓ
  subst ℓ
  let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hm hmN
  let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hm hmN
  let D := R.placeDescent N m 𝒞 (NumberField.primeBelow (cyclotomicField N) w) L ι
  let σ := D.localSystem.arithmeticRepresentation (ProjectiveLine.puncturedPoint _ ξ)
  let S := chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ
  let : NumberField.IsTotallyReal (realCyclotomicField N) :=
    realCyclotomicField_isTotallyReal N
  obtain ⟨B, hB, i, level', ψ, _hi, hψ, _hc, hb', hz', _hh, hpoly⟩ :=
    r.exists_sphericalEigenform_of_mapped_localComparison hb hz S iF σ e (by
      intro q hq P _ hP hp Q _ _
      subst P
      rw [hiF]
      exact chosenEulerLocalDescent_frobenius_charpoly N m ξ hN h5 hm hmN
        w L ι hι q hq (by
          simpa only [chosenCommonEulerCompatibleSystem_eq_common,
            commonEulerCompatibleSystem_residueCharacteristic] using hp) Q)
  let := hB
  let : Algebra (cyclotomicField N) B := (i.comp iF).toAlgebra
  obtain ⟨T⟩ := exists_eigenformCohomologicalActions ψ hb' hz'
  refine ⟨B, hB, i, level', ψ, T, hψ, hb', hz', hpoly, ?_⟩
  intro v
  have he := (S.extendCoefficients (L := B)).equiv_of_polynomial_eq
    T.toCompatibleSystem.system (fun q hq _ht => ?_) v
  · simpa only [T.toCompatibleSystem_action] using he
  · have hs : q ∉ S.bad := by
      simpa only [NumberFieldCompatibleSystem.extendCoefficients_bad] using hq
    obtain ⟨hqψ, hqpoly⟩ := hpoly q hs
    rw [NumberFieldCompatibleSystem.extendCoefficients_polynomial,
      T.toCompatibleSystem.polynomial_eq q hqψ]
    exact hqpoly

end HilbertModularity.Hypergeometric
