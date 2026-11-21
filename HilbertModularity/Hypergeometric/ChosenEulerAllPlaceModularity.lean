/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ChosenEulerModularity
public import HilbertModularity.Hypergeometric.ChosenEulerPromotion

/-! # All-place automorphy of the chosen prime Euler family

The constructed finite character supplies one local eigenform realization;
its retained coefficient embedding and the same-quotient polynomial comparison
then supply every coefficient place. This is the actual Euler application of
[TripathiGoswamiRevised, Theorem `thm:prime`].
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- The cyclotomic coefficient field contains the normal closure of its
real subfield, since the cyclotomic extension is normal. -/
theorem normalClosure_realCyclotomicField_le_cyclotomicField
    (N : ℕ) [NeZero N] :
    IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤
      cyclotomicField N :=
  IntermediateField.normalClosure_le_iff_of_normal.mpr (realCyclotomicField_le N)

/-- One same-family Skinner–Wiles checklist gives a spherical eigenform for
all coefficient places of the actual chosen Euler system. Its finite
comparison character, local polynomial comparison and common coefficient
extension are constructed; the checklist and covariant coordinates remain
explicit until the DO application supplies them. -/
theorem exists_chosenEuler_allPlaceEigenform_of_skinnerWiles
    (N m : ℕ) [NeZero N] [Fact N.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [w.asIdeal.LiesOver (Ideal.span {(N : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [ContinuousSMul (w.adicCompletion (cyclotomicField N)) L]
    [NormedAlgebra ℚ_[N] L] [FiniteDimensional ℚ_[N] L]
    [IsScalarTower ℚ_[N] (w.adicCompletion (cyclotomicField N)) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ ℚ_[N] L]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [CharP (𝒪[L] ⧸ 𝓂[L]) N]
    (ι : cyclotomicField N →+* L)
    (hcoeff : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ρ : Representation L (AbsoluteGalois (realCyclotomicField N)) (Fin 2 → L))
    (e : ρ.Equiv (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
      (darmonLabelledTateFamily (realCyclotomicField N)
        N (le_trans (by decide : 3 ≤ 5) h5) N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) (cyclotomicField N) (normalClosure_realCyclotomicField_le_cyclotomicField N) w L)))
    (M : Type*) [Field M] [NumberField M] [Algebra (realCyclotomicField N) M]
    (H : SkinnerWilesWeightTwoInput N ρ M) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (j : cyclotomicField N →+* B)
        (level : FiniteLevel (realCyclotomicField N))
        (μ : AdditiveQuotientMeasure (realCyclotomicField N))
        (ψ : AlgebraicGoodPrimeEigenform level μ B),
        letI : Algebra (cyclotomicField N) B := j.toAlgebra
        ∃ T : EigenformCohomologicalActions ψ,
          ψ.complexEmbedding = B.val.toRingHom ∧
          (∃ b : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ b) ∧
          (Set.range ψ.form.central_character).Finite ∧
          (∀ q, q ∉ (chosenCommonEulerCompatibleSystem N m hN h5 hmPos hmN ξ).bad →
            ∃ hψ : q ∉ ψ.form.bad,
              ((chosenCommonEulerCompatibleSystem N m hN h5 hmPos hmN ξ).polynomial q).map
                j = ψ.heckePolynomial q hψ) ∧
          ∀ v : HeightOneSpectrum (𝓞 B),
            Nonempty ((((chosenCommonEulerCompatibleSystem N m hN h5 hmPos hmN ξ
              ).extendCoefficients (L := B)).action v).Equiv (T.action v)) := by
  have hι : coefficientEmbeddingAbovePrime N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) (cyclotomicField N)
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans (normalClosure_realCyclotomicField_le_cyclotomicField N))
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m) := by
    rw [coefficientEmbeddingAbovePrime_tau_one]
    have hvalue : IntermediateField.inclusion
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans
          (normalClosure_realCyclotomicField_le_cyclotomicField N)) (tau N m) =
        (root N) ^ m + (root N)⁻¹ ^ m := by
      apply Subtype.ext
      rfl
    rw [hvalue]
    exact congrArg (fun f : cyclotomicField N →+* L =>
      f ((root N) ^ m + (root N)⁻¹ ^ m)) hcoeff
  obtain ⟨level, μ, C, hC, hCnf, φ, r, iF, hiF, hb, hz, _hsys, ⟨euler⟩⟩ :=
    exists_chosenEuler_eigenform_withCoefficientEmbedding_of_skinnerWiles
      N m hN h5 hmPos hmN (cyclotomicField N) (normalClosure_realCyclotomicField_le_cyclotomicField N) w L ι hι ξ ρ e M H
  obtain ⟨B, hB, i, level', ψ, T, hψ, hb', hz', hpoly, hall⟩ :=
    exists_chosenEuler_allPlaceEigenform_of_localRealization
      N m hN h5 hmPos hmN ξ w N L ι hcoeff C level μ φ r iF
      (hiF.trans hcoeff) hb hz euler
  exact ⟨B, hB, i.comp iF, level', μ, ψ, T, hψ, hb', hz', hpoly, hall⟩

end HilbertModularity.Hypergeometric
