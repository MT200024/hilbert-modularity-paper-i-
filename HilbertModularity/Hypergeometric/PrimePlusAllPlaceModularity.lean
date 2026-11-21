/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusSphericalModularity
public import HilbertModularity.RepresentationTheory.CompatibleSystemPromotion
public import HilbertModularity.RepresentationTheory.CompatibleSystemCoefficientExtension

/-! # All-place automorphy of the selected plus Jacobian

Apply the promotion argument in [TripathiGoswamiRevised, Lemma
`lem:promotion` and Theorem `thm:prime`] to the actual selected system. The
coefficient extension is constructed by contraction of primes and the canonical
maps of completions. The same eigenform realizes every extended action.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain NumberField
open scoped ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme HilbertModularForms

/-- The selected finite-character-twisted plus-Jacobian system is realized by
one spherical eigenform at every coefficient place after one number-field
extension. The same-Jacobian Skinner--Wiles checklist remains an explicit
premise; no effective Euler comparison is asserted. -/
theorem exists_primePlus_allPlaceEigenform_of_skinnerWiles
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (A : Type) [Field A] [NumberField A]
    (hA : ∀ a : realCyclotomicField p, ((minpoly ℚ a).map (algebraMap ℚ A)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] A)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) A)
    (E : Type) [NontriviallyNormedField E] [CompleteSpace E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p] [Algebra ℚ E] [IsScalarTower ℚ ℚ_[p] E]
    (hE : ∀ a : realCyclotomicField p, ((minpoly ℚ a).map (algebraMap ℚ E)).Splits)
    (j : A →ₐ[ℚ] E)
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (e : ρ.Equiv ((endomorphismLabelledTate (realCyclotomicField p)
      (primePlusFiber p hp ξ) p (realCyclotomicField p) E hE
      (primePlusFiberRealMultiplication p hp ξ) (j.comp σ)).toRepresentation))
    (L : Type*) [Field L] [NumberField L] [Algebra (realCyclotomicField p) L]
    (H : SkinnerWilesWeightTwoInput p ρ L) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (i : A →+* B) (level : FiniteLevel (realCyclotomicField p))
        (μ : AdditiveQuotientMeasure (realCyclotomicField p))
        (ψ : AlgebraicGoodPrimeEigenform level μ B),
        letI : Algebra A B := i.toAlgebra
        ∃ D : EigenformCohomologicalActions ψ,
        ψ.complexEmbedding = B.val.toRingHom ∧
        (∃ C : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ C) ∧
        (Set.range ψ.form.central_character).Finite ∧
        (∀ q, q ∉ ((primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ).bad →
          ∃ hψ : q ∉ ψ.form.bad,
            (((primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ).polynomial q).map i =
              ψ.heckePolynomial q hψ) ∧
        ∀ w : HeightOneSpectrum (𝓞 B),
          Nonempty (((NumberFieldCompatibleSystem.extendCoefficients (L := B)
            ((primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ)).action w).Equiv
              (D.action w)) := by
  obtain ⟨B, hB, i, level, μ, ψ, hψ, hb, hc, hpoly⟩ :=
    exists_primePlus_sphericalEigenform_of_skinnerWiles p hp ξ A hA σ χ E hE j ρ e L H
  let := hB
  let : Algebra A B := i.toAlgebra
  obtain ⟨D⟩ := exists_eigenformCohomologicalActions ψ hb hc
  refine ⟨B, hB, i, level, μ, ψ, D, hψ, hb, hc, hpoly, ?_⟩
  intro w
  let S := (primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ
  have he := (S.extendCoefficients (L := B)).equiv_of_polynomial_eq
    D.toCompatibleSystem.system (fun q hq _ht => ?_) w
  · simpa only [D.toCompatibleSystem_action] using he
  · have hs : q ∉ S.bad := by
      simpa only [NumberFieldCompatibleSystem.extendCoefficients_bad] using hq
    obtain ⟨hqψ, hqpoly⟩ := hpoly q hs
    rw [NumberFieldCompatibleSystem.extendCoefficients_polynomial,
      D.toCompatibleSystem.polynomial_eq q hqψ]
    exact hqpoly

end HilbertModularity.Hypergeometric
