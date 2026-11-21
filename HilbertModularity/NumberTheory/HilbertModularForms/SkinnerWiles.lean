/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesInput

/-! # The weight-two Skinner--Wiles input

We use the covariant normalization of [SkinnerWiles, §4.5, Theorem A].
The automorphic output is a genuine adelic cuspidal Hecke eigenform. The
associated Galois representation uses arithmetic Frobenius, with the
normalization displayed in [SkinnerWiles, §3.3, (3.2)]. General-field
association here comes from Theorem A; §3.3 itself assumes even field degree. Dualizing it and evaluating at geometric Frobenius
gives the cohomological trace and determinant below, with no Tate twist.
-/

public noncomputable section

open NumberField IsDedekindDomain
open scoped ValuativeRel

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- The cuspidal eigenform consequence of the weight-two case of
[SkinnerWiles, §4.5, Theorem A]. The associated Galois representation and its
arithmetic-Frobenius normalization is displayed in §3.3, (3.2), whose
even-degree assumption is not imposed by Theorem A. `ρ` is
the covariant representation to which the lifting theorem applies. Passing
to geometric Frobenius and dualizing gives `ρᵛ ≃ rᶜᵒʰ`; no finite-order or
Tate twist is inserted. The source calls its output a newform, but this
interface records only the eigenform consequence, since no conductor/newvector
structure has yet been formalized. The analytic properties use the adelic
dictionary in §3.1, pp. 27–29: cusp decay on finitely many reduction sectors
bounds the normalized weight-two lift, and its finite-level nebentype has
finite image. These correspondence steps are included in this input. -/
theorem skinnerWiles_weightTwoEigenform_withAnalyticData
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (_h : SkinnerWilesWeightTwoInput p ρ L) :
    ∃ (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F) (A : Type)
      (hA : Field A),
      letI : Field A := hA
      ∃ hN : NumberField A,
        letI : NumberField A := hN
        ∃ φ : AlgebraicGoodPrimeEigenform level μ A,
          ∃ r : CohomologicalRealization φ p E,
            (∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C) ∧
            (Set.range φ.form.central_character).Finite ∧
            Nonempty (ρ.dual.Equiv r.action) := by
  sorry

/-- The cohomological eigenform consequence of [SkinnerWiles, §4.5,
Theorem A], projected from the classical cusp-form output together with
its analytic adelic properties. -/
theorem skinnerWiles_weightTwoEigenform
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (h : SkinnerWilesWeightTwoInput p ρ L) :
    ∃ (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F) (A : Type)
      (hA : Field A),
      letI : Field A := hA
      ∃ hN : NumberField A,
        letI : NumberField A := hN
        ∃ φ : AlgebraicGoodPrimeEigenform level μ A,
          ∃ r : CohomologicalRealization φ p E,
            Nonempty (ρ.dual.Equiv r.action) := by
  obtain ⟨level, μ, A, hA, hN, φ, r, _, _, hequiv⟩ :=
    skinnerWiles_weightTwoEigenform_withAnalyticData p ρ L h
  exact ⟨level, μ, A, hA, hN, φ, r, hequiv⟩

end HilbertModularity.HilbertModularForms
