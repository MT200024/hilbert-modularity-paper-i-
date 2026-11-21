/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeLevelRefinement
public import HilbertModularity.NumberTheory.HilbertModularForms.GaloisRealization

/-! # Algebraic eigenforms and Galois actions under level refinement

The same adelic eigenfunction has the same algebraic coefficients and Galois
realization after refinement. Only the finite exceptional set grows. This is
used before the finite twist in [TripathiGoswami, §3].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F A : Type*} [Field F] [NumberField F] [Field A] [NumberField A]
  {K : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  {χ : FiniteIdeleClassCharacter F}

/-- Preserve the algebraic coefficients and their complex embedding when
regarding the same eigenfunction at a smaller finite level. -/
def AlgebraicGoodPrimeEigenform.refineLevel
    (φ : AlgebraicGoodPrimeEigenform K μ A) (r : HeckeLevelRefinement K χ) :
    AlgebraicGoodPrimeEigenform r.level μ A where
  form := φ.form.refineLevel r
  complexEmbedding := φ.complexEmbedding
  heckeCoefficient q hq := φ.heckeCoefficient q (φ.form.refineLevel_good r q hq)
  heckeCoefficient_spec q hq := by
    rw [GoodPrimeEigenform.refineLevel_hecke_value]
    exact φ.heckeCoefficient_spec q (φ.form.refineLevel_good r q hq)
  centralCoefficient q hq := φ.centralCoefficient q (φ.form.refineLevel_good r q hq)
  centralCoefficient_spec q hq := by
    rw [GoodPrimeEigenform.refineLevel_central_character,
      GoodPrimeEigenform.refineLevel_hecke_element]
    exact φ.centralCoefficient_spec q _

@[simp]
theorem AlgebraicGoodPrimeEigenform.refineLevel_apply
    (φ : AlgebraicGoodPrimeEigenform K μ A) (r : HeckeLevelRefinement K χ)
    (g : AdelicGL2 F) :
    (φ.refineLevel r).form.toFun g = φ.form.toFun g :=
  GoodPrimeEigenform.refineLevel_apply _ _ _

@[simp]
theorem AlgebraicGoodPrimeEigenform.refineLevel_central_character
    (φ : AlgebraicGoodPrimeEigenform K μ A) (r : HeckeLevelRefinement K χ) :
    (φ.refineLevel r).form.central_character = φ.form.central_character :=
  GoodPrimeEigenform.refineLevel_central_character _ _

@[simp]
theorem AlgebraicGoodPrimeEigenform.refineLevel_complexEmbedding
    (φ : AlgebraicGoodPrimeEigenform K μ A) (r : HeckeLevelRefinement K χ) :
    (φ.refineLevel r).complexEmbedding = φ.complexEmbedding := (rfl)

@[simp]
theorem AlgebraicGoodPrimeEigenform.refineLevel_bad
    (φ : AlgebraicGoodPrimeEigenform K μ A) (r : HeckeLevelRefinement K χ) :
    (φ.refineLevel r).form.bad = φ.form.bad ∪ r.bad :=
  GoodPrimeEigenform.refineLevel_bad _ _

@[simp]
theorem AlgebraicGoodPrimeEigenform.refineLevel_heckeCoefficient
    (φ : AlgebraicGoodPrimeEigenform K μ A) (r : HeckeLevelRefinement K χ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad ∪ r.bad) :
    (φ.refineLevel r).heckeCoefficient q
        (by simpa only [refineLevel_bad] using hq) =
      φ.heckeCoefficient q (fun h => hq (Or.inl h)) := (rfl)

@[simp]
theorem AlgebraicGoodPrimeEigenform.refineLevel_centralCoefficient
    (φ : AlgebraicGoodPrimeEigenform K μ A) (r : HeckeLevelRefinement K χ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad ∪ r.bad) :
    (φ.refineLevel r).centralCoefficient q
        (by simpa only [refineLevel_bad] using hq) =
      φ.centralCoefficient q (fun h => hq (Or.inl h)) := (rfl)

/-- The unchanged Galois representation realizes the refined eigenfunction. -/
def CohomologicalRealization.refineLevel
    {φ : AlgebraicGoodPrimeEigenform K μ A}
    {p : ℕ} [Fact p.Prime] {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]
    (ρ : CohomologicalRealization φ p E) (r : HeckeLevelRefinement K χ) :
    CohomologicalRealization (φ.refineLevel r) p E where
  coefficientEmbedding := ρ.coefficientEmbedding
  action := ρ.action
  continuous := ρ.continuous
  unramified q hq := ρ.unramified q (φ.form.refineLevel_good r q hq)
  frobenius_trace q hq := ρ.frobenius_trace q (φ.form.refineLevel_good r q hq)
  frobenius_det q hq := ρ.frobenius_det q (φ.form.refineLevel_good r q hq)

@[simp]
theorem CohomologicalRealization.refineLevel_action
    {φ : AlgebraicGoodPrimeEigenform K μ A}
    {p : ℕ} [Fact p.Prime] {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]
    (ρ : CohomologicalRealization φ p E) (r : HeckeLevelRefinement K χ) :
    (ρ.refineLevel r).action = ρ.action := (rfl)

@[simp]
theorem CohomologicalRealization.refineLevel_coefficientEmbedding
    {φ : AlgebraicGoodPrimeEigenform K μ A}
    {p : ℕ} [Fact p.Prime] {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]
    (ρ : CohomologicalRealization φ p E) (r : HeckeLevelRefinement K χ) :
    (ρ.refineLevel r).coefficientEmbedding = ρ.coefficientEmbedding := (rfl)

end HilbertModularity.HilbertModularForms
