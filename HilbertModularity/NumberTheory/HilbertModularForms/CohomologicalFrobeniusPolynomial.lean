/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CompatibleSystem

/-! # Frobenius polynomial of a cohomological Hilbert realization

The trace and determinant of an independently supplied realization determine
its rank-two geometric-Frobenius polynomial. The right side is the Hecke
polynomial defined from the adelic eigenform before the realization was chosen.
-/

public noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace HilbertModularity.HilbertModularForms

variable {F A E : Type*} [Field F] [NumberField F]
  [Field A] [NumberField A]
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The cohomological geometric-Frobenius polynomial is the image of the
independent weight-two Hecke polynomial. -/
theorem CohomologicalRealization.frobenius_charpoly
    [NormedField E] {p : ℕ} [Fact p.Prime]
    [NormedAlgebra ℚ_[p] E]
    {φ : AlgebraicGoodPrimeEigenform level μ A}
    (r : CohomologicalRealization φ p E)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (r.action (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      (φ.heckePolynomial q hq).map r.coefficientEmbedding := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  let T := r.action g
  let b := Pi.basisFun E (Fin 2)
  rw [← LinearMap.charpoly_toMatrix T b, Matrix.charpoly_fin_two]
  rw [← LinearMap.trace_eq_matrix_trace E b,
    LinearMap.det_toMatrix b,
    r.frobenius_trace q hq P hP hp Q,
    r.frobenius_det q hq P hP hp Q]
  rw [φ.heckePolynomial_map]
  simp [hP]

end HilbertModularity.HilbertModularForms
