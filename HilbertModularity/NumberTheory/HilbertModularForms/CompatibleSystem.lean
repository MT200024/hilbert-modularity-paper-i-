/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.NumberFieldCompatibleSystem

/-! # Compatible systems attached to Hilbert eigenforms

An eigenform already has algebraic Hecke and central coefficients.  A compatible
system attached to it must use those independent coefficients at every finite
coefficient place, with the cohomological geometric-Frobenius convention.
The actual existence theorem is a separate literature obligation; this module
makes the precise output type and its elementary consequences available.
-/

public noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The independent Hecke polynomial of an algebraic weight-two eigenform.
The central coefficient is evaluated on the same standard prime Hecke element
as the eigenvalue.  Its norm factor gives the determinant of *geometric*
Frobenius in the chosen cohomological convention. -/
def AlgebraicGoodPrimeEigenform.heckePolynomial
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad) : Polynomial E :=
  X ^ 2 - C (φ.heckeCoefficient q hq) * X +
    C ((Nat.card (𝓞 F ⧸ q.asIdeal) : E) * φ.centralCoefficient q hq)

/-- Mapping the independent Hecke polynomial through a coefficient embedding
preserves the residue norm and both eigenform coefficients. -/
theorem AlgebraicGoodPrimeEigenform.heckePolynomial_map
    {K : Type*} [Field K] (φ : AlgebraicGoodPrimeEigenform level μ E)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (σ : E →+* K) :
    (φ.heckePolynomial q hq).map σ =
      X ^ 2 - C (σ (φ.heckeCoefficient q hq)) * X +
        C ((Nat.card (𝓞 F ⧸ q.asIdeal) : K) *
          σ (φ.centralCoefficient q hq)) := by
  simp [AlgebraicGoodPrimeEigenform.heckePolynomial]

/-- A semisimple system genuinely attached to one fixed Hilbert eigenform.
The common polynomial is identified with the form's pre-existing algebraic
Hecke data, rather than being used to define those eigenvalues. -/
structure EigenformCompatibleSystem
    (φ : AlgebraicGoodPrimeEigenform level μ E) where
  system : NumberFieldCompatibleSystem F E
  bad_eq : system.bad = φ.form.bad
  polynomial_eq : ∀ q (hq : q ∉ φ.form.bad),
    system.polynomial q = φ.heckePolynomial q hq

/-- At every good geometric prime away from the coefficient characteristic,
the realization has the actual Hecke characteristic polynomial. -/
theorem EigenformCompatibleSystem.frobenius_charpoly
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (S : EigenformCompatibleSystem φ)
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (S.system.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (S.system.action w
      (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
        (φ.heckePolynomial q hq).map (algebraMap E (w.adicCompletion E)) := by
  rw [S.system.frobenius_charpoly w q (S.bad_eq ▸ hq) P hP hp Q,
    S.polynomial_eq q hq]

/-- The Hecke polynomial determines the actual geometric-Frobenius trace.
The coefficient on the right was defined from the adelic Hecke action before
the compatible system was chosen. -/
theorem EigenformCompatibleSystem.frobenius_trace
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (S : EigenformCompatibleSystem φ)
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (S.system.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
      (S.system.action w
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq) := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  let A := S.system.action w g
  let b := Pi.basisFun (w.adicCompletion E) (Fin 2)
  have hpoly := S.frobenius_charpoly w q hq P hP hp Q
  have hM : (LinearMap.toMatrix b b A).charpoly =
      X ^ 2 - C (algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq)) * X +
        C ((Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion E) *
          algebraMap E (w.adicCompletion E) (φ.centralCoefficient q hq)) := by
    rw [LinearMap.charpoly_toMatrix]
    simpa [AlgebraicGoodPrimeEigenform.heckePolynomial] using hpoly
  rw [LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b,
    Matrix.trace_eq_neg_charpoly_coeff, hM]
  simp

/-- The constant coefficient of the same independently defined Hecke
polynomial determines the geometric-Frobenius determinant. -/
theorem EigenformCompatibleSystem.frobenius_det
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (S : EigenformCompatibleSystem φ)
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (S.system.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.det
      (S.system.action w
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      (Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion E) *
        algebraMap E (w.adicCompletion E) (φ.centralCoefficient q hq) := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  let A := S.system.action w g
  let b := Pi.basisFun (w.adicCompletion E) (Fin 2)
  have hpoly := S.frobenius_charpoly w q hq P hP hp Q
  have hM : (LinearMap.toMatrix b b A).charpoly =
      X ^ 2 - C (algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq)) * X +
        C ((Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion E) *
          algebraMap E (w.adicCompletion E) (φ.centralCoefficient q hq)) := by
    rw [LinearMap.charpoly_toMatrix]
    simpa [AlgebraicGoodPrimeEigenform.heckePolynomial] using hpoly
  have hv := congrArg (fun f : Polynomial (w.adicCompletion E) => f.eval 0) hM
  rw [← LinearMap.det_toMatrix b]
  rw [Matrix.charpoly_fin_two] at hv
  simpa using hv

end HilbertModularity.HilbertModularForms
