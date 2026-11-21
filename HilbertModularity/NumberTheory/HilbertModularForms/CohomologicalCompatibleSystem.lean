/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalFrobeniusPolynomial

/-! # Hilbert cohomological actions and their compatible system

The input records independently constructed Galois actions at all coefficient
places, with their Hecke traces and determinants. The compatible polynomial
is *derived* from these two identities and the rank-two characteristic
polynomial formula. An existence theorem for the actions is a separate
literature obligation; this construction makes no such assertion.
-/

public noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The independently supplied cohomological actions of one algebraic
parallel-weight-two eigenform. At each coefficient place the realization is
continuous and semisimple. Its geometric-Frobenius trace and determinant are
the form's pre-existing Hecke and central coefficients. In particular, no
common Frobenius polynomial is assumed in this input. -/
structure EigenformCohomologicalActions
    (φ : AlgebraicGoodPrimeEigenform level μ E) where
  residueCharacteristic : HeightOneSpectrum (𝓞 E) → ℕ
  residueCharacteristic_prime : ∀ w, (residueCharacteristic w).Prime
  coefficientPrime : ∀ w : HeightOneSpectrum (𝓞 E),
    w.asIdeal.LiesOver (Ideal.span {(residueCharacteristic w : ℤ)})
  action : ∀ w : HeightOneSpectrum (𝓞 E),
    Representation (w.adicCompletion E) (AbsoluteGalois F)
      (Fin 2 → w.adicCompletion E)
  continuous : ∀ w (i j : Fin 2),
    Continuous (fun g : AbsoluteGalois F =>
      action w g (Pi.single j 1) i)
  semisimple : ∀ w, (action w).IsSemisimpleRepresentation
  unramified : ∀ w q, q ∉ φ.form.bad →
    ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
    (residueCharacteristic w : 𝓞 F) ∉ P →
    ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois F,
        g ∈ Q.inertia (AbsoluteGalois F) → action w g = 1
  frobenius_trace : ∀ w q (hq : q ∉ φ.form.bad),
    ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
    (residueCharacteristic w : 𝓞 F) ∉ P →
    ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
          algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq)
  frobenius_det : ∀ w q (hq : q ∉ φ.form.bad),
    ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
    (residueCharacteristic w : 𝓞 F) ∉ P →
    ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      LinearMap.det
        (action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
          (Nat.card (𝓞 F ⧸ P) : w.adicCompletion E) *
            algebraMap E (w.adicCompletion E) (φ.centralCoefficient q hq)

/-- Rank two converts the independent Hecke trace and determinant identities
into a common algebraic geometric-Frobenius polynomial. -/
theorem EigenformCohomologicalActions.frobenius_charpoly
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (D.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (D.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      (φ.heckePolynomial q hq).map (algebraMap E (w.adicCompletion E)) := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  let T := D.action w g
  let b := Pi.basisFun (w.adicCompletion E) (Fin 2)
  rw [← LinearMap.charpoly_toMatrix T b, Matrix.charpoly_fin_two]
  rw [← LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b,
    LinearMap.det_toMatrix b,
    D.frobenius_trace w q hq P hP hp Q,
    D.frobenius_det w q hq P hP hp Q]
  rw [φ.heckePolynomial_map]
  simp [hP]

/-- Independent all-place cohomological actions, trace and determinant data
construct the compatible system attached to the same eigenform. -/
def EigenformCohomologicalActions.toCompatibleSystem
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ) : EigenformCompatibleSystem φ := by
  classical
  exact {
  system := {
    residueCharacteristic := D.residueCharacteristic
    residueCharacteristic_prime := D.residueCharacteristic_prime
    coefficientPrime := D.coefficientPrime
    action := D.action
    continuous := D.continuous
    semisimple := D.semisimple
    bad := φ.form.bad
    bad_finite := φ.form.bad_finite
    polynomial := fun q => if hq : q ∉ φ.form.bad then φ.heckePolynomial q hq else 0
    unramified := D.unramified
    frobenius_charpoly := by
      intro w q hq P _ hP hp Q _ _
      simpa [hq] using D.frobenius_charpoly w q hq P hP hp Q }
  bad_eq := rfl
  polynomial_eq := by
    intro q hq
    simp [hq] }

@[simp] theorem EigenformCohomologicalActions.toCompatibleSystem_action
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E)) :
    (D.toCompatibleSystem).system.action w = D.action w := by
  rfl

@[simp] theorem EigenformCohomologicalActions.toCompatibleSystem_residueCharacteristic
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E)) :
    (D.toCompatibleSystem).system.residueCharacteristic w = D.residueCharacteristic w := by
  rfl

end HilbertModularity.HilbertModularForms
