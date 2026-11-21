/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CovariantFrobeniusNormalization
public import HilbertModularity.RepresentationTheory.CompatiblePolynomials

/-! # From covariant arithmetic Frobenius to an actual cohomological action

An equivalence between the dual of a covariant Tate action and a separately
given cohomological action carries the arithmetic-Frobenius Hecke polynomial
to geometric Frobenius. The covariant trace and determinant identities are
independent inputs; the cohomological identities are consequences. This is
the duality convention in [TripathiGoswami, Remark 2.4].
-/

public noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace HilbertModularity.HilbertModularForms

variable {F A : Type*} [Field F] [NumberField F]
  [Field A] [NumberField A]
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

section AlgebraicCoefficients

variable {K : Type*} [Field K]

/-- An actual dual-action equivalence transfers the covariant arithmetic
Hecke polynomial to cohomological geometric Frobenius. No twist or reciprocal
polynomial is introduced. -/
theorem cohomologicalGeometricFrobenius_heckeCharpoly_of_dualEquiv
    (φ : AlgebraicGoodPrimeEigenform level μ A) (ι : A →+* K)
    (ρ σ : Representation K (AbsoluteGalois F) (Fin 2 → K))
    (e : ρ.dual.Equiv σ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (htrace : LinearMap.trace K (Fin 2 → K)
      (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)) =
        ι (φ.heckeCoefficient q hq))
    (hdet : LinearMap.det
      (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)) =
        (Nat.card (𝓞 F ⧸ P) : K) * ι (φ.centralCoefficient q hq)) :
    (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      (φ.heckePolynomial q hq).map ι := by
  exact (e.charpoly_eq _).symm.trans
    (cohomologicalGeometricFrobenius_heckeCharpoly_of_covariantArithmetic
      φ ι ρ q hq P hP Q htrace hdet)

end AlgebraicCoefficients

section LocalCoefficients

variable {K : Type*} [NormedField K]

/-- Construct the one-place cohomological realization from a separately
supplied cohomological action, its continuity and unramifiedness, a dual-action
equivalence, and the covariant arithmetic-Frobenius Hecke identities. The
cohomological trace and determinant fields are proved from the polynomial. -/
def cohomologicalRealizationOfCovariantArithmetic
    {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (φ : AlgebraicGoodPrimeEigenform level μ A) (ι : A →+* K)
    (ρ σ : Representation K (AbsoluteGalois F) (Fin 2 → K))
    (e : ρ.dual.Equiv σ)
    (hcontinuous : ∀ i j : Fin 2,
      Continuous (fun g : AbsoluteGalois F => σ g (Pi.single j 1) i))
    (hunramified : ∀ q (_hq : q ∉ φ.form.bad)
      (P : Ideal (𝓞 F)) [P.IsMaximal] (_hP : P = q.asIdeal)
      (_hp : (p : 𝓞 F) ∉ P)
      (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
      (g : AbsoluteGalois F),
        g ∈ Q.inertia (AbsoluteGalois F) → σ g = 1)
    (htrace : ∀ q (hq : q ∉ φ.form.bad)
      (P : Ideal (𝓞 F)) [P.IsMaximal] (_hP : P = q.asIdeal)
      (_hp : (p : 𝓞 F) ∉ P)
      (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        LinearMap.trace K (Fin 2 → K)
          (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)) =
            ι (φ.heckeCoefficient q hq))
    (hdet : ∀ q (hq : q ∉ φ.form.bad)
      (P : Ideal (𝓞 F)) [P.IsMaximal] (_hP : P = q.asIdeal)
      (_hp : (p : 𝓞 F) ∉ P)
      (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        LinearMap.det
          (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)) =
            (Nat.card (𝓞 F ⧸ P) : K) * ι (φ.centralCoefficient q hq)) :
    CohomologicalRealization φ p K where
  coefficientEmbedding := ι
  action := σ
  continuous := hcontinuous
  unramified := hunramified
  frobenius_trace := by
    intro q hq P _ hP hp Q _ _
    let T := σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)
    let b := Pi.basisFun K (Fin 2)
    have hpoly := cohomologicalGeometricFrobenius_heckeCharpoly_of_dualEquiv
      φ ι ρ σ e q hq P hP Q (htrace q hq P hP hp Q) (hdet q hq P hP hp Q)
    have hM : (LinearMap.toMatrix b b T).charpoly =
        X ^ 2 - C (ι (φ.heckeCoefficient q hq)) * X +
          C ((Nat.card (𝓞 F ⧸ q.asIdeal) : K) *
            ι (φ.centralCoefficient q hq)) := by
      rw [LinearMap.charpoly_toMatrix]
      simpa [T, φ.heckePolynomial_map] using hpoly
    rw [LinearMap.trace_eq_matrix_trace K b,
      Matrix.trace_eq_neg_charpoly_coeff, hM]
    simp
  frobenius_det := by
    intro q hq P _ hP hp Q _ _
    let T := σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)
    let b := Pi.basisFun K (Fin 2)
    have hpoly := cohomologicalGeometricFrobenius_heckeCharpoly_of_dualEquiv
      φ ι ρ σ e q hq P hP Q (htrace q hq P hP hp Q) (hdet q hq P hP hp Q)
    have hM : (LinearMap.toMatrix b b T).charpoly =
        X ^ 2 - C (ι (φ.heckeCoefficient q hq)) * X +
          C ((Nat.card (𝓞 F ⧸ q.asIdeal) : K) *
            ι (φ.centralCoefficient q hq)) := by
      rw [LinearMap.charpoly_toMatrix]
      simpa [T, φ.heckePolynomial_map] using hpoly
    have hv := congrArg (fun f : Polynomial K => f.eval 0) hM
    rw [← LinearMap.det_toMatrix b]
    rw [Matrix.charpoly_fin_two] at hv
    simpa [T, hP] using hv

end LocalCoefficients

end HilbertModularity.HilbertModularForms
