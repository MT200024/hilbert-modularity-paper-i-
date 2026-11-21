/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CompatibleSystem
public import HilbertModularity.RepresentationTheory.FrobeniusDualNormalization

/-! # Covariant arithmetic and cohomological geometric Hecke polynomials

A literature construction may report the Hecke trace and determinant on a
covariant Tate action at arithmetic Frobenius. Once those two independent
identities have been matched to the actual eigenform, duality converts them
to its cohomological geometric-Frobenius Hecke polynomial. This proves the
normalization step without treating the existence of either action or the
classical-to-adelic Hecke correspondence as automatic.
-/

public noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace HilbertModularity.HilbertModularForms

variable {F E K : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Field K]
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- Independent arithmetic-Frobenius trace and determinant formulas give the
eigenform's algebraic Hecke polynomial at the chosen coefficient embedding. -/
theorem covariantArithmeticFrobenius_heckeCharpoly
    (φ : AlgebraicGoodPrimeEigenform level μ E) (ι : E →+* K)
    (ρ : Representation K (AbsoluteGalois F) (Fin 2 → K))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (htrace : LinearMap.trace K (Fin 2 → K)
      (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)) =
        ι (φ.heckeCoefficient q hq))
    (hdet : LinearMap.det
      (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)) =
        (Nat.card (𝓞 F ⧸ P) : K) * ι (φ.centralCoefficient q hq)) :
    (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      (φ.heckePolynomial q hq).map ι := by
  let T := ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)
  let b := Pi.basisFun K (Fin 2)
  rw [← LinearMap.charpoly_toMatrix T b, Matrix.charpoly_fin_two]
  rw [← LinearMap.trace_eq_matrix_trace K b,
    LinearMap.det_toMatrix b, htrace, hdet]
  rw [φ.heckePolynomial_map]
  simp [hP]

/-- Dualizing a covariant arithmetic-Frobenius Hecke action gives the
cohomological geometric-Frobenius polynomial with exactly the same Hecke
coefficient and norm times central coefficient. -/
theorem cohomologicalGeometricFrobenius_heckeCharpoly_of_covariantArithmetic
    (φ : AlgebraicGoodPrimeEigenform level μ E) (ι : E →+* K)
    (ρ : Representation K (AbsoluteGalois F) (Fin 2 → K))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (htrace : LinearMap.trace K (Fin 2 → K)
      (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)) =
        ι (φ.heckeCoefficient q hq))
    (hdet : LinearMap.det
      (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)) =
        (Nat.card (𝓞 F ⧸ P) : K) * ι (φ.centralCoefficient q hq)) :
    (ρ.dual (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      (φ.heckePolynomial q hq).map ι := by
  exact (HilbertModularity.charpoly_dual_geometricFrobenius_eq_arithmetic ρ P Q).trans
    (covariantArithmeticFrobenius_heckeCharpoly φ ι ρ q hq P hP Q htrace hdet)

end HilbertModularity.HilbertModularForms
