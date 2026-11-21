/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FrobeniusHeckeRoots
public import HilbertModularity.NumberTheory.HilbertModularForms.CompatibleSystem
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Compatible-system trace formulas after spherical replacement

The all-good-prime polynomial comparison in
`CohomologicalRealization.exists_sphericalEigenform_of_localComparison` feeds
this final deduction of [TripathiGoswamiRevised, `thm:intro-main`].
The actual eigenform may have a larger coefficient field. The trace is still
computed in an original completion of the independently supplied effective
system; no enlarged compatible system is needed. The selected normalized Euler
comparison remains an explicit input.
-/

public noncomputable section

open scoped NumberField
open IsDedekindDomain Polynomial

namespace HilbertModularity.Cyclotomic

open HilbertModularForms

attribute [local instance] Ideal.Quotient.field

variable (N : ℕ) [NeZero N]
  {K A B M : Type*} [Field K] [NumberField K] [Field A] [NumberField A]
  [Field B] [NumberField B] [Field M]
  [Algebra K (cyclotomicField N)]
  [Algebra (cyclotomicField N) (AlgebraicClosure K)]
  [IsScalarTower K (cyclotomicField N) (AlgebraicClosure K)]
  [IsGalois (cyclotomicField N) (AlgebraicClosure K)]
  {level : FiniteLevel K} {μ : AdditiveQuotientMeasure K}

/-- Equality with the independently defined Hecke polynomial supplies the
finite-field root and degree-one/two formulas after coefficient enlargement.
Both the local comparison and the normalized Euler trace use the same original
coefficient completion, embedded in a common overfield. -/
theorem exists_mccarthyValue_eq_compatibleEigenform_roots
    (S : NumberFieldCompatibleSystem K A)
    (φ : AlgebraicGoodPrimeEigenform level μ B)
    (i : A →+* B) (w : HeightOneSpectrum (𝓞 A))
    [Algebra (w.adicCompletion A) M]
    (j : B →+* Qbar) (ι : Qbar →+* M)
    (hι : ι.comp (j.comp i) =
      (algebraMap (w.adicCompletion A) M).comp (algebraMap A (w.adicCompletion A)))
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ)
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S.bad)
    (hφ : q ∉ φ.form.bad)
    (hHecke : (S.polynomial q).map i = φ.heckePolynomial q hφ)
    [P.asIdeal.LiesOver q.asIdeal]
    (hell : (S.residueCharacteristic w : 𝓞 K) ∉ q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal]
    [Q.LiesOver q.asIdeal] [Q.LiesOver P.asIdeal]
    (hcomparison :
      ι ((cyclotomicField N).val
        (normalizedCyclotomicEulerTrace N P.asIdeal hP m
          (P.specialization ξ hξ.valuation_eq_one.le))) =
        algebraMap (w.adicCompletion A) M
        (LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
          (S.action w (AlgEquiv.restrictScalarsHom K
            (NumberField.geometricFrobenius (cyclotomicField N)
              (AlgebraicClosure K) P.asIdeal Q :
                AlgebraicClosure K ≃ₐ[cyclotomicField N] AlgebraicClosure K))))) :
    ∃ α β : Qbar,
      (X - C α) * (X - C β) = (φ.heckePolynomial q hφ).map j ∧
      mccarthyValue N P hP m θ ξ hξ =
        α ^ P.asIdeal.inertiaDeg (𝓞 K) + β ^ P.asIdeal.inertiaDeg (𝓞 K) ∧
      (P.asIdeal.inertiaDeg (𝓞 K) = 1 →
        mccarthyValue N P hP m θ ξ hξ = j (φ.heckeCoefficient q hφ)) ∧
      (P.asIdeal.inertiaDeg (𝓞 K) = 2 →
        mccarthyValue N P hP m θ ξ hξ =
          j (φ.heckeCoefficient q hφ) ^ 2 -
            2 * ((Nat.card (𝓞 K ⧸ q.asIdeal) : Qbar) *
              j (φ.centralCoefficient q hφ))) := by
  let ρ := S.action w
  let a := j (φ.heckeCoefficient q hφ)
  let δ := (Nat.card (𝓞 K ⧸ q.asIdeal) : Qbar) * j (φ.centralCoefficient q hφ)
  have hpoly : (ρ.baseChange M (NumberField.geometricFrobenius K (AlgebraicClosure K)
      q.asIdeal Q : AbsoluteGalois K)).charpoly =
      (X ^ 2 - C a * X + C δ).map ι := by
    change ((ρ _).baseChange M).charpoly = _
    rw [LinearMap.charpoly_baseChange,
      S.frobenius_charpoly w q hq q.asIdeal rfl hell Q, Polynomial.map_map]
    rw [← hι, ← Polynomial.map_map,
      ← Polynomial.map_map, hHecke, φ.heckePolynomial_map q hφ j]
  have hunram : ∀ g ∈ Q.inertia (AbsoluteGalois K), ρ g = 1 :=
    S.unramified w q hq q.asIdeal rfl hell Q
  let b := Pi.basisFun (w.adicCompletion A) (Fin 2)
  have hunramM : ∀ g ∈ Q.inertia (AbsoluteGalois K), ρ.baseChange M g = 1 := by
    intro g hg
    change (ρ g).baseChange M = 1
    rw [hunram g hg, LinearMap.baseChange_one]
  have hcomparisonM : ι ((cyclotomicField N).val
      (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization ξ hξ.valuation_eq_one.le))) =
      LinearMap.trace M _ (ρ.baseChange M
        (AlgEquiv.restrictScalarsHom K
          (NumberField.geometricFrobenius (cyclotomicField N)
            (AlgebraicClosure K) P.asIdeal Q :
              AlgebraicClosure K ≃ₐ[cyclotomicField N] AlgebraicClosure K))) := by
    change _ = LinearMap.trace M _ ((ρ _).baseChange M)
    rw [LinearMap.trace_baseChange]
    exact hcomparison
  obtain ⟨α, β, hroots, hvalue⟩ := exists_mccarthyValue_eq_hecke_root_powers
    N P hP m hm hmN θ hθ ξ hξ q.asIdeal Q (ρ.baseChange M) (b.baseChange M) hunramM ι a δ hpoly hcomparisonM
  refine ⟨α, β, ?_, hvalue, ?_, ?_⟩
  · simpa only [φ.heckePolynomial_map q hφ j] using hroots
  · intro hf
    rw [hvalue, hf]
    exact root_sum_of_quadratic_factorization α β a δ hroots
  · intro hf
    rw [hvalue, hf]
    exact root_sq_sum_of_quadratic_factorization α β a δ hroots

end HilbertModularity.Cyclotomic
