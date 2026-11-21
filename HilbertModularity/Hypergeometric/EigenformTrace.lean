/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FrobeniusHeckeRoots
public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalFrobeniusPolynomial
public import HilbertModularity.RepresentationTheory.CompatiblePolynomials
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Finite hypergeometric values from an actual Hilbert eigenform

This is the last deduction of [TripathiGoswamiRevised, proof of
`thm:intro-main`]. An equivalence with the cohomological representation of one
actual eigenform supplies rank, unramifiedness and its independent Hecke
polynomial. The normalized Euler comparison still has to be supplied for the
selected effective representation. All algebraic coefficients use fixed,
compatible embeddings.
-/

public noncomputable section

open scoped NumberField
open IsDedekindDomain Polynomial

namespace HilbertModularity.Cyclotomic

open HilbertModularForms

attribute [local instance] Ideal.Quotient.field

variable (N : ℕ) [NeZero N]
  {K A L M V : Type*} [Field K] [NumberField K] [Field A] [NumberField A]
  [NormedField L] [Field M] [Algebra L M] {ell : ℕ} [Fact ell.Prime] [NormedAlgebra ℚ_[ell] L]
  [Algebra K (cyclotomicField N)]
  [Algebra (cyclotomicField N) (AlgebraicClosure K)]
  [IsScalarTower K (cyclotomicField N) (AlgebraicClosure K)]
  [IsGalois (cyclotomicField N) (AlgebraicClosure K)]
  [AddCommGroup V] [Module L V] [Module.Free L V] [Module.Finite L V]
  {level : FiniteLevel K} {μ : AdditiveQuotientMeasure K}

/-- A local identification with an actual eigenform implies the finite-field
Hecke formulas. The Hecke coefficients are defined by the adelic eigenform,
not by the supplied effective representation. Its rank-two basis and inertia
triviality are deduced from the identification. The local field and algebraic
coefficients embed compatibly in a common overfield, with no topology required
on that overfield. Repeated roots are allowed. -/
theorem exists_mccarthyValue_eq_eigenform_roots
    (φ : AlgebraicGoodPrimeEigenform level μ A)
    (r : CohomologicalRealization φ ell L)
    (ρ : Representation L (AbsoluteGalois K) V) (e : ρ.Equiv r.action)
    (j : A →+* Qbar) (ι : Qbar →+* M)
    (hι : ι.comp j = (algebraMap L M).comp r.coefficientEmbedding)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ)
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ φ.form.bad)
    [P.asIdeal.LiesOver q.asIdeal]
    (hell : (ell : 𝓞 K) ∉ q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal]
    [Q.LiesOver q.asIdeal] [Q.LiesOver P.asIdeal]
    (hcomparison :
      ι ((cyclotomicField N).val
        (normalizedCyclotomicEulerTrace N P.asIdeal hP m
          (P.specialization ξ hξ.valuation_eq_one.le))) =
        algebraMap L M (LinearMap.trace L V
          (ρ (AlgEquiv.restrictScalarsHom K
            (NumberField.geometricFrobenius (cyclotomicField N)
              (AlgebraicClosure K) P.asIdeal Q :
                AlgebraicClosure K ≃ₐ[cyclotomicField N] AlgebraicClosure K))))) :
    ∃ α β : Qbar,
      (X - C α) * (X - C β) = (φ.heckePolynomial q hq).map j ∧
      mccarthyValue N P hP m θ ξ hξ =
        α ^ P.asIdeal.inertiaDeg (𝓞 K) + β ^ P.asIdeal.inertiaDeg (𝓞 K) ∧
      (P.asIdeal.inertiaDeg (𝓞 K) = 1 →
        mccarthyValue N P hP m θ ξ hξ = j (φ.heckeCoefficient q hq)) ∧
      (P.asIdeal.inertiaDeg (𝓞 K) = 2 →
        mccarthyValue N P hP m θ ξ hξ =
          j (φ.heckeCoefficient q hq) ^ 2 -
            2 * ((Nat.card (𝓞 K ⧸ q.asIdeal) : Qbar) *
              j (φ.centralCoefficient q hq))) := by
  let a := j (φ.heckeCoefficient q hq)
  let δ := (Nat.card (𝓞 K ⧸ q.asIdeal) : Qbar) * j (φ.centralCoefficient q hq)
  have hpoly : (ρ.baseChange M (NumberField.geometricFrobenius K (AlgebraicClosure K)
      q.asIdeal Q : AbsoluteGalois K)).charpoly =
      (X ^ 2 - C a * X + C δ).map ι := by
    change ((ρ _).baseChange M).charpoly = _
    rw [LinearMap.charpoly_baseChange, e.charpoly_eq,
      r.frobenius_charpoly q hq q.asIdeal rfl hell Q, Polynomial.map_map]
    rw [← hι, ← Polynomial.map_map, φ.heckePolynomial_map q hq j]
  have hunram : ∀ g ∈ Q.inertia (AbsoluteGalois K), ρ g = 1 := by
    intro g hg
    ext v
    apply e.toLinearEquiv.injective
    have he := e.toIntertwiningMap.isIntertwining ρ r.action g v
    simpa only [Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.coe_toIntertwiningMap,
      r.unramified q hq q.asIdeal rfl hell Q g hg,
      Module.End.one_apply] using he
  let b := (Pi.basisFun L (Fin 2)).map e.symm.toLinearEquiv
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
  · simpa only [φ.heckePolynomial_map q hq j] using hroots
  · intro hf
    rw [hvalue, hf]
    exact root_sum_of_quadratic_factorization α β a δ hroots
  · intro hf
    rw [hvalue, hf]
    exact root_sq_sum_of_quadratic_factorization α β a δ hroots

end HilbertModularity.Cyclotomic
