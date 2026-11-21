/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.CompatibleEigenformTrace
public import HilbertModularity.RepresentationTheory.CompatibleSystemPlaces

/-! # Finite-field traces with one fixed algebraic embedding

The coefficient place in [TripathiGoswamiRevised, proof of
`thm:intro-main`] is chosen after the geometric prime. Extend the fixed
algebraic coefficient embedding into its completed algebraic closure, choose
an absolute prime over the cyclotomic prime, and apply the root formula.
This removes local auxiliary choices and their residue-characteristic
exclusion from the conclusion. The actual Euler trace comparison remains
an application hypothesis.
-/

public noncomputable section

open scoped NumberField
open IsDedekindDomain Polynomial

namespace HilbertModularity.Cyclotomic

open HilbertModularForms

attribute [local instance] Ideal.Quotient.field

variable (N : ℕ) [NeZero N]
  {K A B : Type*} [Field K] [NumberField K] [Field A] [NumberField A]
  [Field B] [NumberField B]
  [Algebra K (cyclotomicField N)]
  [Algebra (cyclotomicField N) (AlgebraicClosure K)]
  [IsScalarTower K (cyclotomicField N) (AlgebraicClosure K)]
  [IsGalois (cyclotomicField N) (AlgebraicClosure K)]
  {level : FiniteLevel K} {μ : AdditiveQuotientMeasure K}

/-- At every good prime, one fixed algebraic coefficient embedding gives
all three finite-field formulas. No coefficient place or absolute Frobenius
prime needs to be supplied in the conclusion. -/
theorem exists_mccarthyValue_eq_compatibleEigenform_roots_at_good_prime
    (S : NumberFieldCompatibleSystem K A)
    (φ : AlgebraicGoodPrimeEigenform level μ B)
    (i : A →+* B) (j : B →+* Qbar)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ)
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S.bad)
    [P.asIdeal.LiesOver q.asIdeal]
    (hφ : q ∉ φ.form.bad)
    (hHecke : (S.polynomial q).map i = φ.heckePolynomial q hφ)
    (hcomparison : ∀ (w : HeightOneSpectrum (𝓞 A)),
      (S.residueCharacteristic w : 𝓞 K) ∉ q.asIdeal →
      ∀ (ι : Qbar →+* AlgebraicClosure (w.adicCompletion A)),
        ι.comp (j.comp i) =
          (algebraMap (w.adicCompletion A) (AlgebraicClosure (w.adicCompletion A))).comp
            (algebraMap A (w.adicCompletion A)) →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal]
        [Q.LiesOver q.asIdeal] [Q.LiesOver P.asIdeal],
        ι ((cyclotomicField N).val
          (normalizedCyclotomicEulerTrace N P.asIdeal hP m
            (P.specialization ξ hξ.valuation_eq_one.le))) =
          algebraMap (w.adicCompletion A) (AlgebraicClosure (w.adicCompletion A))
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
  obtain ⟨w, hw⟩ := S.exists_place_away_from_prime q.asIdeal
  let M := AlgebraicClosure (w.adicCompletion A)
  let : Algebra A Qbar := (j.comp i).toAlgebra
  let : Algebra A M :=
    ((algebraMap (w.adicCompletion A) M).comp
      (algebraMap A (w.adicCompletion A))).toAlgebra
  let : Algebra.IsAlgebraic A Qbar :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (L := A) (A := Qbar)
  let ι : Qbar →ₐ[A] M := IsAlgClosed.lift
  have hι : ι.toRingHom.comp (j.comp i) =
      (algebraMap (w.adicCompletion A) M).comp
        (algebraMap A (w.adicCompletion A)) := by
    ext a
    exact ι.commutes a
  have : Algebra.IsIntegral (𝓞 (cyclotomicField N)) (𝓞 (AlgebraicClosure K)) :=
    Algebra.IsIntegral.tower_top ℤ
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (AlgebraicClosure K)) P.asIdeal
  let := hQ
  let := hQP
  have : Q.LiesOver q.asIdeal := Ideal.LiesOver.trans Q P.asIdeal q.asIdeal
  exact exists_mccarthyValue_eq_compatibleEigenform_roots N S φ i w j ι.toRingHom hι
    P hP m hm hmN θ hθ ξ hξ q hq hφ hHecke hw Q
    (hcomparison w hw ι.toRingHom hι Q)

end HilbertModularity.Cyclotomic
