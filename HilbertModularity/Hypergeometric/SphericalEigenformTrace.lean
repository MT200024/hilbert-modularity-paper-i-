/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.CompatibleEigenformTrace
public import HilbertModularity.NumberTheory.HilbertModularForms.SphericalEigenformComparison

/-! # One Hilbert eigenform for all compatible finite-field traces

The final deduction of [TripathiGoswamiRevised, `thm:intro-main`]
chooses the form before the good prime. The effective compatible system,
its initial local modularity comparison and the actual normalized Euler
trace comparisons remain explicit. No realization in the enlarged coefficient
field is needed, and the original local residue characteristic excludes no
prime in the conclusion.
-/

public noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace HilbertModularity.Cyclotomic

open HilbertModularForms

attribute [local instance] Ideal.Quotient.field

variable (N : ℕ) [NeZero N]
  {K A E M V : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  [Field A] [NumberField A] [NormedField E] [Field M]
  {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] E]
  [Algebra K (cyclotomicField N)]
  [Algebra (cyclotomicField N) (AlgebraicClosure K)]
  [IsScalarTower K (cyclotomicField N) (AlgebraicClosure K)]
  [IsGalois (cyclotomicField N) (AlgebraicClosure K)]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {level : FiniteLevel K} {μ : AdditiveQuotientMeasure K}
  {φ : AlgebraicGoodPrimeEigenform level μ A}

/-- One actual eigenform gives the McCarthy root formula at every good prime
of the supplied system. The finite coefficient enlargement retains the original
complex embedding and central character. The comparison with the actual Euler
trace is required at the chosen original coefficient completion. The eigenform
and the supplied system may have different coefficient fields; `iA` records
their comparison and is retained in the final embedding. -/
theorem exists_sphericalEigenform_mccarthyValue
    {A₀ : Type*} [Field A₀] [NumberField A₀]
    (r : CohomologicalRealization φ p E)
    (hbounded : ∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C)
    (hcentral : (Set.range φ.form.central_character).Finite)
    (S : NumberFieldCompatibleSystem K A₀) (iA : A₀ →+* A)
    (σ : Representation E (AbsoluteGalois K) V) (e : σ.Equiv r.action)
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 K) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius K (AlgebraicClosure K) P Q)).charpoly =
          (S.polynomial q).map (r.coefficientEmbedding.comp iA)) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (i : A →+* B) (level' : FiniteLevel K)
        (ψ : AlgebraicGoodPrimeEigenform level' μ B),
        B.val.toRingHom.comp i = φ.complexEmbedding ∧
        ψ.complexEmbedding = B.val.toRingHom ∧
        ψ.form.central_character = φ.form.central_character ∧
        (∃ C : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ C) ∧
        (Set.range ψ.form.central_character).Finite ∧
        ∀ (w : HeightOneSpectrum (𝓞 A₀)) [Algebra (w.adicCompletion A₀) M]
          (j : B →+* Qbar) (ι : Qbar →+* M),
          ι.comp (j.comp (i.comp iA)) =
            (algebraMap (w.adicCompletion A₀) M).comp
              (algebraMap A₀ (w.adicCompletion A₀)) →
        ∀ (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
          (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
          (m : ℕ) (_hm : 0 < m) (_hmN : m < N)
          (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (_hθ : θ ≠ 1)
          (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ)
          (q : HeightOneSpectrum (𝓞 K)) (_hq : q ∉ S.bad)
          [P.asIdeal.LiesOver q.asIdeal]
          (_hell : (S.residueCharacteristic w : 𝓞 K) ∉ q.asIdeal)
          (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal]
          [Q.LiesOver q.asIdeal] [Q.LiesOver P.asIdeal]
          (_hcomparison :
            ι ((cyclotomicField N).val
              (normalizedCyclotomicEulerTrace N P.asIdeal hP m
                (P.specialization ξ hξ.valuation_eq_one.le))) =
              algebraMap (w.adicCompletion A₀) M
              (LinearMap.trace (w.adicCompletion A₀) (Fin 2 → w.adicCompletion A₀)
                (S.action w (AlgEquiv.restrictScalarsHom K
                  (NumberField.geometricFrobenius (cyclotomicField N)
                    (AlgebraicClosure K) P.asIdeal Q :
                      AlgebraicClosure K ≃ₐ[cyclotomicField N] AlgebraicClosure K))))),
          ∃ (hφ : q ∉ ψ.form.bad) (α β : Qbar),
            (X - C α) * (X - C β) = (ψ.heckePolynomial q hφ).map j ∧
            mccarthyValue N P hP m θ ξ hξ =
              α ^ P.asIdeal.inertiaDeg (𝓞 K) + β ^ P.asIdeal.inertiaDeg (𝓞 K) ∧
            (P.asIdeal.inertiaDeg (𝓞 K) = 1 →
              mccarthyValue N P hP m θ ξ hξ = j (ψ.heckeCoefficient q hφ)) ∧
            (P.asIdeal.inertiaDeg (𝓞 K) = 2 →
              mccarthyValue N P hP m θ ξ hξ =
                j (ψ.heckeCoefficient q hφ) ^ 2 -
                  2 * ((Nat.card (𝓞 K ⧸ q.asIdeal) : Qbar) *
                    j (ψ.centralCoefficient q hφ))) := by
  obtain ⟨B, hB, i, level', ψ, hi, hψ, hc, hb, hfin, _, hgood⟩ :=
    r.exists_sphericalEigenform_of_mapped_localComparison hbounded hcentral S iA σ e hlocal
  let := hB
  refine ⟨B, hB, i, level', ψ, hi, hψ, hc, hb, hfin, ?_⟩
  intro w _ j ι hι P hP m hm hmN θ hθ ξ hξ q hq _ hell Q _ _ _ hcomparison
  obtain ⟨hψq, hpoly⟩ := hgood q hq
  obtain ⟨α, β, hroots, hvalue, hd1, hd2⟩ :=
    exists_mccarthyValue_eq_compatibleEigenform_roots N S ψ (i.comp iA) w j ι hι
      P hP m hm hmN θ hθ ξ hξ q hq hψq hpoly hell Q hcomparison
  exact ⟨hψq, α, β, hroots, hvalue, hd1, hd2⟩

end HilbertModularity.Cyclotomic
