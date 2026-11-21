/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.CompatibleTraceAtEveryPrime
public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesSphericalComparison

/-! # From the modularity checklist to finite-field Hecke traces

The final deduction of [TripathiGoswamiRevised, `thm:intro-main`]
combines the Skinner--Wiles checklist, the finite arithmetic comparison and the
normalized Euler trace. A single eigenform and a fixed algebraic embedding
are chosen before any good prime. The effective compatible system and its
comparison to the selected geometric family remain explicit inputs.
-/

public noncomputable section

open NumberField IsDedekindDomain Polynomial
open scoped ValuativeRel

namespace HilbertModularity.Cyclotomic

open HilbertModularForms

attribute [local instance] Ideal.Quotient.field

universe u

variable (N : ℕ) [NeZero N]
  {K : Type*} [Field K] [NumberField K]
  [Algebra K (cyclotomicField N)]
  [Algebra (cyclotomicField N) (AlgebraicClosure K)]
  [IsScalarTower K (cyclotomicField N) (AlgebraicClosure K)]
  [IsGalois (cyclotomicField N) (AlgebraicClosure K)]

/-- One actual cuspidal weight-two eigenform supplies the finite-field root,
degree-one and degree-two formulas from the modularity checklist. The fixed
embedding of the original coefficient field is preserved. Neither an initial
modular form nor local auxiliary primes are assumed. The selected-family
checklist, finite comparison and Euler trace are application hypotheses,
not assertions that the original deep-cusp theorem has been completed. -/
theorem exists_mccarthyEigenform_of_skinnerWiles_finiteComparison
    (p : ℕ) [Fact p.Prime]
    {E : Type u} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois K) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    {A : Type*} [Field A] [NumberField A]
    (χ : FiniteAlgebraicGaloisCharacter K A) (k : A →+* E)
    (S : NumberFieldCompatibleSystem K A)
    {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (σ : Representation E (AbsoluteGalois K) V)
    (hcomparison : Nonempty (((Representation.ofCharacter
      ((Units.map k.toMonoidHom).comp χ.toMonoidHom)).tprod ρ.dual).Equiv σ))
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 K) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius K (AlgebraicClosure K) P Q)).charpoly =
          (S.polynomial q).map k)
    (i₀ : A →+* Qbar) (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (ξ : cyclotomicField N)
    (htrace :
      ∀ (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
        (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
        (hξ : P.GoodUnit ξ)
        (q : HeightOneSpectrum (𝓞 K)), q ∉ S.bad →
        ∀ [P.asIdeal.LiesOver q.asIdeal] (w : HeightOneSpectrum (𝓞 A)),
      (S.residueCharacteristic w : 𝓞 K) ∉ q.asIdeal →
      ∀ (ι : Qbar →+* AlgebraicClosure (w.adicCompletion A)),
        ι.comp i₀ =
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
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (i : A →+* B) (j : B →+* Qbar), j.comp i = i₀ ∧
      ∃ (level : FiniteLevel K) (μ : AdditiveQuotientMeasure K)
        (ψ : AlgebraicGoodPrimeEigenform level μ B),
        ψ.complexEmbedding = B.val.toRingHom ∧
        (∃ C : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ C) ∧
        (Set.range ψ.form.central_character).Finite ∧
        ∀ (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
          (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
          (hξ : P.GoodUnit ξ)
          (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (_hθ : θ ≠ 1)
          (q : HeightOneSpectrum (𝓞 K)) (_hq : q ∉ S.bad)
          [P.asIdeal.LiesOver q.asIdeal],
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
  obtain ⟨B, hB, i, level, μ, ψ, hψ, hb, hc, hgood⟩ :=
    exists_sphericalEigenform_of_skinnerWiles_finiteComparison
      p ρ L H χ k S σ hcomparison hlocal
  let := hB
  let : Algebra A B := i.toAlgebra
  let : Algebra A Qbar := i₀.toAlgebra
  let : Algebra.IsAlgebraic A B :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (L := A) (A := B)
  let j : B →ₐ[A] Qbar := IsAlgClosed.lift
  have hj : j.toRingHom.comp i = i₀ := by
    ext a
    exact j.commutes a
  refine ⟨B, hB, i, j.toRingHom, hj, level, μ, ψ, hψ, hb, hc, ?_⟩
  intro P hP hξ θ hθ q hq _
  obtain ⟨hφ, hpoly⟩ := hgood q hq
  refine ⟨hφ, ?_⟩
  apply exists_mccarthyValue_eq_compatibleEigenform_roots_at_good_prime
    N S ψ i j.toRingHom P hP m hm hmN θ hθ ξ hξ q hq hφ hpoly
  intro w hw ι hι Q _ _ _
  exact htrace P hP hξ q hq w hw ι (by simpa only [hj] using hι) Q

end HilbertModularity.Cyclotomic
