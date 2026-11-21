/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.SkinnerWilesFiniteFieldTrace
public import HilbertModularity.NumberTheory.LocalSpecialization.GoodPrimeDescent

/-! # Finite-field traces at every eligible prime

The exceptional-set argument in [TripathiGoswamiRevised, `thm:intro-main`]
uses that the parameter descends to the base field. The good-unit conditions at
any upper prime then suffice, provided the selected compatible system has no
additional bad primes. The selected-system containment remains an explicit
application hypothesis.
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

/-- One eigenform and one coefficient embedding work at every good-unit prime
away from the conductor. The proof removes the auxiliary exceptional-set premise
using descent of valuations. It requires actual modularity, comparison and trace
inputs, and containment of the chosen system's bad set in the canonical one. -/
theorem exists_mccarthyEigenform_at_goodUnit_primes
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
    (x : K)
    (hbad : S.bad ⊆ LocalSpecialization.badPrimesBelow (K := K)
      (algebraMap K (cyclotomicField N) x) N)
    (htrace :
      ∀ (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
        (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
        (hx : P.GoodUnit (algebraMap K (cyclotomicField N) x))
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
            (P.specialization (algebraMap K (cyclotomicField N) x) hx.valuation_eq_one.le))) =
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
          (hx : P.GoodUnit (algebraMap K (cyclotomicField N) x))
          (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (_hθ : θ ≠ 1)
          (q : HeightOneSpectrum (𝓞 K))
          [P.asIdeal.LiesOver q.asIdeal],
          ∃ (hφ : q ∉ ψ.form.bad) (α β : Qbar),
            (X - C α) * (X - C β) = (ψ.heckePolynomial q hφ).map j ∧
            mccarthyValue N P hP m θ (algebraMap K (cyclotomicField N) x) hx =
              α ^ P.asIdeal.inertiaDeg (𝓞 K) + β ^ P.asIdeal.inertiaDeg (𝓞 K) ∧
            (P.asIdeal.inertiaDeg (𝓞 K) = 1 →
              mccarthyValue N P hP m θ (algebraMap K (cyclotomicField N) x) hx = j (ψ.heckeCoefficient q hφ)) ∧
            (P.asIdeal.inertiaDeg (𝓞 K) = 2 →
              mccarthyValue N P hP m θ (algebraMap K (cyclotomicField N) x) hx =
                j (ψ.heckeCoefficient q hφ) ^ 2 -
                  2 * ((Nat.card (𝓞 K ⧸ q.asIdeal) : Qbar) *
                    j (ψ.centralCoefficient q hφ))) := by
  obtain ⟨B, hB, i, j, hij, level, μ, ψ, hψ, hb, hc, hgood⟩ :=
    exists_mccarthyEigenform_of_skinnerWiles_finiteComparison
      N p ρ L H χ k S σ hcomparison hlocal i₀ m hm hmN
      (algebraMap K (cyclotomicField N) x) htrace
  let := hB
  refine ⟨B, hB, i, j, hij, level, μ, ψ, hψ, hb, hc, ?_⟩
  intro P hP hx θ hθ q _
  exact hgood P hP hx θ hθ q
    (LocalSpecialization.not_mem_of_goodUnit_of_subset_badPrimesBelow
      x N S.bad hbad q P hx hP)

end HilbertModularity.Cyclotomic
