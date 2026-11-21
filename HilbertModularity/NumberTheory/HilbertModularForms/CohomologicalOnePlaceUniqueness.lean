/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalActionUniqueness
public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalFrobeniusPolynomial
public import HilbertModularity.NumberTheory.HilbertModularForms.CompatibleSystemOnePlace

/-! # Comparing one-place and all-place eigenform realizations

An independently supplied one-place cohomological realization has the same
geometric-Frobenius polynomial as an all-place eigenform action when their
coefficient embeddings agree. The named Frobenius semisimple detector then
identifies their semisimple actions at the chosen completion. This comparison
keeps the field embedding and residue characteristic explicit.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- A one-place realization and the all-place eigenform action agree at the
same canonical completion, provided the coefficient embedding is the fixed
algebra map and both actions are semisimple. -/
theorem CohomologicalRealization.equiv_eigenformActions_at_place
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] (w.adicCompletion E)]
    (r : CohomologicalRealization φ p (w.adicCompletion E))
    (hp : p = D.residueCharacteristic w)
    (hι : r.coefficientEmbedding = algebraMap E (w.adicCompletion E))
    (hrs : r.action.IsSemisimpleRepresentation) :
    Nonempty (r.action.Equiv (D.action w)) := by
  let S := D.toCompatibleSystem
  let bad := S.system.badAt w
  have hgood (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ bad) :
      q ∉ φ.form.bad ∧ (p : 𝓞 F) ∉ q.asIdeal := by
    obtain ⟨hqgood, hqprime⟩ := S.system.good_of_not_mem_badAt w q hq
    exact ⟨by simpa only [S.bad_eq] using hqgood,
      hp.symm ▸ (by simpa only [S, D.toCompatibleSystem_residueCharacteristic] using hqprime)⟩
  have hru : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : AbsoluteGalois F,
          g ∈ Q.inertia (AbsoluteGalois F) → r.action g = 1 := by
    intro q hq P _ hP hpP Q _ _ g hg
    exact r.unramified q (hgood q hq).1 P hP hpP Q g hg
  have hDu : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : AbsoluteGalois F,
          g ∈ Q.inertia (AbsoluteGalois F) → D.action w g = 1 := by
    intro q hq P _ hP hpP Q _ _ g hg
    exact D.unramified w q (hgood q hq).1 P hP (hp ▸ hpP) Q g hg
  have hpoly : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (r.action (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (D.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly := by
    intro q hq P _ hP hpP Q _ _
    rw [r.frobenius_charpoly q (hgood q hq).1 P hP hpP Q, hι]
    exact (D.frobenius_charpoly w q (hgood q hq).1 P hP (hp ▸ hpP) Q).symm
  exact frobenius_semisimple_detection w p Fact.out
    (hp ▸ D.coefficientPrime w) r.action (D.action w)
    r.continuous (D.continuous w) hrs (D.semisimple w)
    bad (S.system.badAt_finite w) hru hDu hpoly

/-- A finite-character tensor preserves the one-place comparison with the
chosen eigenform action. -/
noncomputable def CohomologicalRealization.characterTensorEquiv_eigenformActions_at_place
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] (w.adicCompletion E)]
    (r : CohomologicalRealization φ p (w.adicCompletion E))
    (hp : p = D.residueCharacteristic w)
    (hι : r.coefficientEmbedding = algebraMap E (w.adicCompletion E))
    (hrs : r.action.IsSemisimpleRepresentation)
    (χ : AbsoluteGalois F →* (w.adicCompletion E)ˣ) :
    ((Representation.ofCharacter χ).tprod r.action).Equiv
      ((Representation.ofCharacter χ).tprod (D.action w)) :=
  (Representation.characterTwistTensorEquiv r.action χ).trans
    (((r.equiv_eigenformActions_at_place D w p hp hι hrs).some.characterTwist χ).trans
      (Representation.characterTwistTensorEquiv (D.action w) χ).symm)

end HilbertModularity.HilbertModularForms
