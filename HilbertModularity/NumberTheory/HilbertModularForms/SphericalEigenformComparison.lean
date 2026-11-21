/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SphericalEigenformExistence
public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalCoefficientPromotion
public import HilbertModularity.NumberTheory.HilbertModularForms.AlgebraicHeckePolynomialAfterPromotion
public import HilbertModularity.RepresentationTheory.CompatibleSystemCoefficientExtension

/-! # One eigenform covering every good prime of the compared system

For the final argument of [TripathiGoswamiRevised, `thm:intro-main`],
first promote the supplied local comparison. Trivial inertia then selects a
single spherical replacement whose good set contains that of the original
system. The replacement is chosen before the geometric prime.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F A E : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
  [Field A] [NumberField A] [NormedField E]
  {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] E]
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  {φ : AlgebraicGoodPrimeEigenform level μ A}
  {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- A local comparison supplies one spherical eigenform good at every good
prime of the independent system, with a finite coefficient enlargement.
The conclusion retains the actual form, analytic hypotheses, coefficient
embeddings and the Hecke polynomial at every good prime of the system. No good prime is discarded
because of the residue characteristic of the initial local comparison. -/
theorem CohomologicalRealization.exists_sphericalEigenform_of_localComparison
    (r : CohomologicalRealization φ p E)
    (hbounded : ∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C)
    (hcentral : (Set.range φ.form.central_character).Finite)
    (S : NumberFieldCompatibleSystem F A)
    (σ : Representation E (AbsoluteGalois F) V) (e : σ.Equiv r.action)
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (S.polynomial q).map r.coefficientEmbedding) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (i : A →+* B) (level' : FiniteLevel F)
        (ψ : AlgebraicGoodPrimeEigenform level' μ B),
        B.val.toRingHom.comp i = φ.complexEmbedding ∧
        ψ.complexEmbedding = B.val.toRingHom ∧
        ψ.form.central_character = φ.form.central_character ∧
        (∃ C : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ C) ∧
        (Set.range ψ.form.central_character).Finite ∧
        (∀ q (hφ : q ∉ φ.form.bad) (hψ : q ∉ ψ.form.bad),
          (φ.heckePolynomial q hφ).map i = ψ.heckePolynomial q hψ) ∧
        ∀ q, q ∉ S.bad →
          ∃ hψ : q ∉ ψ.form.bad, (S.polynomial q).map i = ψ.heckePolynomial q hψ := by
  obtain ⟨D⟩ := exists_eigenformCohomologicalActions φ hbounded hcentral
  obtain ⟨B, hB, i, level', ψ, hi, hψ, hc, hb, hh, hu⟩ :=
    exists_sphericalEigenform φ hbounded hcentral D
  let := hB
  refine ⟨B, hB, i, level', ψ, hi, hψ, hc, hb, ?_, hh, ?_⟩
  · simpa only [hc] using hcentral
  · intro q hq
    let P := q.asIdeal
    have : P.IsMaximal := q.isMaximal
    obtain ⟨w, hwD, hwS⟩ := D.exists_common_place_away_from_prime S P
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 (AlgebraicClosure F)) P
    let := hQ
    let := hQP
    obtain ⟨ew⟩ := r.promote_localComparison S D.toCompatibleSystem σ e hlocal w
    have ew' : (S.action w).Equiv (D.action w) := by
      simpa only [D.toCompatibleSystem_action] using ew
    have hunram : ∀ g : AbsoluteGalois F,
        g ∈ Q.inertia (AbsoluteGalois F) → D.action w g = 1 := by
      intro g hg
      have hsg := S.unramified w q hq P rfl hwS Q g hg
      apply LinearMap.ext
      intro v
      have he := ew'.toIntertwiningMap.isIntertwining
        (S.action w) (D.action w) g (ew'.symm v)
      simpa [hsg] using he.symm
    obtain ⟨hgood, hpoly⟩ := hu q w P rfl hwD Q hunram
    refine ⟨hgood, hpoly hgood (S.polynomial q) ?_⟩
    exact (ew'.charpoly_eq _).symm.trans (S.frobenius_charpoly w q hq P rfl hwS Q)

/-- The local comparison may use a different number field from the original
system. Construct its coefficient extension along `iA`, then choose the single
spherical eigenform. The output polynomials retain the composite coefficient
embedding; the original geometric exceptional set is unchanged. -/
theorem CohomologicalRealization.exists_sphericalEigenform_of_mapped_localComparison
    {A₀ : Type*} [Field A₀] [NumberField A₀]
    (r : CohomologicalRealization φ p E)
    (hbounded : ∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C)
    (hcentral : (Set.range φ.form.central_character).Finite)
    (S : NumberFieldCompatibleSystem F A₀) (iA : A₀ →+* A)
    (σ : Representation E (AbsoluteGalois F) V) (e : σ.Equiv r.action)
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (S.polynomial q).map (r.coefficientEmbedding.comp iA)) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (i : A →+* B) (level' : FiniteLevel F)
        (ψ : AlgebraicGoodPrimeEigenform level' μ B),
        B.val.toRingHom.comp i = φ.complexEmbedding ∧
        ψ.complexEmbedding = B.val.toRingHom ∧
        ψ.form.central_character = φ.form.central_character ∧
        (∃ C : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ C) ∧
        (Set.range ψ.form.central_character).Finite ∧
        (∀ q (hφ : q ∉ φ.form.bad) (hψ : q ∉ ψ.form.bad),
          (φ.heckePolynomial q hφ).map i = ψ.heckePolynomial q hψ) ∧
        ∀ q, q ∉ S.bad →
          ∃ hψ : q ∉ ψ.form.bad,
            (S.polynomial q).map (i.comp iA) = ψ.heckePolynomial q hψ := by
  let : Algebra A₀ A := iA.toAlgebra
  have hlocal' : ∀ q, q ∉ (S.extendCoefficients (L := A)).bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          ((S.extendCoefficients (L := A)).polynomial q).map r.coefficientEmbedding := by
    intro q hq P _ hP hp Q _ _
    simpa only [NumberFieldCompatibleSystem.extendCoefficients_polynomial,
      Polynomial.map_map, RingHom.algebraMap_toAlgebra] using hlocal q
        (by simpa only [NumberFieldCompatibleSystem.extendCoefficients_bad] using hq)
        P hP hp Q
  obtain ⟨B, hB, i, level', ψ, hi, hψ, hc, hb, hf, hh, hg⟩ :=
    r.exists_sphericalEigenform_of_localComparison hbounded hcentral
      (S.extendCoefficients (L := A)) σ e hlocal'
  let := hB
  refine ⟨B, hB, i, level', ψ, hi, hψ, hc, hb, hf, hh, ?_⟩
  intro q hq
  obtain ⟨hψq, hp⟩ := hg q
    (by simpa only [NumberFieldCompatibleSystem.extendCoefficients_bad] using hq)
  refine ⟨hψq, ?_⟩
  simpa only [NumberFieldCompatibleSystem.extendCoefficients_polynomial,
    Polynomial.map_map, RingHom.algebraMap_toAlgebra] using hp

end HilbertModularity.HilbertModularForms
