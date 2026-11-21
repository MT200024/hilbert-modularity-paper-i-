/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalCompatibleSystem
public import HilbertModularity.NumberTheory.HilbertModularForms.CovariantHeckeTwistComparison
public import HilbertModularity.RepresentationTheory.FiniteExceptionalPrimes
public import HilbertModularity.RepresentationTheory.FrobeniusSemisimpleDetection

/-! # Uniqueness of a Hilbert eigenform's cohomological action

Two independently constructed actions with the same normalized Hecke trace
and determinant are equivalent at each coefficient place. The finite set in
the detector contains the eigenform's bad primes and the residue-characteristic
primes of both actions. The only literature input is the named Frobenius
semisimple detector [MilneAV, Chapter IV, §3, Lemmas 3.8–3.9].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- Forms at possibly different levels with equal algebraic Hecke polynomials
at their common good primes have equivalent cohomological actions at every
coefficient place. The two finite exceptional sets need not coincide. -/
theorem EigenformCohomologicalActions.equiv_of_heckePolynomial_eq
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    {level' : FiniteLevel F} {μ' : AdditiveQuotientMeasure F}
    {ψ : AlgebraicGoodPrimeEigenform level' μ' E}
    (D : EigenformCohomologicalActions φ) (D' : EigenformCohomologicalActions ψ)
    (hhecke : ∀ q (hφ : q ∉ φ.form.bad) (hψ : q ∉ ψ.form.bad),
      φ.heckePolynomial q hφ = ψ.heckePolynomial q hψ)
    (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((D.action w).Equiv (D'.action w)) := by
  let S := D.toCompatibleSystem
  let T := D'.toCompatibleSystem
  let bad := S.system.comparisonBad T.system w w
  have hgood (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ bad) :
      q ∉ φ.form.bad ∧ q ∉ ψ.form.bad ∧
        (D.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal ∧
        (D'.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal := by
    obtain ⟨hS, hT, _, _, hpS, hpT⟩ :=
      S.system.good_of_not_mem_comparisonBad T.system w w q hq
    exact ⟨by simpa only [S.bad_eq] using hS,
      by simpa only [T.bad_eq] using hT,
      by simpa only [S, D.toCompatibleSystem_residueCharacteristic] using hpS,
      by simpa only [T, D'.toCompatibleSystem_residueCharacteristic] using hpT⟩
  have hDu : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (D.residueCharacteristic w : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : AbsoluteGalois F,
          g ∈ Q.inertia (AbsoluteGalois F) → D.action w g = 1 := by
    intro q hq P _ hP _ Q _ _ g hg
    exact D.unramified w q (hgood q hq).1 P hP
      (hP.symm ▸ (hgood q hq).2.2.1) Q g hg
  have hD'u : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (D.residueCharacteristic w : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : AbsoluteGalois F,
          g ∈ Q.inertia (AbsoluteGalois F) → D'.action w g = 1 := by
    intro q hq P _ hP _ Q _ _ g hg
    exact D'.unramified w q (hgood q hq).2.1 P hP
      (hP.symm ▸ (hgood q hq).2.2.2) Q g hg
  have hpoly : ∀ q, q ∉ bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      (D.residueCharacteristic w : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (D.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (D'.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly := by
    intro q hq P _ hP _ Q _ _
    exact (D.frobenius_charpoly w q (hgood q hq).1 P hP
      (hP.symm ▸ (hgood q hq).2.2.1) Q).trans
      ((congrArg (fun f : Polynomial E => f.map (algebraMap E (w.adicCompletion E)))
        (hhecke q (hgood q hq).1 (hgood q hq).2.1)).trans
      (D'.frobenius_charpoly w q (hgood q hq).2.1 P hP
        (hP.symm ▸ (hgood q hq).2.2.2) Q).symm)
  exact frobenius_semisimple_detection w
    (D.residueCharacteristic w) (D.residueCharacteristic_prime w)
    (D.coefficientPrime w) (D.action w) (D'.action w)
    (D.continuous w) (D'.continuous w) (D.semisimple w) (D'.semisimple w)
    bad (S.system.comparisonBad_finite T.system w w) hDu hD'u hpoly

/-- Matching Hecke polynomials transfer trivial inertia at any prime, including
primes in either form's finite exceptional set. This does not assert that an
unramified prime is outside the exceptional set of the chosen adelic vector. -/
theorem EigenformCohomologicalActions.unramified_of_heckePolynomial_eq
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    {level' : FiniteLevel F} {μ' : AdditiveQuotientMeasure F}
    {ψ : AlgebraicGoodPrimeEigenform level' μ' E}
    (D : EigenformCohomologicalActions φ) (D' : EigenformCohomologicalActions ψ)
    (hhecke : ∀ q (hφ : q ∉ φ.form.bad) (hψ : q ∉ ψ.form.bad),
      φ.heckePolynomial q hφ = ψ.heckePolynomial q hψ)
    (w : HeightOneSpectrum (𝓞 E))
    (Q : Ideal (𝓞 (AlgebraicClosure F)))
    (hu : ∀ g : AbsoluteGalois F,
      g ∈ Q.inertia (AbsoluteGalois F) → D.action w g = 1) :
    ∀ g : AbsoluteGalois F,
      g ∈ Q.inertia (AbsoluteGalois F) → D'.action w g = 1 := by
  obtain ⟨e⟩ := D.equiv_of_heckePolynomial_eq D' hhecke w
  intro g hg
  apply LinearMap.ext
  intro v
  have he := e.toIntertwiningMap.isIntertwining
    (D.action w) (D'.action w) g (e.symm v)
  simpa [hu g hg] using he.symm

/-- The normalized cohomological action of an eigenform is unique up to
equivalence at each fixed coefficient completion. -/
theorem EigenformCohomologicalActions.equiv_at_place
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D D' : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((D.action w).Equiv (D'.action w)) :=
  D.equiv_of_heckePolynomial_eq D' (fun _ _ _ => rfl) w

/-- Tensoring two cohomological actions of the same eigenform by the same
character preserves their equivalence at a fixed coefficient place. -/
def EigenformCohomologicalActions.characterTensorEquiv_at_place
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D D' : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E))
    (χ : AbsoluteGalois F →* (w.adicCompletion E)ˣ) :
    ((Representation.ofCharacter χ).tprod (D.action w)).Equiv
      ((Representation.ofCharacter χ).tprod (D'.action w)) :=
  (Representation.characterTwistTensorEquiv (D.action w) χ).trans
    (((D.equiv_at_place D' w).some.characterTwist χ).trans
      (Representation.characterTwistTensorEquiv (D'.action w) χ).symm)

end HilbertModularity.HilbertModularForms
