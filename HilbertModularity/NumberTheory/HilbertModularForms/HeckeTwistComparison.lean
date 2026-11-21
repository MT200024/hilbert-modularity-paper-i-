/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.GaloisTwist

/-! # Hecke coefficients of equivalent Galois twists

If two cohomological realizations are related by a character twist, their
Hecke coefficients at common good primes are related by the character's value
on geometric Frobenius. This is the normalization used after the direct
Skinner--Wiles application in [TripathiGoswami, §3].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- The precise geometric-Frobenius Hecke relation for two actual eigenforms
whose cohomological Galois realizations differ by a character twist. The
coefficient comparison is in the common `p`-adic coefficient field; no choice
of complex embedding or Artin-map convention is suppressed. -/
theorem CohomologicalRealization.heckeCoefficient_of_characterTwistEquiv
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    {A : Type*} [Field A] [NumberField A]
    {φ : AlgebraicGoodPrimeEigenform level μ A}
    (r : CohomologicalRealization φ p E)
    {level' : FiniteLevel F} {μ' : AdditiveQuotientMeasure F}
    {A' : Type*} [Field A'] [NumberField A']
    {φ' : AlgebraicGoodPrimeEigenform level' μ' A'}
    (r' : CohomologicalRealization φ' p E)
    (ν : AbsoluteGalois F →* Eˣ)
    (e : (r.action.characterTwist ν).Equiv r'.action)
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ φ.form.bad) (hq' : q ∉ φ'.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    r'.coefficientEmbedding (φ'.heckeCoefficient q hq') =
      (ν (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) *
        r.coefficientEmbedding (φ.heckeCoefficient q hq) := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  have he : LinearMap.trace E (Fin 2 → E) (r'.action g) =
      LinearMap.trace E (Fin 2 → E) ((r.action.characterTwist ν) g) := by
    have hconj : e.toLinearEquiv.toLinearMap ∘ₗ
        (r.action.characterTwist ν) g ∘ₗ e.toLinearEquiv.symm.toLinearMap =
          r'.action g := by
      apply LinearMap.ext
      intro v
      change e ((r.action.characterTwist ν) g (e.symm v)) = r'.action g v
      simpa using e.toIntertwiningMap.isIntertwining
        (r.action.characterTwist ν) r'.action g (e.symm v)
    rw [← hconj]
    change LinearMap.trace E (Fin 2 → E)
      (e.toLinearEquiv.toLinearMap * (r.action.characterTwist ν) g *
        e.toLinearEquiv.symm.toLinearMap) = _
    rw [LinearMap.trace_mul_comm E
      (e.toLinearEquiv.toLinearMap * (r.action.characterTwist ν) g)
      e.toLinearEquiv.symm.toLinearMap]
    have hunit : e.toLinearEquiv.symm.toLinearMap *
        e.toLinearEquiv.toLinearMap = 1 := by
      apply LinearMap.ext
      intro v
      exact e.symm_apply_apply v
    rw [← mul_assoc, hunit, one_mul]
  calc
    r'.coefficientEmbedding (φ'.heckeCoefficient q hq') =
        LinearMap.trace E (Fin 2 → E) (r'.action g) :=
      (r'.frobenius_trace q hq' P hP hp Q).symm
    _ = LinearMap.trace E (Fin 2 → E) ((r.action.characterTwist ν) g) := he
    _ = (ν g : E) * r.coefficientEmbedding (φ.heckeCoefficient q hq) :=
      r.trace_characterTwist_geometricFrobenius p ν q hq P hP hp Q

/-- The determinant part of the same comparison, with the residue norm left
visible on both sides. Thus the central Hecke coefficient has the expected
square-character factor in the geometric-Frobenius normalization. -/
theorem CohomologicalRealization.centralCoefficient_of_characterTwistEquiv
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    {A : Type*} [Field A] [NumberField A]
    {φ : AlgebraicGoodPrimeEigenform level μ A}
    (r : CohomologicalRealization φ p E)
    {level' : FiniteLevel F} {μ' : AdditiveQuotientMeasure F}
    {A' : Type*} [Field A'] [NumberField A']
    {φ' : AlgebraicGoodPrimeEigenform level' μ' A'}
    (r' : CohomologicalRealization φ' p E)
    (ν : AbsoluteGalois F →* Eˣ)
    (e : (r.action.characterTwist ν).Equiv r'.action)
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ φ.form.bad) (hq' : q ∉ φ'.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (Nat.card (𝓞 F ⧸ P) : E) *
        r'.coefficientEmbedding (φ'.centralCoefficient q hq') =
      (ν (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) ^ 2 *
        ((Nat.card (𝓞 F ⧸ P) : E) *
          r.coefficientEmbedding (φ.centralCoefficient q hq)) := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  have hconj : e.toLinearEquiv.toLinearMap ∘ₗ
      (r.action.characterTwist ν) g ∘ₗ e.toLinearEquiv.symm.toLinearMap =
        r'.action g := by
    apply LinearMap.ext
    intro v
    change e ((r.action.characterTwist ν) g (e.symm v)) = r'.action g v
    simpa using e.toIntertwiningMap.isIntertwining
      (r.action.characterTwist ν) r'.action g (e.symm v)
  calc
    (Nat.card (𝓞 F ⧸ P) : E) *
        r'.coefficientEmbedding (φ'.centralCoefficient q hq') =
      LinearMap.det (r'.action g) :=
        (r'.frobenius_det q hq' P hP hp Q).symm
    _ = LinearMap.det ((r.action.characterTwist ν) g) := by
      rw [← hconj]
      exact LinearMap.det_conj _ e.toLinearEquiv
    _ = (ν g : E) ^ 2 *
        ((Nat.card (𝓞 F ⧸ P) : E) *
          r.coefficientEmbedding (φ.centralCoefficient q hq)) :=
      r.det_characterTwist_geometricFrobenius p ν q hq P hP hp Q

/-- The central Hecke coefficient itself is multiplied by the square of the
geometric-Frobenius character value at common good primes. -/
theorem CohomologicalRealization.centralCoefficient_characterTwistEquiv
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E] [CharZero E]
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    {A : Type*} [Field A] [NumberField A]
    {φ : AlgebraicGoodPrimeEigenform level μ A}
    (r : CohomologicalRealization φ p E)
    {level' : FiniteLevel F} {μ' : AdditiveQuotientMeasure F}
    {A' : Type*} [Field A'] [NumberField A']
    {φ' : AlgebraicGoodPrimeEigenform level' μ' A'}
    (r' : CohomologicalRealization φ' p E)
    (ν : AbsoluteGalois F →* Eˣ)
    (e : (r.action.characterTwist ν).Equiv r'.action)
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ φ.form.bad) (hq' : q ∉ φ'.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    r'.coefficientEmbedding (φ'.centralCoefficient q hq') =
      (ν (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) ^ 2 *
        r.coefficientEmbedding (φ.centralCoefficient q hq) := by
  have hcard : 0 < Nat.card (𝓞 F ⧸ P) := Nat.card_pos
  have hnorm : (Nat.card (𝓞 F ⧸ P) : E) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hcard.ne'
  have h := r.centralCoefficient_of_characterTwistEquiv p r' ν e
    q hq hq' P hP hp Q
  apply (mul_left_cancel₀ hnorm)
  calc
    (Nat.card (𝓞 F ⧸ P) : E) *
        r'.coefficientEmbedding (φ'.centralCoefficient q hq') =
      (ν (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) ^ 2 *
        ((Nat.card (𝓞 F ⧸ P) : E) *
          r.coefficientEmbedding (φ.centralCoefficient q hq)) := h
    _ = (Nat.card (𝓞 F ⧸ P) : E) *
        ((ν (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) ^ 2 *
          r.coefficientEmbedding (φ.centralCoefficient q hq)) := by ring

end HilbertModularity.HilbertModularForms
