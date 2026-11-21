/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.GaloisRealization
public import HilbertModularity.RepresentationTheory.CharacterTwist

/-! # Rank-two Galois character twists

The cohomological Frobenius trace and determinant scale by the character and
its square, respectively. This fixes the normalization needed for finite
idele-class twists of Hilbert eigenforms.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

section CharacterTwist

variable {F E : Type*} [Field F] [Field E]

/-- The trace of a rank-two character twist at any Galois element. -/
theorem trace_characterTwist
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (ν : AbsoluteGalois F →* Eˣ) (g : AbsoluteGalois F) :
    LinearMap.trace E (Fin 2 → E) ((ρ.characterTwist ν) g) =
      (ν g : E) * LinearMap.trace E (Fin 2 → E) (ρ g) := by
  change LinearMap.trace E (Fin 2 → E) ((ν g : E) • ρ g) = _
  simp

/-- The determinant of a rank-two character twist at any Galois element. -/
theorem det_characterTwist
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (ν : AbsoluteGalois F →* Eˣ) (g : AbsoluteGalois F) :
    LinearMap.det ((ρ.characterTwist ν) g) =
      (ν g : E) ^ 2 * LinearMap.det (ρ g) := by
  change LinearMap.det ((ν g : E) • ρ g) = _
  simp [LinearMap.det_smul]

end CharacterTwist

section GeometricFrobenius

variable {F E : Type*} [Field F]
variable [NumberField F] [NormedField E]
variable (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] E]

/-- At a good prime the geometric-Frobenius trace of a character twist is
the character value times the algebraic Hecke coefficient. -/
theorem CohomologicalRealization.trace_characterTwist_geometricFrobenius
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    {A : Type*} [Field A] [NumberField A]
    {φ : AlgebraicGoodPrimeEigenform level μ A}
    (r : CohomologicalRealization φ p E)
    (ν : AbsoluteGalois F →* Eˣ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace E (Fin 2 → E)
      ((r.action.characterTwist ν)
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      (ν (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) *
        r.coefficientEmbedding (φ.heckeCoefficient q hq) := by
  rw [trace_characterTwist, r.frobenius_trace q hq P hP hp Q]

/-- At a good prime the geometric-Frobenius determinant of a character
twist is multiplied by the square of the character value. -/
theorem CohomologicalRealization.det_characterTwist_geometricFrobenius
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    {A : Type*} [Field A] [NumberField A]
    {φ : AlgebraicGoodPrimeEigenform level μ A}
    (r : CohomologicalRealization φ p E)
    (ν : AbsoluteGalois F →* Eˣ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.det
      ((r.action.characterTwist ν)
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      (ν (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) ^ 2 *
        ((Nat.card (𝓞 F ⧸ P) : E) *
          r.coefficientEmbedding (φ.centralCoefficient q hq)) := by
  rw [det_characterTwist, r.frobenius_det q hq P hP hp Q]

end GeometricFrobenius

end HilbertModularity.HilbertModularForms
