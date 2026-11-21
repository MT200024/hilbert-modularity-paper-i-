/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.GoodPrimeEigenform
public import HilbertModularity.NumberTheory.AbsoluteFrobenius

/-! # Galois realizations of Hilbert eigenforms

The algebraic coefficient field mediates between complex Hecke eigenvalues and
their `p`-adic realizations. The Galois action is the cohomological action:
geometric Frobenius has the standard weight-two Hecke trace and determinant.
The determinant includes the central character and the residue cardinality.
See [SkinnerWiles, §4.5] and [src_skinner_hilbert_2009, §1].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- A genuine adelic Hilbert eigenform whose Hecke and central-character values
lie in a specified number field under a chosen complex embedding. -/
structure AlgebraicGoodPrimeEigenform (level : FiniteLevel F)
    (μ : AdditiveQuotientMeasure F) (A : Type*) [Field A] [NumberField A] where
  form : GoodPrimeEigenform level μ
  complexEmbedding : A →+* ℂ
  heckeCoefficient : ∀ q, q ∉ form.bad → A
  heckeCoefficient_spec : ∀ q (hq : q ∉ form.bad),
    complexEmbedding (heckeCoefficient q hq) = form.hecke_value q hq
  centralCoefficient : ∀ q, q ∉ form.bad → A
  centralCoefficient_spec : ∀ q (hq : q ∉ form.bad),
    complexEmbedding (centralCoefficient q hq) =
      (form.central_character
        (adelicDeterminant F (form.hecke_data q hq).element) : ℂ)

/-- The actual absolute Galois group of a number field. -/
abbrev AbsoluteGalois (F : Type*) [Field F] :=
  Gal(AlgebraicClosure F/F)

/-- A rank-two continuous cohomological Galois realization of an algebraic
parallel-weight-two eigenform. The trace and determinant use *geometric*
Frobenius at every good prime away from the realization characteristic.
The choice of a prime of the algebraic closure does not affect these values
because the action is unramified there. -/
structure CohomologicalRealization {level : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} {A : Type*} [Field A] [NumberField A]
    (φ : AlgebraicGoodPrimeEigenform level μ A)
    (p : ℕ) [Fact p.Prime] (E : Type*) [NormedField E]
    [NormedAlgebra ℚ_[p] E] where
  coefficientEmbedding : A →+* E
  action : Representation E (AbsoluteGalois F) (Fin 2 → E)
  continuous : ∀ i j : Fin 2,
    Continuous (fun g : AbsoluteGalois F => action g (Pi.single j 1) i)
  unramified : ∀ q (_hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (_hP : P = q.asIdeal)
    (_hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (g : AbsoluteGalois F),
      g ∈ Q.inertia (AbsoluteGalois F) → action g = 1
  frobenius_trace : ∀ q (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (_hP : P = q.asIdeal)
    (_hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      LinearMap.trace E (Fin 2 → E)
        (action (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
          coefficientEmbedding (φ.heckeCoefficient q hq)
  frobenius_det : ∀ q (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (_hP : P = q.asIdeal)
    (_hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      LinearMap.det
        (action (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
          (Nat.card (𝓞 F ⧸ P) : E) *
            coefficientEmbedding (φ.centralCoefficient q hq)

end HilbertModularity.HilbertModularForms
