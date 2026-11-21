/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTwistComparison

/-! # Hecke coefficients after a covariant character twist

The Skinner--Wiles representation is covariant, while the Hilbert eigenform
realization is cohomological. This module transports two chosen cohomological
realizations through a character twist of the common covariant dual, then
compares their Hecke coefficients at geometric Frobenius. See
[SkinnerWiles, §3.3, (3.2)] and [TripathiGoswami, §3].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace Representation.Equiv

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- An equivariance remains equivariant after twisting both actions by the
same scalar character. -/
def characterTwist {ρ : Representation K G V} {σ : Representation K G W}
    (e : ρ.Equiv σ) (ν : G →* Kˣ) :
    (ρ.characterTwist ν).Equiv (σ.characterTwist ν) :=
  .mk e.toLinearEquiv (by
    intro g
    ext v
    change e ((ν g : K) • ρ g v) = (ν g : K) • σ g (e v)
    rw [map_smul]
    congr 1
    exact e.toIntertwiningMap.isIntertwining ρ σ g v)

end Representation.Equiv

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- If an untwisted and a twisted cohomological realization are identified
with the corresponding dual covariant actions, they are themselves related
by the same cohomological character twist. -/
def CohomologicalRealization.characterTwistEquiv_of_covariantDual
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
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (ν : AbsoluteGalois F →* Eˣ)
    (e : ρ.dual.Equiv r.action)
    (e' : (ρ.dual.characterTwist ν).Equiv r'.action) :
    (r.action.characterTwist ν).Equiv r'.action :=
  (e.symm.characterTwist ν).trans e'

/-- The Hecke trace attached to a twisted covariant dual has the exact
geometric-Frobenius character factor in the common coefficient field. -/
theorem CohomologicalRealization.heckeCoefficient_of_covariantDualTwist
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
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (ν : AbsoluteGalois F →* Eˣ)
    (e : ρ.dual.Equiv r.action)
    (e' : (ρ.dual.characterTwist ν).Equiv r'.action)
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ φ.form.bad) (hq' : q ∉ φ'.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    r'.coefficientEmbedding (φ'.heckeCoefficient q hq') =
      (ν (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) *
        r.coefficientEmbedding (φ.heckeCoefficient q hq) :=
  r.heckeCoefficient_of_characterTwistEquiv p r' ν
    (r.characterTwistEquiv_of_covariantDual p r' ρ ν e e')
    q hq hq' P hP hp Q

/-- The central coefficient of the twisted covariant dual has the square
of the same geometric-Frobenius character factor. -/
theorem CohomologicalRealization.centralCoefficient_of_covariantDualTwist
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
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (ν : AbsoluteGalois F →* Eˣ)
    (e : ρ.dual.Equiv r.action)
    (e' : (ρ.dual.characterTwist ν).Equiv r'.action)
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ φ.form.bad) (hq' : q ∉ φ'.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (p : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    r'.coefficientEmbedding (φ'.centralCoefficient q hq') =
      (ν (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) ^ 2 *
        r.coefficientEmbedding (φ.centralCoefficient q hq) :=
  r.centralCoefficient_characterTwistEquiv p r' ν
    (r.characterTwistEquiv_of_covariantDual p r' ρ ν e e')
    q hq hq' P hP hp Q

end HilbertModularity.HilbertModularForms
