/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCohomologicalProperties
public import HilbertModularity.RepresentationTheory.FiniteCharacterRamifiedPrimes

/-! # Ramification of the selected plus-Jacobian comparison character

At a good-reduction prime away from the coefficient characteristic, the selected
labelled action is unramified. An unramified representation equivalent to its
finite-character twist therefore forces that character to be unramified.
This is the good-prime step of [TripathiGoswamiRevised, Theorem `RMgeneral`].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

/-- The actual comparison character cannot introduce ramification at a prime
where the selected Jacobian has good reduction and the compared action is
unramified. No exceptional-set certificate for the character is assumed sharp. -/
theorem not_mem_ramifiedPrimes_of_primePlus_comparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type) [Field E] [NumberField E]
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) E)
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ primePlusFiberBadPrimes p hp ξ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L) (j : E →+* L)
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois (realCyclotomicField p)) V)
    (e : ρ.Equiv ((primePlusCohomologicalAction p hp ξ ℓ L hL σ).characterTwist
      ((Units.map j.toMonoidHom).comp χ.toMonoidHom)))
    (hρ : ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
      [Q.IsMaximal] [Q.LiesOver P.asIdeal],
      ∀ g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois (realCyclotomicField p)),
        ρ g = 1) :
    P ∉ χ.ramifiedPrimes := by
  apply χ.not_mem_ramifiedPrimes_of_unramified_comparison P j ρ
    (primePlusCohomologicalAction p hp ξ ℓ L hL σ) e hρ
  intro Q _ _ g hg
  exact primePlusCohomologicalAction_unramified p hp ξ ℓ L hL σ P hP Q hℓP g hg

end HilbertModularity.Hypergeometric
