/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCohomologicalCoordinates
public import HilbertModularity.Geometry.GroupScheme.PrimeTateSemisimplicity
public import HilbertModularity.Geometry.GroupScheme.PrimeGoodReduction
public import HilbertModularity.RepresentationTheory.CompatiblePolynomials

/-! # Arithmetic properties of the selected cohomological action

The continuous rank-two coordinates transport the properties of the same
fixed-labelled dual Tate factor; they introduce no new arithmetic premise.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
  (ℓ : ℕ) [Fact ℓ.Prime]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[ℓ] L]
  (hL : ∀ a : realCyclotomicField p,
    ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
  (σ : realCyclotomicField p →ₐ[ℚ] L)

/-- The coordinate action retains semisimplicity of the actual labelled dual. -/
theorem primePlusCohomologicalAction_isSemisimple :
    (primePlusCohomologicalAction p hp ξ ℓ L hL σ).IsSemisimpleRepresentation := by
  with_reducible
    exact (primePlusCohomologicalActionEquiv p hp ξ ℓ L hL σ).isSemisimple_iff.mpr
      (primePlusFiber_labelled_dual_isSemisimple p hp ξ ℓ L hL σ)

/-- The coordinate action is unramified outside the same geometric exceptional
set and its own coefficient characteristic. -/
theorem primePlusCohomologicalAction_unramified
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ primePlusFiberBadPrimes p hp ξ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))
    (hg : g ∈ Q.inertia (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))) :
    primePlusCohomologicalAction p hp ξ ℓ L hL σ g = 1 := by
  with_reducible
    exact (primePlusCohomologicalActionEquiv p hp ξ ℓ L hL σ).apply_eq_one_of g
      (primePlusFiber_labelled_dual_unramified p hp ξ P hP Q ℓ hℓP L hL σ g hg)

/-- An equivariant coordinate change preserves the actual Frobenius polynomial. -/
theorem primePlusCohomologicalAction_charpoly
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p)) :
    (primePlusCohomologicalAction p hp ξ ℓ L hL σ g).charpoly =
      ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toRepresentation.dual g).charpoly := by
  with_reducible
    exact (primePlusCohomologicalActionEquiv p hp ξ ℓ L hL σ).charpoly_eq g

end HilbertModularity.Hypergeometric
