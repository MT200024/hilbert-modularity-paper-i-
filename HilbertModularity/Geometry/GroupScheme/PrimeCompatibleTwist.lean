/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCompatibleLocalComparison
public import HilbertModularity.RepresentationTheory.CompatibleSystemTwist

/-! # The selected character-twisted polynomial in local coefficients

The scalar twist of the selected plus Jacobian action has the common polynomial
of the assembled twisted system. The character and coefficient embedding remain
explicit; this does not identify that action with the Euler realization.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

/-- At every prime good for both inputs, an arbitrary local realization of the
selected character twist has the same algebraic Frobenius polynomial as the
assembled system. This is the local comparison used in
[TripathiGoswamiRevised, Theorem `RMgeneral` and Lemma `promotion`]. -/
theorem primePlusCohomologicalAction_twist_compatible_charpoly
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type) [Field E] [NumberField E]
    (hE : ∀ a : realCyclotomicField p, ((minpoly ℚ a).map (algebraMap ℚ E)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] E)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) E)
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ ((primePlusCompatibleSystem p hp ξ E hE σ).characterTwist χ).bad)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (j : E →ₐ[ℚ] L) :
    ((primePlusCohomologicalAction p hp ξ ℓ L hL (j.comp σ)).characterTwist
      ((Units.map j.toRingHom.toMonoidHom).comp χ.toMonoidHom)
      (NumberField.geometricFrobenius (realCyclotomicField p)
        (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q)).charpoly =
      (((primePlusCompatibleSystem p hp ξ E hE σ).characterTwist χ).polynomial P).map
        j.toRingHom := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] L).injective
  have hgood : P ∉ (primePlusCompatibleSystem p hp ξ E hE σ).bad ∧ P ∉ χ.bad := by
    simpa only [NumberFieldCompatibleSystem.characterTwist_bad, Set.mem_union, not_or]
      using hP
  let ρ := primePlusCohomologicalAction p hp ξ ℓ L hL (j.comp σ)
  let χL := (Units.map j.toRingHom.toMonoidHom).comp χ.toMonoidHom
  let g := NumberField.geometricFrobenius (realCyclotomicField p)
    (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q
  have hρ := primePlusCohomologicalAction_compatible_charpoly
    p hp ξ E hE σ P hgood.1 Q ℓ hℓP L hL j
  have hχ : (χL g : L) = j (χ.frobeniusValue P : E) := by
    rw [χ.frobeniusValue_eq P hgood.2 Q]
    rfl
  rw [NumberFieldCompatibleSystem.characterTwist_polynomial]
  exact ((Representation.characterTwistTensorEquiv ρ χL).charpoly_eq g).symm.trans
    (Representation.charpoly_characterTensor_eq_map_scaleRoots j.toRingHom ρ χL g
      ((primePlusCompatibleSystem p hp ξ E hE σ).polynomial P)
      (χ.frobeniusValue P : E) hρ hχ)

end HilbertModularity.Hypergeometric
