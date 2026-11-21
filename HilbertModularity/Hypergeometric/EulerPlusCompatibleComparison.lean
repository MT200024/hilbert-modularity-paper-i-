/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationSamePlaceComparison
public import HilbertModularity.Geometry.GroupScheme.PrimeCompatibleTwist
public import HilbertModularity.RepresentationTheory.CompatibleSystemCofiniteComparison

/-! # Promoting a fixed Euler–plus comparison to every coefficient place

The common algebraic coefficient field and finite character are fixed before
the target place. Equality at one local realization determines the common
polynomials outside its residue characteristic, hence all semisimple actions.
This is the promotion deduction in [TripathiGoswamiRevised,
Theorem `thm:RMgeneral` and Lemma `lem:promotion`].
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- A fixed local Euler–plus character comparison promotes to every place
of the common number field, including places above two. Both compatible
systems are constructed from the actual chosen geometric families. -/
theorem chosenEuler_equiv_twistedPlus_at_all_places_of_localComparison
    (N m : ℕ) [NeZero N] [Fact N.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (A : Type) [Field A] [NumberField A] [Algebra (cyclotomicField N) A]
    (hA : ∀ a : realCyclotomicField N,
      ((minpoly ℚ a).map (algebraMap ℚ A)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] A)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField N) A)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [FiniteDimensional ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ_[(NumberField.primeBelow (cyclotomicField N) w)]
      (w.adicCompletion (cyclotomicField N)) L]
    [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[(NumberField.primeBelow (cyclotomicField N) w)] L]
    (j : A →ₐ[ℚ] L)
    (hcoeff : j.toRingHom.comp (algebraMap (cyclotomicField N) A) =
      (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
        (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))))
    (hL : ∀ a : realCyclotomicField N,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (e : let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hm hmN
      let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hm hmN
      let ι := j.toRingHom.comp (algebraMap (cyclotomicField N) A)
      ((R.placeDescent N m 𝒞 (NumberField.primeBelow (cyclotomicField N) w)
        L ι).localSystem.arithmeticRepresentation (ProjectiveLine.puncturedPoint _ ξ)).Equiv
        ((primePlusCohomologicalAction N h5 ξ
          (NumberField.primeBelow (cyclotomicField N) w) L hL (j.comp σ)).characterTwist
          ((Units.map j.toRingHom.toMonoidHom).comp χ.toMonoidHom)))
    (v : HeightOneSpectrum (𝓞 A)) :
    Nonempty ((((chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ
      ).extendCoefficients (L := A)).action v).Equiv
      (((primePlusCompatibleSystem N h5 ξ A hA σ).characterTwist χ).action v)) := by
  let S := chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ
  let T := (primePlusCompatibleSystem N h5 ξ A hA σ).characterTwist χ
  apply (S.extendCoefficients (L := A)).equiv_of_polynomial_eq_outside
    T (S.badAt w) (S.badAt_finite w) _ v
  intro q _hS hT hextra
  obtain ⟨hq, hℓ⟩ := S.good_of_not_mem_badAt w q hextra
  obtain ⟨Q, hQ, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (AlgebraicClosure (realCyclotomicField N))) q.asIdeal
  let : Q.IsMaximal := hQ
  let : Q.LiesOver q.asIdeal := hOver
  have hℓ' : (NumberField.primeBelow (cyclotomicField N) w :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal := by
    simpa only [S, chosenCommonEulerCompatibleSystem_eq_common,
      commonEulerCompatibleSystem_residueCharacteristic] using hℓ
  have hEuler := chosenEulerLocalDescent_frobenius_charpoly_extended
    N m ξ hN h5 hm hmN w L
    (j.toRingHom.comp (algebraMap (cyclotomicField N) A)) hcoeff.symm
    A j.toRingHom rfl q hq hℓ Q
  have hPlus := primePlusCohomologicalAction_twist_compatible_charpoly
    N h5 ξ A hA σ χ q hT Q (NumberField.primeBelow (cyclotomicField N) w)
    hℓ' L hL j
  apply Polynomial.map_injective j.toRingHom j.injective
  exact hEuler.symm.trans ((e.charpoly_eq
    (NumberField.geometricFrobenius (realCyclotomicField N)
      (AlgebraicClosure (realCyclotomicField N)) q.asIdeal Q)).trans hPlus)

end HilbertModularity.Hypergeometric
