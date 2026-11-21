/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCompatibleSystem
public import HilbertModularity.RepresentationTheory.CompatibleSystemPlaces

/-! # The selected compatible polynomial in arbitrary local coefficients

The polynomial fixed by the completion system also computes the same labelled
Tate factor over any local coefficient field. Injectivity at one permissible
completion identifies the two algebraic polynomials. This supplies the local
compatibility step in [TripathiGoswamiRevised, Lemma `labelled-RM-compat`].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
  (E : Type) [Field E] [NumberField E]
  (hE : ∀ a : realCyclotomicField p, ((minpoly ℚ a).map (algebraMap ℚ E)).Splits)
  (σ : realCyclotomicField p →ₐ[ℚ] E)

local instance (w : HeightOneSpectrum (𝓞 E)) :
    NontriviallyNormedField (w.adicCompletion E) :=
  Valued.toNontriviallyNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))

local instance (w : HeightOneSpectrum (𝓞 E)) : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

/-- A polynomial is determined by its realization at all permissible coefficient
places; one such place suffices because the coefficient embedding is injective. -/
theorem primePlusCompatibleSystem_polynomial_eq_of_completion_charpoly
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ (primePlusCompatibleSystem p hp ξ E hE σ).bad)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (R : Polynomial E)
    (hR : ∀ w : HeightOneSpectrum (𝓞 E),
      (NumberField.primeBelow E w : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal →
      (primePlusCompletionAction p hp ξ E hE σ w
        (NumberField.geometricFrobenius (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q)).charpoly =
        R.map (algebraMap E (w.adicCompletion E))) :
    R = (primePlusCompatibleSystem p hp ξ E hE σ).polynomial P := by
  obtain ⟨w, hw⟩ := (primePlusCompatibleSystem p hp ξ E hE σ).exists_place_away_from_prime
    P.asIdeal
  have hw' : (NumberField.primeBelow E w : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal := by
    simpa only [primePlusCompatibleSystem_residueCharacteristic] using hw
  have hs := (primePlusCompatibleSystem p hp ξ E hE σ).frobenius_charpoly
    w P hP P.asIdeal rfl hw Q
  rw [primePlusCompatibleSystem_action] at hs
  exact Polynomial.map_injective (algebraMap E (w.adicCompletion E))
    (algebraMap E (w.adicCompletion E)).injective
    ((hR w hw').symm.trans hs)

/-- The common polynomial of the assembled system computes the native labelled
dual Tate action over every coefficient field with the specified embedding.
Neither a new compatible-system premise nor an equivalence of different
Jacobians is required. -/
theorem primePlusCompatibleSystem_local_charpoly_of_goodReduction
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ (primePlusCompatibleSystem p hp ξ E hE σ).bad)
    (B : CommGrp (Over (Spec (CommRingCat.of
      (P.valuationSubringAtPrime (realCyclotomicField p))))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (e : primePlusFiber p hp ξ ≅ localGenericFiber (realCyclotomicField p) P B)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (L : Type) [Field L] [CharZero L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (j : E →ₐ[ℚ] L) :
    ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
      ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
      (j.comp σ)).toRepresentation.dual
        (NumberField.geometricFrobenius (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q)).charpoly =
      ((primePlusCompatibleSystem p hp ξ E hE σ).polynomial P).map j.toRingHom := by
  let hrm := exists_primePlusFiber_labelled_dual_frobeniusPolynomial
    p hp ξ P B e E hE σ
  let R := hrm.choose
  have hR := hrm.choose_spec
  have heq : R = (primePlusCompatibleSystem p hp ξ E hE σ).polynomial P := by
    apply primePlusCompatibleSystem_polynomial_eq_of_completion_charpoly
      p hp ξ E hE σ P hP Q R
    intro w hw
    rw [primePlusCompletionAction_eq, primePlusCohomologicalAction_charpoly]
    exact hR Q (NumberField.primeBelow E w) (Fact.out) hw (w.adicCompletion E)
      (primePlusCompletionSplits p E hE w) (Algebra.algHom ℚ E (w.adicCompletion E))
  exact (hR Q ℓ (Fact.out) hℓP L hL j).trans
    (congrArg (fun S : Polynomial E => S.map j.toRingHom) heq)

/-- The common polynomial of the assembled system computes the native labelled
dual Tate action over every coefficient field with the specified embedding.
Neither a new compatible-system premise nor an equivalence of different
Jacobians is required. -/
theorem primePlusCompatibleSystem_local_charpoly
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ (primePlusCompatibleSystem p hp ξ E hE σ).bad)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (L : Type) [Field L] [CharZero L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (j : E →ₐ[ℚ] L) :
    ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
      ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
      (j.comp σ)).toRepresentation.dual
        (NumberField.geometricFrobenius (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q)).charpoly =
      ((primePlusCompatibleSystem p hp ξ E hE σ).polynomial P).map j.toRingHom := by
  have hP' : P ∉ primePlusFiberBadPrimes p hp ξ := by
    simpa only [primePlusCompatibleSystem_bad] using hP
  let hm := exists_primePlusFiber_goodReductionModel p hp ξ P hP'
  let B := hm.choose
  let : IsProper B.X.hom := hm.choose_spec.1
  let : Smooth B.X.hom := hm.choose_spec.2.1
  let : GeometricallyConnected B.X.hom := hm.choose_spec.2.2.1
  let e := hm.choose_spec.2.2.2.some
  exact primePlusCompatibleSystem_local_charpoly_of_goodReduction
    p hp ξ E hE σ P hP B e Q ℓ hℓP L hL j

/-- The selected local coordinate action has the polynomial fixed by the
compatible system, with exactly the chosen algebraic coefficient embedding. -/
theorem primePlusCohomologicalAction_compatible_charpoly
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ (primePlusCompatibleSystem p hp ξ E hE σ).bad)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (j : E →ₐ[ℚ] L) :
    (primePlusCohomologicalAction p hp ξ ℓ L hL (j.comp σ)
      (NumberField.geometricFrobenius (realCyclotomicField p)
        (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q)).charpoly =
      ((primePlusCompatibleSystem p hp ξ E hE σ).polynomial P).map j.toRingHom := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] L).injective
  rw [primePlusCohomologicalAction_charpoly]
  exact primePlusCompatibleSystem_local_charpoly p hp ξ E hE σ P hP Q ℓ hℓP L hL j

end HilbertModularity.Hypergeometric
