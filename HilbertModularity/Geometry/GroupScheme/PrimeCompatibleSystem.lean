/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCohomologicalProperties
public import HilbertModularity.RepresentationTheory.NumberFieldCompatibleSystem
public import HilbertModularity.NumberTheory.LocalGlobalInertia

/-! # The compatible cohomological system of the selected plus Jacobian

One algebraic coefficient field and one RM embedding are fixed before choosing
coefficient places. The representations use their actual adic completions and
the exceptional geometric set is independent of the coefficient place.
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

include hE in
/-- Splitting of the fixed RM field persists in each coefficient completion. -/
theorem primePlusCompletionSplits (w : HeightOneSpectrum (𝓞 E))
    (a : realCyclotomicField p) :
    ((minpoly ℚ a).map (algebraMap ℚ (w.adicCompletion E))).Splits := by
  simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ E (w.adicCompletion E)]
    using (hE a).map (algebraMap E (w.adicCompletion E))

/-- The actual rank-two cohomological action at a coefficient place. -/
def primePlusCompletionAction (w : HeightOneSpectrum (𝓞 E)) :
    Representation (w.adicCompletion E)
      (HilbertModularForms.AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → w.adicCompletion E) :=
  primePlusCohomologicalAction p hp ξ (NumberField.primeBelow E w) (w.adicCompletion E)
    (primePlusCompletionSplits p E hE w) ((Algebra.algHom ℚ E (w.adicCompletion E)).comp σ)

/-- The completion action retains the selected cohomological coordinates. -/
theorem primePlusCompletionAction_eq (w : HeightOneSpectrum (𝓞 E)) :
    primePlusCompletionAction p hp ξ E hE σ w =
      primePlusCohomologicalAction p hp ξ (NumberField.primeBelow E w)
        (w.adicCompletion E) (primePlusCompletionSplits p E hE w)
        ((Algebra.algHom ℚ E (w.adicCompletion E)).comp σ) := (rfl)

/-- At a good prime one polynomial works at every permissible coefficient place. -/
theorem exists_primePlusCompletion_frobeniusPolynomial
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ primePlusFiberBadPrimes p hp ξ) :
    ∃ R : Polynomial E, ∀ (w : HeightOneSpectrum (𝓞 E)),
      (NumberField.primeBelow E w : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P.asIdeal],
        (primePlusCompletionAction p hp ξ E hE σ w
          (NumberField.geometricFrobenius (realCyclotomicField p)
            (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q)).charpoly =
          R.map (algebraMap E (w.adicCompletion E)) := by
  let hm := exists_primePlusFiber_goodReductionModel p hp ξ P hP
  let B := hm.choose
  let : IsProper B.X.hom := hm.choose_spec.1
  let : Smooth B.X.hom := hm.choose_spec.2.1
  let : GeometricallyConnected B.X.hom := hm.choose_spec.2.2.1
  let e := hm.choose_spec.2.2.2.some
  obtain ⟨R, hR⟩ := exists_primePlusFiber_labelled_dual_frobeniusPolynomial
    p hp ξ P B e E hE σ
  refine ⟨R, ?_⟩
  intro w hw Q _ _
  rw [primePlusCompletionAction, primePlusCohomologicalAction_charpoly]
  exact hR Q (NumberField.primeBelow E w) (Fact.out) hw (w.adicCompletion E)
    (primePlusCompletionSplits p E hE w) (Algebra.algHom ℚ E (w.adicCompletion E))

/-- The common polynomial at a good prime, extended by zero at exceptional primes. -/
def primePlusFrobeniusPolynomial (P : HeightOneSpectrum (𝓞 (realCyclotomicField p))) :
    Polynomial E := by
  classical
  exact if hP : P ∉ primePlusFiberBadPrimes p hp ξ then
    (exists_primePlusCompletion_frobeniusPolynomial p hp ξ E hE σ P hP).choose
  else 0

/-- The selected plus Jacobian, with the original RM label and cohomological
convention, supplies an actual semisimple compatible system. All arithmetic
properties are deductions from the named literature inputs used upstream. -/
def primePlusCompatibleSystem : NumberFieldCompatibleSystem (realCyclotomicField p) E where
  residueCharacteristic := NumberField.primeBelow E
  residueCharacteristic_prime := fun w => (NumberField.primeBelow_prime E w).out
  coefficientPrime := fun w => NumberField.liesOver_primeBelow E w
  action := primePlusCompletionAction p hp ξ E hE σ
  continuous := fun w i j => continuous_primePlusCohomologicalAction_entry
    p hp ξ (NumberField.primeBelow E w) (w.adicCompletion E)
    (primePlusCompletionSplits p E hE w) ((Algebra.algHom ℚ E (w.adicCompletion E)).comp σ) i j
  semisimple := fun w => primePlusCohomologicalAction_isSemisimple
    p hp ξ (NumberField.primeBelow E w) (w.adicCompletion E)
    (primePlusCompletionSplits p E hE w) ((Algebra.algHom ℚ E (w.adicCompletion E)).comp σ)
  bad := primePlusFiberBadPrimes p hp ξ
  bad_finite := primePlusFiberBadPrimes_finite p hp ξ
  polynomial := primePlusFrobeniusPolynomial p hp ξ E hE σ
  unramified := by
    intro w q hq P _ hP hw Q _ _ g hg
    subst P
    exact primePlusCohomologicalAction_unramified p hp ξ (NumberField.primeBelow E w)
      (w.adicCompletion E) (primePlusCompletionSplits p E hE w)
      ((Algebra.algHom ℚ E (w.adicCompletion E)).comp σ) q hq Q hw g hg
  frobenius_charpoly := by
    intro w q hq P _ hP hw Q _ _
    subst P
    dsimp only [primePlusFrobeniusPolynomial]
    rw [dite_eq_left hq]
    exact (exists_primePlusCompletion_frobeniusPolynomial p hp ξ E hE σ q hq).choose_spec
      w hw Q

/-- The system's action is exactly the selected fixed-label cohomological action. -/
theorem primePlusCompatibleSystem_action (w : HeightOneSpectrum (𝓞 E)) :
    (primePlusCompatibleSystem p hp ξ E hE σ).action w =
      primePlusCompletionAction p hp ξ E hE σ w := (rfl)

/-- The assembled system retains the coefficient-independent geometric set. -/
theorem primePlusCompatibleSystem_bad :
    (primePlusCompatibleSystem p hp ξ E hE σ).bad =
      primePlusFiberBadPrimes p hp ξ := (rfl)

/-- Its coefficient characteristic is the rational prime under that place. -/
theorem primePlusCompatibleSystem_residueCharacteristic (w : HeightOneSpectrum (𝓞 E)) :
    (primePlusCompatibleSystem p hp ξ E hE σ).residueCharacteristic w =
      NumberField.primeBelow E w := (rfl)

/-- The system uses the previously constructed common algebraic polynomial. -/
theorem primePlusCompatibleSystem_polynomial
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p))) :
    (primePlusCompatibleSystem p hp ξ E hE σ).polynomial P =
      primePlusFrobeniusPolynomial p hp ξ E hE σ P := (rfl)

end HilbertModularity.Hypergeometric
