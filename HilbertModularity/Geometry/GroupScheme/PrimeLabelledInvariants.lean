/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCompatibleSystem
public import HilbertModularity.RepresentationTheory.CompatibleInvariants

/-! # Trace and determinant of the selected labelled compatible system

The algebraic values are extracted from the common polynomial, using the same
fixed coefficient field and RM label. These are cohomological dual invariants;
the covariant determinant normalization is in `PrimeLabelledDeterminant`.
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

/-- The trace and determinant at every permissible completion are the images
of the same algebraic coefficients. This is the invariant extraction in
[TripathiGoswamiRevised, Lemma `labelled-RM-compat`]. -/
theorem primePlusCompletion_frobenius_trace_det
    (w : HeightOneSpectrum (𝓞 E))
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ primePlusFiberBadPrimes p hp ξ)
    (hw : (NumberField.primeBelow E w : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    let g := NumberField.geometricFrobenius (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q
    let R := primePlusFrobeniusPolynomial p hp ξ E hE σ P
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (primePlusCompletionAction p hp ξ E hE σ w g) =
          algebraMap E (w.adicCompletion E) (-R.coeff 1) ∧
      (primePlusCompletionAction p hp ξ E hE σ w g).det =
        algebraMap E (w.adicCompletion E) (R.coeff 0) := by
  have hP' : P ∉ (primePlusCompatibleSystem p hp ξ E hE σ).bad := by
    simpa only [primePlusCompatibleSystem_bad] using hP
  have hw' : ((primePlusCompatibleSystem p hp ξ E hE σ).residueCharacteristic w :
      𝓞 (realCyclotomicField p)) ∉ P.asIdeal := by
    simpa only [primePlusCompatibleSystem_residueCharacteristic] using hw
  simpa only [primePlusCompatibleSystem_action, primePlusCompatibleSystem_polynomial]
    using (primePlusCompatibleSystem p hp ξ E hE σ).frobenius_trace_det
      w P hP' P.asIdeal rfl hw' Q

end HilbertModularity.Hypergeometric
