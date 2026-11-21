/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeLabelledInvariants

/-! # Fixed-label invariants at every good-reduction model

The common algebraic polynomial controls Frobenius, trace and determinant at
all permissible coefficient places. Every actual good model excludes its
prime from the exact bad-reduction set of the selected plus Jacobian.
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

/-- At every actual good-reduction model, geometric Frobenius has the same
algebraic polynomial, trace and determinant under the fixed coefficient
embeddings. The polynomial is defined before the coefficient place is chosen.
This is the cohomological invariant assertion of
[TripathiGoswamiRevised, Lemma `labelled-RM-compat`]. The covariant
cyclotomic ratio is proved separately in `PrimeLabelledDeterminant`. -/
theorem primePlusCompletion_frobeniusInvariants_of_goodReduction
    (w : HeightOneSpectrum (𝓞 E))
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (B : CommGrp (Over (Spec (CommRingCat.of
      (P.valuationSubringAtPrime (realCyclotomicField p))))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (e : primePlusFiber p hp ξ ≅ localGenericFiber (realCyclotomicField p) P B)
    (hw : (NumberField.primeBelow E w : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    let g := NumberField.geometricFrobenius (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q
    let R := primePlusFrobeniusPolynomial p hp ξ E hE σ P
    (primePlusCompletionAction p hp ξ E hE σ w g).charpoly =
        R.map (algebraMap E (w.adicCompletion E)) ∧
      LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
          (primePlusCompletionAction p hp ξ E hE σ w g) =
            algebraMap E (w.adicCompletion E) (-R.coeff 1) ∧
        (primePlusCompletionAction p hp ξ E hE σ w g).det =
          algebraMap E (w.adicCompletion E) (R.coeff 0) := by
  have hP := primePlusFiber_not_mem_badPrimes_of_goodReduction p hp ξ P B e
  refine ⟨?_, primePlusCompletion_frobenius_trace_det p hp ξ E hE σ w P hP hw Q⟩
  have hP' : P ∉ (primePlusCompatibleSystem p hp ξ E hE σ).bad := by
    simpa only [primePlusCompatibleSystem_bad] using hP
  have hw' : ((primePlusCompatibleSystem p hp ξ E hE σ).residueCharacteristic w :
      𝓞 (realCyclotomicField p)) ∉ P.asIdeal := by
    simpa only [primePlusCompatibleSystem_residueCharacteristic] using hw
  simpa only [primePlusCompatibleSystem_action, primePlusCompatibleSystem_polynomial]
    using (primePlusCompatibleSystem p hp ξ E hE σ).frobenius_charpoly
      w P hP' P.asIdeal rfl hw' Q

end HilbertModularity.Hypergeometric
