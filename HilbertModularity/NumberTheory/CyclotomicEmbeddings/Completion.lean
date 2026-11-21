/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicEmbeddings
public import HilbertModularity.FieldTheory.Normal.Closure
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Exponent-labelled embeddings at a coefficient prime

The fixed cyclotomic labels extend to the chosen completion and any further
coefficient extension. Containment of the normal closure supplies the splitting
condition for the primitive coefficient projectors.
-/

@[expose] public noncomputable section
open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Cyclotomic
variable (N m : ℕ) [NeZero N] (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E] (hE : realCyclotomicField N ≤ E)
  (w : HeightOneSpectrum (𝓞 E))

/-- The exponent-labelled coefficient embedding at a specified finite prime of the coefficient field. -/
def coefficientEmbeddingAtPrime : realCyclotomicField N →ₐ[ℚ] w.adicCompletion E :=
  (Algebra.algHom ℚ E (w.adicCompletion E)).comp (coefficientEmbedding N m hm E hE)

/-- The labelled generator retains its exponent after passage to the coefficient completion. -/
@[simp]
theorem coefficientEmbeddingAtPrime_tau_one :
    coefficientEmbeddingAtPrime N m hm E hE w (tau N 1) =
      algebraMap E (w.adicCompletion E) (IntermediateField.inclusion hE (tau N m)) :=
  congrArg (algebraMap E (w.adicCompletion E)) (coefficientEmbedding_tau_one N m hm E hE)

omit hm hE in
/-- A completion of a coefficient field containing the normal closure splits every coefficient polynomial. -/
theorem splits_minpoly_coefficientCompletion
    (h : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (x : realCyclotomicField N) :
    ((minpoly ℚ x).map (algebraMap ℚ (w.adicCompletion E))).Splits := by
  have hs := IntermediateField.splits_minpoly_of_normalClosure_le (realCyclotomicField N) E h x
  simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ E (w.adicCompletion E)] using
    hs.map (algebraMap E (w.adicCompletion E))

variable (L : Type*) [Field L] [Algebra (w.adicCompletion E) L] [Algebra ℚ L]
  [IsScalarTower ℚ (w.adicCompletion E) L]

/-- The same labelled coefficient embedding in a further extension of the chosen completion. -/
def coefficientEmbeddingAbovePrime : realCyclotomicField N →ₐ[ℚ] L :=
  (Algebra.algHom ℚ (w.adicCompletion E) L).comp (coefficientEmbeddingAtPrime N m hm E hE w)

/-- Extending the local coefficient field preserves the chosen exponent label. -/
@[simp]
theorem coefficientEmbeddingAbovePrime_tau_one :
    coefficientEmbeddingAbovePrime N m hm E hE w L (tau N 1) =
      algebraMap (w.adicCompletion E) L
        (algebraMap E (w.adicCompletion E) (IntermediateField.inclusion hE (tau N m))) :=
  congrArg (algebraMap (w.adicCompletion E) L)
    (coefficientEmbeddingAtPrime_tau_one N m hm E hE w)

include w in
omit hm hE in
/-- Every further extension of the chosen completion still splits the coefficient polynomials. -/
theorem splits_minpoly_above_coefficientPrime
    (h : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (x : realCyclotomicField N) :
    ((minpoly ℚ x).map (algebraMap ℚ L)).Splits := by
  have hs := splits_minpoly_coefficientCompletion N E w h x
  simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ (w.adicCompletion E) L] using
    hs.map (algebraMap (w.adicCompletion E) L)

end HilbertModularity.Cyclotomic
