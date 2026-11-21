/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerPlusCohomologicalCoordinates
public import Mathlib.RepresentationTheory.Character

/-! # Traces on the same chosen Darmon and native plus factor

The family comparison and the native coordinate comparison preserve the
same exponent label. Their composition identifies the trace used by the
arithmetic Euler comparison with the trace of the actual native RM factor.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (m : ℕ) (hm : m.Coprime p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L]
  [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
  [IsScalarTower ℚ ℚ_[p] L]

/-- Identify the chosen arithmetic cohomological fibre with the original
native RM dual factor of the same selected plus Jacobian. -/
def darmonPrimeCohomologicalEquivNative :
    ((darmonCohomologicalFamily (realCyclotomicField p) p
      (three_le_of_five_le hp) p m hm E hE w L).arithmeticRepresentation
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).Equiv
      ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        p (realCyclotomicField p) L
        (splits_minpoly_above_coefficientPrime p E w L hE)
        (primePlusFiberRealMultiplication p hp ξ)
        (coefficientEmbeddingAbovePrime p m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
          w L)).toRepresentation.dual) :=
  (darmonPrimeCohomologicalEquivPlus p hp m hm ξ E hE w L).trans
    (primePlusCohomologicalActionEquiv p hp ξ p L
      (splits_minpoly_above_coefficientPrime p E w L hE)
      (coefficientEmbeddingAbovePrime p m hm E
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE) w L))

/-- The arithmetic comparison's trace is the trace of the same native
cohomological RM factor, with no choice of ordering or numerical trace assumed.
This is the fixed-label transport in [TripathiGoswamiRevised,
Theorem `thm:RMgeneral` and Example `ex:p5-numerical-check`]. -/
theorem darmonPrimeCohomological_character_eq_native
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p)) :
    ((darmonCohomologicalFamily (realCyclotomicField p) p
      (three_le_of_five_le hp) p m hm E hE w L).arithmeticRepresentation
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).character g =
      ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        p (realCyclotomicField p) L
        (splits_minpoly_above_coefficientPrime p E w L hE)
        (primePlusFiberRealMultiplication p hp ξ)
        (coefficientEmbeddingAbovePrime p m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
          w L)).toRepresentation.dual).character g := by
  exact congrArg (fun f => f g)
    (Representation.char_iso
      (darmonPrimeCohomologicalEquivNative p hp m hm ξ E hE w L))

end HilbertModularity.Hypergeometric
