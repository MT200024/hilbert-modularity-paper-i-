/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.RealMultiplicationPairing

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricExistence
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Cyclotomic

/-! # Coefficient factors of the selected prime plus Jacobian

The same pointed plus Jacobian selected in `PrimeHypergeometricExistence` supplies
the integral real multiplication and the generic tensor-Tate base triple. Its
labelled factors are taken from that family's Tate local system, not from a
second choice of Darmon's abelian scheme. See [DarmonFibres, Section 3,
Example 3 and Propositions 3.2 and 3.4] and [TripathiGoswami, the prime-level
plus family following Lemma `DO-m-independence`].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- The selected plus family's geometric tensor-Tate basis, at every
realization prime, with one fixed choice of the three inertia generators. -/
def primePlusTensorTateTriple : PrimePlusTensorTateTriple p
    (primePlusFamily p hp) (primePlusRealMultiplication p hp)
    (primePlusData p hp).multiplication_finite
    (primePlusData p hp).multiplication_etale :=
  (primePlusData p hp).tensorTateTriple

/-- The exponent-labelled Tate local system of the selected pointed plus
Jacobian. The parameter `m` changes the coefficient embedding, not the family. -/
def primePlusLabelledTateFamily (K : Type) [Field K]
    (m : ℕ) (hm : m.Coprime p)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L] :
    Scheme.EtaleLocalSystem K (ProjectiveLine.punctured (realCyclotomicField p)) L := by
  letI : NeZero p := ⟨by omega⟩
  exact labelledTateFamilyAtPrime K (primePlusFamily p hp) p p m hm E hE w L
    (primePlusRealMultiplication p hp)

/-- The selected family's local system uses the fixed exponent-labelled
Tate construction; this equation is its public definitional interface. -/
theorem primePlusLabelledTateFamily_eq_labelled (K : Type) [Field K]
    (m : ℕ) (hm : m.Coprime p)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L] :
    primePlusLabelledTateFamily p hp K m hm E hE w L =
      labelledTateFamilyAtPrime K (primePlusFamily p hp) p p m hm E hE w L
        (primePlusRealMultiplication p hp) := (rfl)

/-- At every nonsingular parameter, the labelled arithmetic action is the
idempotent summand of the native Tate module of the same selected Jacobian. -/
def primePlusLabelledTateFamily_arithmeticEquiv (K : Type) [Field K]
    (m : ℕ) (hm : m.Coprime p)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p)) :
    Representation.Equiv
      ((primePlusLabelledTateFamily p hp K m hm E hE w L).arithmeticRepresentation x)
      (GroupScheme.labelledTateSubrepresentation K
        (GroupScheme.fiber K (primePlusFamily p hp) x).X p
        (realCyclotomicField p) L
        (splits_minpoly_above_coefficientPrime p E w L hE)
        (GroupScheme.fiberPointsAction K (AlgebraicClosure K)
          (primePlusFamily p hp) x (𝓞 (realCyclotomicField p))
          (primePlusRealMultiplication p hp))
        (GroupScheme.fiberPointsAction_realized K (AlgebraicClosure K)
          (primePlusFamily p hp) x (𝓞 (realCyclotomicField p))
          (primePlusRealMultiplication p hp))
        (coefficientEmbeddingAbovePrime p m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
          w L)).toRepresentation := by
  letI : NeZero p := ⟨by omega⟩
  exact labelledTateFamilyAtPrime_arithmeticEquiv K (primePlusFamily p hp) p p m hm
    E hE w L (primePlusRealMultiplication p hp) x

/-- Arithmetic specialization in the endomorphism-labelled native API,
with the same selected family, fibre and coefficient embedding. -/
def primePlusLabelledTateFamily_arithmeticEquivEndomorphism (K : Type) [Field K] [CharZero K]
    (m : ℕ) (hm : m.Coprime p)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[p] L]
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p)) :
    ((primePlusLabelledTateFamily p hp K m hm E hE w L).arithmeticRepresentation x).Equiv
      ((endomorphismLabelledTate K (fiber K (primePlusFamily p hp) x)
        p (realCyclotomicField p) L (splits_minpoly_above_coefficientPrime p E w L hE)
        ((fiberEndomorphismMap K (primePlusFamily p hp) x).comp
          (primePlusRealMultiplication p hp))
        (coefficientEmbeddingAbovePrime p m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE) w L)
      ).toRepresentation) := by
  unfold endomorphismLabelledTate
  exact primePlusLabelledTateFamily_arithmeticEquiv p hp K m hm E hE w L x

end HilbertModularity.Hypergeometric
