/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientTopology
public import HilbertModularity.NumberTheory.CyclotomicEmbeddings.Completion
public import HilbertModularity.NumberTheory.PadicCompletion

/-! # Continuous Tate factors at an exponent-labelled coefficient prime

These specialize the single family's coefficient decomposition using the fixed
real-cyclotomic embeddings and the canonical p-adic action through the chosen
coefficient completion, as in [TripathiGoswami].
-/

@[expose] public noncomputable section
open IsDedekindDomain

namespace HilbertModularity.Cyclotomic
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  [Surjective (p • 𝟙 A).hom.hom.hom.left]
  (N m : ℕ) [NeZero N] (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type u) [NontriviallyNormedField L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
  (φ : 𝓞 (realCyclotomicField N) →+* End A)

/-- The exponent-labelled continuous Tate family at the chosen coefficient prime above p. -/
def labelledTateFamilyAtPrime : Scheme.EtaleLocalSystem K S L := by
  let : ContinuousSMul ℚ_[p] L := NumberField.padicCompletionExtensionContinuousSMul p E w L
  exact GroupScheme.labelledTateEtaleLocalSystem K A p L (realCyclotomicField N) φ
    (splits_minpoly_above_coefficientPrime N E w L hE)
    (coefficientEmbeddingAbovePrime N m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L)

/-- Arithmetic specialization uses the same exponent-labelled native Tate summand. -/
def labelledTateFamilyAtPrime_arithmeticEquiv (x : Spec (CommRingCat.of K) ⟶ S) :
    Representation.Equiv ((labelledTateFamilyAtPrime K A p N m hm E hE w L φ).arithmeticRepresentation x)
      (GroupScheme.labelledTateSubrepresentation K (GroupScheme.fiber K A x).X p
        (realCyclotomicField N) L (splits_minpoly_above_coefficientPrime N E w L hE)
        (GroupScheme.fiberPointsAction K (AlgebraicClosure K) A x (𝓞 (realCyclotomicField N)) φ)
        (GroupScheme.fiberPointsAction_realized K (AlgebraicClosure K) A x
          (𝓞 (realCyclotomicField N)) φ)
        (coefficientEmbeddingAbovePrime N m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L)).toRepresentation := by
  let : ContinuousSMul ℚ_[p] L := NumberField.padicCompletionExtensionContinuousSMul p E w L
  exact GroupScheme.labelledTateEtaleLocalSystem_arithmeticEquiv K A p L (realCyclotomicField N) φ
    (splits_minpoly_above_coefficientPrime N E w L hE)
    (coefficientEmbeddingAbovePrime N m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L) x

end HilbertModularity.Cyclotomic
