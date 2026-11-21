/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem.DualScalarExtension
public import HilbertModularity.Geometry.GroupScheme.HypergeometricFactors
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientDualTopology

/-! # Cohomological factors of the chosen Darmon family

The cohomological family is the continuous contragredient of the one previously
chosen covariant family. Actual arithmetic fibres retain the same exponent
label: coefficient endomorphisms are transposed without inversion. This is the
cohomological RM factor of [TripathiGoswami]. The chosen scheme depends on
the named [DarmonFibres] existence theorem; no étale-cohomology comparison is
asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra
namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

variable (K : Type) [Field K] (N : ℕ) [NeZero N] (hN : 3 ≤ N)
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]

/-- The cohomological factor is the continuous dual of the same chosen labelled Darmon family. -/
def darmonCohomologicalFamily :
    Scheme.EtaleLocalSystem K (ProjectiveLine.punctured (realCyclotomicField N)) L :=
  (darmonLabelledTateFamily K N hN p m hm E hE w L).cohDual

/-- The chosen continuous dual has exactly the same embedding-labelled algebraic dual family. -/
theorem darmonCohomologicalFamily_algebraicFunctor :
    (darmonCohomologicalFamily K N hN p m hm E hE w L).algebraicFunctor =
      GroupScheme.labelledCohomologicalTateLocalSystem K (darmonFamily N hN) p L
        (realCyclotomicField N) (darmonRealMultiplication N hN)
        (splits_minpoly_above_coefficientPrime N E w L hE)
        (coefficientEmbeddingAbovePrime N m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L) := rfl

/-- Every nonsingular arithmetic fibre is the dual of the native factor with the same label. -/
def darmonCohomologicalFamilyArithmeticEquiv
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField N)) :
    Representation.Equiv
      ((darmonCohomologicalFamily K N hN p m hm E hE w L).arithmeticRepresentation x)
      (GroupScheme.labelledDualTateFactor K (GroupScheme.fiber K (darmonFamily N hN) x).X p
        (realCyclotomicField N) L (splits_minpoly_above_coefficientPrime N E w L hE)
        (GroupScheme.fiberPointsAction K (AlgebraicClosure K) (darmonFamily N hN) x
          (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN))
        (GroupScheme.fiberPointsAction_realized K (AlgebraicClosure K) (darmonFamily N hN) x
          (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN))
        (coefficientEmbeddingAbovePrime N m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L)) := by
  let : ContinuousSMul ℚ_[p] L := NumberField.padicCompletionExtensionContinuousSMul p E w L
  exact GroupScheme.labelledCohomologicalTateEtaleLocalSystemArithmeticEquiv K
    (darmonFamily N hN) p L (realCyclotomicField N) (darmonRealMultiplication N hN)
    (splits_minpoly_above_coefficientPrime N E w L hE) x
    (coefficientEmbeddingAbovePrime N m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L)

/-- Restriction of functionals realizes the chosen cohomological family as a quotient of the ambient dual. -/
def darmonCohomologicalFamilyQuotient :
    ModuleCat.cohDual L (GroupScheme.extendedTateLocalSystem K (darmonFamily N hN) p L) ⟶
      (darmonCohomologicalFamily K N hN p m hm E hE w L).algebraicFunctor :=
  GroupScheme.labelledCohomologicalTateLocalSystemQuotient K (darmonFamily N hN) p L
    (realCyclotomicField N) (darmonRealMultiplication N hN)
    (splits_minpoly_above_coefficientPrime N E w L hE)
    (coefficientEmbeddingAbovePrime N m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L)

/-- The actual transposed Darmon coefficient action keeps the same scalar embedding on the dual factor. -/
theorem darmonCohomologicalFamily_scalar_label (a : realCyclotomicField N) :
    ModuleCat.cohDualEndomorphism L
        (GroupScheme.extendedTensorTateLocalSystemAction K (darmonFamily N hN) p L
          (realCyclotomicField N) (darmonRealMultiplication N hN)) ((1 : L) ⊗ₜ[ℚ] a) ≫
        darmonCohomologicalFamilyQuotient K N hN p m hm E hE w L =
      coefficientEmbeddingAbovePrime N m hm E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L a •
        darmonCohomologicalFamilyQuotient K N hN p m hm E hE w L :=
  GroupScheme.numberFieldAction_labelledCohomologicalTateLocalSystem K (darmonFamily N hN) p L
    (realCyclotomicField N) (darmonRealMultiplication N hN)
    (splits_minpoly_above_coefficientPrime N E w L hE)
    (coefficientEmbeddingAbovePrime N m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L) a

/-- At the actual generic geometric point, the cohomological monodromy is the dual of the chosen covariant one. -/
theorem darmonCohomologicalFamily_genericMonodromy :
    Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N))
      (darmonCohomologicalFamily (RatFunc (realCyclotomicField N)) N hN p m hm E hE w L).algebraicFunctor
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) =
        (darmonGenericLabelledTateMonodromy N hN p m hm E hE w L).dual :=
  Scheme.fiberMonodromy_cohDual (RatFunc (realCyclotomicField N))
    (ProjectiveLine.punctured (realCyclotomicField N))
    (darmonLabelledTateFamily (RatFunc (realCyclotomicField N)) N hN p m hm E hE w L).algebraicFunctor
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))

/-- Extending the coefficients of the chosen cohomological family commutes with duality. -/
def darmonCohomologicalFamilyExtendScalarsIso
    (L' : Type) [NontriviallyNormedField L'] [CompleteSpace L']
    [Algebra L L'] [ContinuousSMul L L'] :
    ((darmonCohomologicalFamily K N hN p m hm E hE w L).extendScalars L').toFunctor ≅
      ((darmonLabelledTateFamily K N hN p m hm E hE w L).extendScalars L').cohDual.toFunctor :=
  (darmonLabelledTateFamily K N hN p m hm E hE w L).cohDualExtendScalarsIso L'

/-- The coefficient-extension comparison respects the actual arithmetic fibre action. -/
def darmonCohomologicalFamilyExtendScalarsArithmeticEquiv
    (L' : Type) [NontriviallyNormedField L'] [CompleteSpace L']
    [Algebra L L'] [ContinuousSMul L L']
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField N)) :
    Representation.Equiv
      (((darmonCohomologicalFamily K N hN p m hm E hE w L).extendScalars L').arithmeticRepresentation x)
      (((darmonLabelledTateFamily K N hN p m hm E hE w L).extendScalars L').cohDual.arithmeticRepresentation x) :=
  (darmonLabelledTateFamily K N hN p m hm E hE w L).cohDualExtendScalarsArithmeticEquiv L' x

end HilbertModularity.Hypergeometric
