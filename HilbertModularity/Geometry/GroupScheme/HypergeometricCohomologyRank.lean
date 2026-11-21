/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomology
public import HilbertModularity.Geometry.GroupScheme.HypergeometricRanks

/-! # Rank of the chosen cohomological Darmon fibres -/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

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

/-- Duality preserves the rank of the fixed coefficient-labelled Darmon fibre.
The rank-two input is [DarmonFibres, Proposition 3.4], already specialized to
this same family and label by `finrank_darmonLabelledTateSummand_at`. -/
theorem finrank_darmonCohomologicalFamily_at
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField N)) :
    Module.finrank L ((darmonCohomologicalFamily K N hN p m hm E hE w L).algebraicFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured (realCyclotomicField N)) x)) = 2 := by
  have hrank := finrank_darmonLabelledTateSummand_at N hN p L
    (splits_minpoly_above_coefficientPrime N E w L hE)
    (coefficientEmbeddingAbovePrime N m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L) K x
  have e := darmonCohomologicalFamilyArithmeticEquiv K N hN p m hm E hE w L x
  refine e.toLinearEquiv.finrank_eq.trans ?_
  have hd := Subspace.dual_finrank_eq (K := L) (V :=
    GroupScheme.labelledTateSummand K (GroupScheme.fiber K (darmonFamily N hN) x).X p
      (realCyclotomicField N) L (splits_minpoly_above_coefficientPrime N E w L hE)
      (GroupScheme.fiberPointsAction K (AlgebraicClosure K) (darmonFamily N hN) x
        (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN))
      (coefficientEmbeddingAbovePrime N m hm E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L))
  exact hd.trans hrank

end HilbertModularity.Hypergeometric
