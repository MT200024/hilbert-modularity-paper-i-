/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.RealMultiplicationHodgeTate
public import HilbertModularity.Hypergeometric.DarmonWeightComparison
public import HilbertModularity.NumberTheory.RealCyclotomic

/-! # Hodge weights of the actual chosen Darmon cohomological family

The fixed-label arithmetic fibre is the dual Tate factor of the same abelian
variety. The general RM Hodge comparison therefore supplies weights zero and
one at every local label, for every conductor `N ≥ 3` and coprime exponent.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain NumberField.LocalGalois
open scoped NumberField
attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

/-- Apply the standard totally real RM Hodge input to the original arithmetic
fibre, with its exact exponent-labelled coefficient embedding. No primality
assumption on the conductor or exact determinant identity is needed. -/
theorem darmonCohomologicalFamily_labelledHodgeTate
    (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[p] L]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let D := darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L
    let ρ := puncturedFiberCoordinateRepresentation (realCyclotomicField N) L ξ D
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion (realCyclotomicField N)))
        (Representation.restrictScalars ℚ_[p] (ρ.comp (localGaloisRestriction p (realCyclotomicField N) q))))) ∧
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion (realCyclotomicField N) →ₐ[ℚ_[p]] AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion (realCyclotomicField N)))
        (ρ.comp (localGaloisRestriction p (realCyclotomicField N) q)) n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) := by
  let K := realCyclotomicField N
  let D := darmonCohomologicalFamily K N hN p m hm E hE w L
  let x := ProjectiveLine.puncturedPoint K ξ
  let ρ := puncturedFiberCoordinateRepresentation K L ξ D
  let : Smooth (darmonFamily N hN).X.hom :=
    (darmonFamily_smoothOfRelativeDimension N hN).smooth
  let A := GroupScheme.fiber K (darmonFamily N hN) x
  let hL := splits_minpoly_above_coefficientPrime N E w L hE
  let φ := GroupScheme.fiberPointsAction K (AlgebraicClosure K) (darmonFamily N hN) x
    (𝓞 K) (darmonRealMultiplication N hN)
  let hφ := GroupScheme.fiberPointsAction_realized K (AlgebraicClosure K)
    (darmonFamily N hN) x (𝓞 K) (darmonRealMultiplication N hN)
  let σ := coefficientEmbeddingAbovePrime N m hm E
    ((IntermediateField.le_normalClosure K).trans hE) w L
  let V := Fin (Module.finrank L (D.toFunctor.obj (Scheme.etaleFiberPoint K
    (ProjectiveLine.punctured K) x))) → L
  let : IsModuleTopology ℚ_[p] V := isModuleTopologyOfFiniteDimensional
  have eTate : (D.arithmeticRepresentation x).Equiv
      (GroupScheme.labelledDualTateFactor K A.X p K L hL φ hφ σ) := by
    with_reducible
      exact darmonCohomologicalFamilyArithmeticEquiv K N hN p m hm E hE w L x
  let eCoord := (D.coordinateMonodromyEquiv x).symm.compHom
    (Scheme.galoisToEtaleFundamentalGroup K x)
  have hdim : Module.finrank L V = 2 := by
    have hrank := finrank_darmonCohomologicalFamily_at K N hN p m hm E hE w L x
    with_reducible
      exact (D.coordinateMonodromyEquiv x).toLinearEquiv.finrank_eq.symm.trans hrank
  exact GroupScheme.labelledDualTate_hodgeTate_of_totallyReal K A p K inferInstance
    L hL φ hφ σ ρ (eCoord.trans eTate) hdim

end HilbertModularity.Hypergeometric
