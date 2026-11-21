/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomologyRank
public import HilbertModularity.Geometry.GroupScheme.HypergeometricAbsoluteIrreducibility
public import HilbertModularity.RepresentationTheory.DualIrreducibility
public import HilbertModularity.Geometry.Etale.ArithmeticProjectionKernel
public import HilbertModularity.Hypergeometric.RMComparison

/-! # Absolute irreducibility of the chosen cohomological Darmon family

The transverse cusp generators of [DarmonFibres, Propositions 3.2 and 3.4]
remain transverse under extension of the fixed coefficient embedding.
Duality and geometric paths give the same assertion at every rational base point.
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField CategoryTheory.MonObj
namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]

/-- The chosen cohomological factor is absolutely irreducible on the actual
arithmetic kernel. This is deduced from its simultaneous cusp basis; it is not
an additional hypothesis on the family. -/
theorem darmonCohomologicalFamily_arithmeticKernel_baseChange_isIrreducible
    (M : Type) [Field M] [Algebra L M] [Algebra ℚ_[p] M] [Algebra ℚ M]
    [IsScalarTower ℚ ℚ_[p] M] [IsScalarTower ℚ L M] [IsScalarTower ℚ_[p] L M]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Representation.IsIrreducible (Representation.baseChange M
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ
        (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)).comp
          (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ).ker.subtype)) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  let σ := coefficientEmbeddingAbovePrime N m hm E
    ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L
  let hL := splits_minpoly_above_coefficientPrime N E w L hE
  let x := ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ
  let F := GroupScheme.labelledTateLocalSystem (realCyclotomicField N)
    (darmonFamily N hN) p L (realCyclotomicField N) (darmonRealMultiplication N hN) hL σ
  let k := (Scheme.etaleFundamentalGroupMap
    (ProjectiveLine.puncturedToSpec (realCyclotomicField N)) (realCyclotomicField N) x).ker.subtype
  let ρ := (Scheme.fiberMonodromy (realCyclotomicField N)
    (ProjectiveLine.punctured (realCyclotomicField N)) F x).comp k
  have : FiniteDimensional L (F.obj
      (Scheme.etaleFiberPoint (realCyclotomicField N)
        (ProjectiveLine.punctured (realCyclotomicField N)) x)) :=
    Module.finite_of_finrank_pos (by
      rw [finrank_darmonLabelledTateLocalSystem_at N hN p L hL σ]
      norm_num)
  have : (Representation.baseChange M ρ).IsIrreducible :=
    darmonLabelledMonodromy_at_arithmeticKernel_baseChange_isIrreducible N hN p L hL σ M x
  have hdual := Representation.isIrreducible_dual_baseChange M ρ
  have hk : (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ).ker =
      (Scheme.etaleFundamentalGroupMap (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
        (realCyclotomicField N) x).ker :=
    puncturedArithmeticProjectionHom_ker (realCyclotomicField N) ξ
  unfold puncturedFiberMonodromy
  rw [hk]
  change Representation.IsIrreducible (Representation.baseChange M
    ((Scheme.fiberMonodromy (realCyclotomicField N) _ (ModuleCat.cohDual L F) x).comp k))
  have he := congrArg (fun r => Representation.baseChange M (r.comp k))
    (Scheme.fiberMonodromy_cohDual (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) F x)
  have hd := congrArg (fun r => Representation.baseChange M r)
    (Representation.dual_compHom
      (Scheme.fiberMonodromy (realCyclotomicField N) _ F x) k)
  exact (he.trans hd).symm ▸ hdual

end HilbertModularity.Hypergeometric
