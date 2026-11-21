/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricFactors
public import HilbertModularity.Geometry.GroupScheme.HypergeometricScalarConjugate
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficientTensor
public import HilbertModularity.NumberTheory.CyclotomicLocalGalois
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.GeometricPathArithmetic
public import HilbertModularity.Geometry.Etale.GeometricFiberPath
public import HilbertModularity.Geometry.ProjectiveLine.CoordinateRing
public import HilbertModularity.Geometry.ProjectiveLine.FunctionField

/-! # Rank two at arithmetic fibres of the chosen Darmon family

The actual finite étale geometric fibre functors are joined by a geometric
path. Its coefficient-linear Tate transport identifies each labelled generic
fibre with the corresponding arithmetic fibre of the same chosen family.
Thus the rank from [DarmonFibres, Proposition 3.4] persists at every nonsingular
specialization in [TripathiGoswami].
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField
namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
  (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
  (σ : realCyclotomicField N →ₐ[ℚ] L)
  (K : Type) [Field K]
  (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField N))

/-- Every arithmetic fibre of every coefficient-labelled chosen Tate family has rank two. -/
theorem finrank_darmonLabelledTateLocalSystem_at :
    Module.finrank L ((GroupScheme.labelledTateLocalSystem K
      (darmonFamily N hN) p L (realCyclotomicField N) (darmonRealMultiplication N hN) hL σ).obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured (realCyclotomicField N)) x)) = 2 := by
  let e := Scheme.finiteArithmeticFiberIso (RatFunc (realCyclotomicField N)) K
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) x
  exact (GroupScheme.labelledTateGeometricPathIso (RatFunc (realCyclotomicField N)) K e
    (darmonFamily N hN) p L (realCyclotomicField N) (darmonRealMultiplication N hN) hL σ
      ).toLinearEquiv.finrank_eq.symm.trans
    (finrank_darmonLabelledTateLocalSystem N hN p L hL σ)

/-- The actual embedding-labelled native Tate summand of each chosen scheme fibre has rank two. -/
theorem finrank_darmonLabelledTateSummand_at :
    Module.finrank L (GroupScheme.labelledTateSummand K
      (GroupScheme.fiber K (darmonFamily N hN) x).X p (realCyclotomicField N) L hL
      (GroupScheme.fiberPointsAction K (AlgebraicClosure K) (darmonFamily N hN) x
        (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN)) σ) = 2 :=
  (GroupScheme.labelledTateLocalSystemArithmeticFiberIso K (darmonFamily N hN) p L x
    (realCyclotomicField N) (darmonRealMultiplication N hN) hL σ).toLinearEquiv.finrank_eq.symm.trans
    (finrank_darmonLabelledTateLocalSystem_at N hN p L hL σ K x)

end HilbertModularity.Hypergeometric

namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic
variable (p k : ℕ) [Fact p.Prime] (hN : 3 ≤ p ^ (k + 1))

/-- The actual native completed-coefficient Tate module of every chosen arithmetic fibre has rank two. -/
theorem finrank_darmonLocalTateRep_at (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured
      (realCyclotomicField (p ^ (k + 1)))) :
    Module.finrank (RealPrimePowerCompletion p k)
      (GroupScheme.localCoefficientTateRep K (darmonFamily (p ^ (k + 1)) hN) x p k
        (darmonRealMultiplication (p ^ (k + 1)) hN)) = 2 := by
  let τ := realPrimePowerCompletionEmbedding p k
  let hL : ∀ a : realCyclotomicField (p ^ (k + 1)),
      ((minpoly ℚ a).map (algebraMap ℚ (PadicAlgCl p))).Splits :=
    fun _ => IsAlgClosed.splits _
  exact (GroupScheme.finrank_labelledTateSummand_eq_localCoefficientTateRep
    p k (PadicAlgCl p) τ K (darmonFamily (p ^ (k + 1)) hN) x
    (darmonRealMultiplication (p ^ (k + 1)) hN) hL).symm.trans
      (finrank_darmonLabelledTateSummand_at (p ^ (k + 1)) hN p (PadicAlgCl p) hL
        (GroupScheme.localTateCoefficientLabel p k (PadicAlgCl p) τ) K x)

/-- The actual native local Tate representation at every rational nonsingular parameter has rank two. -/
theorem finrank_darmonLocalTateRepresentation (ξ : ProjectiveLine.Parameter ℚ) :
    Module.finrank (RealPrimePowerCompletion p k) (darmonLocalTateRepresentation p k hN ξ) = 2 := by
  unfold darmonLocalTateRepresentation
  have h := finrank_darmonLocalTateRep_at p k hN (realCyclotomicField (p ^ (k + 1)))
    (ProjectiveLine.puncturedPoint (realCyclotomicField (p ^ (k + 1)))
      (darmonRationalParameter (p ^ (k + 1)) ξ))
  with_reducible exact h

/-- Every actual local coefficient conjugate of the chosen Tate representation has rank two. -/
theorem finrank_darmonLocalScalarConjugate (ξ : ProjectiveLine.Parameter ℚ)
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    Module.finrank (RealPrimePowerCompletion p k)
      (darmonLocalScalarConjugate p k hN ξ m hm) = 2 := by
  unfold darmonLocalScalarConjugate
  exact (Rep.finrank_localCoefficientConjugate p k m hm
    (darmonLocalTateRepresentation p k hN ξ)).trans
      (finrank_darmonLocalTateRepresentation p k hN ξ)

/-- The native generic Tate representation of the same chosen prime-power family has rank two. -/
theorem finrank_darmonGenericLocalTateRepresentation :
    Module.finrank (RealPrimePowerCompletion p k)
      (darmonGenericLocalTateRepresentation p k hN) = 2 := by
  unfold darmonGenericLocalTateRepresentation
  have h := finrank_darmonLocalTateRep_at p k hN (RatFunc (realCyclotomicField (p ^ (k + 1))))
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField (p ^ (k + 1))))
  with_reducible exact h

end HilbertModularity.Hypergeometric
