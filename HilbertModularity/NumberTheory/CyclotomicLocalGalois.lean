/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicCompletion
public import HilbertModularity.NumberTheory.PadicGalois
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Local Galois restriction at the real cyclotomic conductor prime

We embed the actual completion into the algebraic p-adic numbers and extend
this embedding to the global algebraic closure. Normal restriction then maps
the local absolute Galois group to the original global Galois group. These are
the local restriction and period-field action used in [TripathiGoswami,
def:DO]. The auxiliary embeddings are choices; the coefficient field and its
place are the actual completion at the unique prime above the conductor.
-/

@[expose] public noncomputable section
namespace HilbertModularity.Cyclotomic

variable (p k : ℕ) [Fact p.Prime]

/-- An algebraic embedding of the actual finite coefficient completion into `Qp`-bar. -/
def realPrimePowerCompletionEmbedding :
    RealPrimePowerCompletion p k →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift

/-- The algebraic embedding is continuous for the actual completion topology. -/
theorem continuous_realPrimePowerCompletionEmbedding :
    Continuous (realPrimePowerCompletionEmbedding p k) :=
  (realPrimePowerCompletionEmbedding p k).toLinearMap.continuous_of_finiteDimensional

/-- The completion is a closed embedded local field inside the algebraic p-adic numbers. -/
theorem isClosedEmbedding_realPrimePowerCompletionEmbedding :
    Topology.IsClosedEmbedding (realPrimePowerCompletionEmbedding p k) :=
  LinearMap.isClosedEmbedding_of_injective
    (f := (realPrimePowerCompletionEmbedding p k).toLinearMap)
    (LinearMap.ker_eq_bot.mpr (realPrimePowerCompletionEmbedding p k).injective)

/-- The chosen completion embedding, as an algebra structure. -/
@[instance_reducible] def realPrimePowerCompletionPadicAlgebra :
    Algebra (RealPrimePowerCompletion p k) (PadicAlgCl p) :=
  (realPrimePowerCompletionEmbedding p k).toAlgebra

attribute [local instance] realPrimePowerCompletionPadicAlgebra

/-- The completion embedding respects the original rational p-adic scalars. -/
theorem realPrimePowerCompletionPadicTower :
    IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k) (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun a => (realPrimePowerCompletionEmbedding p k).commutes a |>.symm

attribute [local instance] realPrimePowerCompletionPadicTower

/-- The global real field embedded through its specified completion. -/
@[instance_reducible] def realPrimePowerPadicAlgebra :
    Algebra (realCyclotomicField (p ^ (k + 1))) (PadicAlgCl p) :=
  ((realPrimePowerCompletionEmbedding p k).toRingHom.comp
    (algebraMap (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k))).toAlgebra

attribute [local instance] realPrimePowerPadicAlgebra

/-- This global embedding factors through the actual completion map. -/
theorem realPrimePowerPadicTower :
    IsScalarTower (realCyclotomicField (p ^ (k + 1)))
      (RealPrimePowerCompletion p k) (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] realPrimePowerPadicTower

/-- Extend the fixed global embedding to the global algebraic closure. -/
def realPrimePowerAlgebraicClosureEmbedding :
    AlgebraicClosure (realCyclotomicField (p ^ (k + 1))) →ₐ[realCyclotomicField (p ^ (k + 1))]
      PadicAlgCl p := by
  letI : Module.IsTorsionFree (realCyclotomicField (p ^ (k + 1))) (PadicAlgCl p) :=
    DivisionSemiring.to_moduleIsTorsionFree
  exact IsAlgClosed.lift

/-- The extended embedding as an algebra structure for normal restriction. -/
@[instance_reducible] def realPrimePowerAlgebraicClosurePadicAlgebra :
    Algebra (AlgebraicClosure (realCyclotomicField (p ^ (k + 1)))) (PadicAlgCl p) :=
  (realPrimePowerAlgebraicClosureEmbedding p k).toAlgebra

attribute [local instance] realPrimePowerAlgebraicClosurePadicAlgebra

/-- The extended embedding agrees with the chosen embedding on the global field. -/
theorem realPrimePowerAlgebraicClosurePadicTower :
    IsScalarTower (realCyclotomicField (p ^ (k + 1)))
      (AlgebraicClosure (realCyclotomicField (p ^ (k + 1)))) (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun a => (realPrimePowerAlgebraicClosureEmbedding p k).commutes a |>.symm

attribute [local instance] realPrimePowerAlgebraicClosurePadicTower

/-- Restriction from the actual local Galois group to the original global Galois group. -/
def realPrimePowerLocalGaloisRestriction :
    Gal(PadicAlgCl p/RealPrimePowerCompletion p k) →*
      Gal(AlgebraicClosure (realCyclotomicField (p ^ (k + 1)))/realCyclotomicField (p ^ (k + 1))) :=
  (AlgEquiv.restrictNormalHom _).comp (AlgEquiv.restrictScalarsHom _)

/-- Restriction is characterized by its action on the embedded global algebraic closure. -/
theorem realPrimePowerLocalGaloisRestriction_commutes
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p k))
    (x : AlgebraicClosure (realCyclotomicField (p ^ (k + 1)))) :
    realPrimePowerAlgebraicClosureEmbedding p k (realPrimePowerLocalGaloisRestriction p k g x) =
      g (realPrimePowerAlgebraicClosureEmbedding p k x) :=
  (g.restrictScalars (realCyclotomicField (p ^ (k + 1)))).restrictNormal_commutes _ x

open IntermediateField in
/-- Local restriction is continuous for the actual Krull topologies. -/
theorem continuous_realPrimePowerLocalGaloisRestriction :
    Continuous (realPrimePowerLocalGaloisRestriction p k) := by
  classical
  let F := realCyclotomicField (p ^ (k + 1))
  let C := RealPrimePowerCompletion p k
  let f := realPrimePowerAlgebraicClosureEmbedding p k
  let : Algebra.IsAlgebraic C (PadicAlgCl p) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) C
  apply continuous_of_continuousAt_one (realPrimePowerLocalGaloisRestriction p k)
  rw [ContinuousAt, map_one]
  refine ((galGroupBasis C (PadicAlgCl p)).nhds_one_hasBasis.tendsto_iff
    (galGroupBasis F (AlgebraicClosure F)).nhds_one_hasBasis).mpr ?_
  rintro _ ⟨_, ⟨L, hL : FiniteDimensional _ _, rfl⟩, rfl⟩
  refine ⟨_, ⟨_, ⟨adjoin C (L.map f), ?_, rfl⟩, rfl⟩, fun g hg x => ?_⟩
  · suffices Algebra.EssFiniteType C (adjoin C (L.map f : Set (PadicAlgCl p))) by
      apply Algebra.finite_of_essFiniteType_of_isAlgebraic
    replace hL : Algebra.EssFiniteType F L := inferInstance
    rw [essFiniteType_iff] at hL ⊢
    obtain ⟨s, rfl⟩ := hL
    use s.image f
    rw [adjoin_map, adjoin_adjoin_right, Finset.coe_image]
  · apply f.injective
    exact (realPrimePowerLocalGaloisRestriction_commutes p k g x).trans
      (hg ⟨f x, subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩)

/-- Each scalar from the chosen coefficient completion acts uniformly continuously. -/
theorem realPrimePowerCompletion_uniformContinuousConstSMul :
    UniformContinuousConstSMul (RealPrimePowerCompletion p k) (PadicAlgCl p) where
  uniformContinuous_const_smul a := by
    simpa only [Algebra.smul_def] using
      (uniformContinuous_mul_left' (algebraMap (RealPrimePowerCompletion p k) (PadicAlgCl p) a))

attribute [local instance] realPrimePowerCompletion_uniformContinuousConstSMul

/-- Completing the chosen algebraic embedding preserves the rational p-adic scalar tower. -/
theorem realPrimePowerCompletionComplexTower :
    IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k) ℂ_[p] := inferInstance

/-- Passing to `Cp` uses the same algebraic completion embedding. -/
@[simp] theorem realPrimePowerCompletionComplex_algebraMap (a : RealPrimePowerCompletion p k) :
    algebraMap (RealPrimePowerCompletion p k) ℂ_[p] a =
      ((realPrimePowerCompletionEmbedding p k a : PadicAlgCl p) : ℂ_[p]) := rfl

/-- The actual p-adic period action of this same local Galois group. -/
def realPrimePowerLocalPeriodAction :
    Gal(PadicAlgCl p/RealPrimePowerCompletion p k) →* Gal(PadicAlgCl p/ℚ_[p]) :=
  AlgEquiv.restrictScalarsHom ℚ_[p]

/-- The period action fixes the image of the actual local base field. -/
theorem realPrimePowerLocalPeriodAction_fixes
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p k)) (a : RealPrimePowerCompletion p k) :
    PadicComplex.galoisEquiv p (realPrimePowerLocalPeriodAction p k g)
        (algebraMap (RealPrimePowerCompletion p k) ℂ_[p] a) =
      algebraMap (RealPrimePowerCompletion p k) ℂ_[p] a := by
  rw [realPrimePowerCompletionComplex_algebraMap, PadicComplex.galoisEquiv_coe]
  exact congrArg (fun z : PadicAlgCl p => (z : ℂ_[p])) (g.commutes a)

open IntermediateField in
/-- Restricting local automorphisms to rational p-adic scalars is Krull-continuous. -/
theorem continuous_realPrimePowerLocalPeriodAction :
    Continuous (realPrimePowerLocalPeriodAction p k) := by
  classical
  let C := RealPrimePowerCompletion p k
  let f := AlgHom.id ℚ_[p] (PadicAlgCl p)
  let : Algebra.IsAlgebraic C (PadicAlgCl p) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) C
  apply continuous_of_continuousAt_one (realPrimePowerLocalPeriodAction p k)
  rw [ContinuousAt, map_one]
  refine ((galGroupBasis C (PadicAlgCl p)).nhds_one_hasBasis.tendsto_iff
    (galGroupBasis ℚ_[p] (PadicAlgCl p)).nhds_one_hasBasis).mpr ?_
  rintro _ ⟨_, ⟨L, hL : FiniteDimensional _ _, rfl⟩, rfl⟩
  refine ⟨_, ⟨_, ⟨adjoin C (L.map f), ?_, rfl⟩, rfl⟩, fun g hg x => ?_⟩
  · suffices Algebra.EssFiniteType C (adjoin C (L.map f : Set (PadicAlgCl p))) by
      apply Algebra.finite_of_essFiniteType_of_isAlgebraic
    replace hL : Algebra.EssFiniteType ℚ_[p] L := inferInstance
    rw [essFiniteType_iff] at hL ⊢
    obtain ⟨s, rfl⟩ := hL
    use s.image f
    rw [adjoin_map, adjoin_adjoin_right, Finset.coe_image]
  · exact hg ⟨f x, subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩

/-- The actual local Galois action on `Cp` is jointly continuous. -/
theorem continuous_realPrimePowerLocalPeriodAction_apply :
    Continuous fun y : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) × ℂ_[p] =>
      PadicComplex.galoisEquiv p (realPrimePowerLocalPeriodAction p k y.1) y.2 := by
  have h : Continuous fun y : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) × ℂ_[p] =>
      (realPrimePowerLocalPeriodAction p k y.1, y.2) :=
    ((continuous_realPrimePowerLocalPeriodAction p k).comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def] using (PadicComplex.continuous_galoisAction p).comp h

end HilbertModularity.Cyclotomic
