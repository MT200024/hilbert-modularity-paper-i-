/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.Topology.Algebra.UniformRing

/-! # Maps between adic completions

An inclusion of fraction fields extends continuously to their adic completions
when the chosen prime of the larger Dedekind domain lies over the smaller one.
-/

@[expose] public noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {A K B L : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.IsTorsionFree A B]
  [Field K] [Field L] [Algebra K L]
  [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- The continuous extension of a field inclusion to adic completions at primes
lying over one another. -/
def completionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
        (adicCompletion.equiv K v).toRingHom)

/-- The extended map is continuous for the canonical adic topologies. -/
theorem continuous_completionMap : Continuous (completionMap (K := K) (L := L) v w) := by
  exact (adicCompletion.uniformEquiv L w).symm.continuous.comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.uniformEquiv K v).continuous)

/-- The map of completions extends the original field inclusion. -/
@[simp] theorem completionMap_algebraMap (x : K) :
    completionMap (K := K) (L := L) v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  apply (adicCompletion.equiv L w).injective
  simp only [completionMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, adicCompletion.equiv_apply,
    algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.mapRingHom_apply]
  change UniformSpace.Completion.map
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (↑((WithVal.equiv (v.valuation K)).symm x)) = _
  rw [UniformSpace.Completion.map_coe (uniformContinuous_algebraMap_liesOver K L v w)]
  rfl

/-- The scalar action on completions induced by the extended field inclusion. -/
instance completionAlgebra : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionMap (K := K) (L := L) v w).toAlgebra

/-- The original base field acts compatibly through its completion. -/
instance completionIsScalarTower : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap K (w.adicCompletion L) x =
      completionMap v w (algebraMap K (v.adicCompletion K) x)
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]

/-- The scalar action of the smaller completion is jointly continuous. -/
instance completionContinuousSMul : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul := by
    change Continuous (fun x : v.adicCompletion K × w.adicCompletion L =>
      completionMap v w x.1 * x.2)
    exact ((continuous_completionMap v w).comp continuous_fst).mul continuous_snd

end IsDedekindDomain.HeightOneSpectrum
