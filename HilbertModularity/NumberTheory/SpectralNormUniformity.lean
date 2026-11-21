/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.SpectralNormTopology
import Mathlib.Tactic.FastInstance

/-! # Spectral norm with a fixed additive uniform structure -/

public noncomputable section

namespace spectralNorm

variable (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [U : UniformSpace L] [IsUniformAddGroup L] [ContinuousSMul K L] [T2Space L]

/-- The additive uniformity is determined by the vector-space topology. -/
theorem uniformSpace_eq_of_finiteDimensional :
    (spectralNorm.normedField K L).toMetricSpace.toUniformSpace = U := by
  apply IsUniformAddGroup.ext
  · let : NormedField L := spectralNorm.normedField K L
    let : UniformSpace L := (spectralNorm.normedField K L).toMetricSpace.toUniformSpace
    let : TopologicalSpace L :=
      (spectralNorm.normedField K L).toMetricSpace.toUniformSpace.toTopologicalSpace
    infer_instance
  · infer_instance
  · change @nhds L
      ((spectralNorm.normedField K L).toMetricSpace.toUniformSpace.toTopologicalSpace) 0 =
      @nhds L U.toTopologicalSpace 0
    rw [spectralNorm.topology_eq_of_finiteDimensional K L]

/-- Normalize the norm while preserving the given uniform space literally. -/
@[expose, instance_reducible] def normedFieldWithUniformSpace : NormedField L :=
  fast_instance% { spectralNorm.normedField K L with
    toMetricSpace := @MetricSpace.replaceUniformity L U
      (spectralNorm.normedField K L).toMetricSpace
      (congrArg (fun u : UniformSpace L => @uniformity L u)
        (uniformSpace_eq_of_finiteDimensional K L)).symm }

/-- The normalized field remains nontrivially normed. -/
@[expose, instance_reducible] def nontriviallyNormedFieldWithUniformSpace : NontriviallyNormedField L :=
  { normedFieldWithUniformSpace K L with
    non_trivial := by
      change ∃ x : L, 1 < (spectralNorm K L x : ℝ)
      exact (spectralNorm.nontriviallyNormedField K L).non_trivial }

/-- The normalized norm extends the specified base-field norm with the
original algebra map. Its proof does not require a new topology. -/
@[expose, instance_reducible] def normedAlgebraWithUniformSpace :
    @NormedAlgebra K L _ (normedFieldWithUniformSpace K L).toNormedCommRing.toSeminormedCommRing.toSeminormedRing := by
  letI : NormedField L := normedFieldWithUniformSpace K L
  exact { (inferInstance : Algebra K L) with
    norm_smul_le r x := by
      change (spectralNorm K L (r • x) : ℝ) ≤ ‖r‖ * (spectralNorm K L x : ℝ)
      exact (spectralNorm.normedAlgebra K L).norm_smul_le r x }

end spectralNorm
