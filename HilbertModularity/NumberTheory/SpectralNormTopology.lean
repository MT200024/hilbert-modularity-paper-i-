/- Assembled by AxiomProver. -/

module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Normalizing a finite local coefficient extension

The spectral norm extends the base-field norm. A finite-dimensional Hausdorff
topological vector space has a unique vector-space topology, so replacing an
unnormalized valuation norm by the spectral norm preserves the topology used
by the Galois representations.
-/

public noncomputable section

namespace spectralNorm

/-- Normalizing the norm on a finite extension preserves any Hausdorff
topological vector-space topology already carried by that extension. -/
theorem topology_eq_of_finiteDimensional
    (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [t : TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul K L]
    [T2Space L] :
    (spectralNorm.normedField K L).toMetricSpace.toUniformSpace.toTopologicalSpace = t := by
  have hold : t = moduleTopology K L := by
    let : IsModuleTopology K L := isModuleTopologyOfFiniteDimensional
    exact eq_moduleTopology K L
  let := spectralNorm.normedField K L
  let : TopologicalSpace L :=
    (spectralNorm.normedField K L).toMetricSpace.toUniformSpace.toTopologicalSpace
  let := spectralNorm.normedAlgebra K L
  let : IsModuleTopology K L := isModuleTopologyOfFiniteDimensional
  exact (eq_moduleTopology K L).trans hold.symm

end spectralNorm
