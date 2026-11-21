/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.SpectralNormTopology
public import HilbertModularity.NumberTheory.CyclotomicLocalField

/-! # A normalized norm on the actual conductor completion

The native adic completion carries its discrete-valuation norm. For the
Skinner–Wiles coefficient field we use the spectral norm extending the
canonical `ℚₚ` norm. Its topology is the original local-field topology.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField TensorProduct

namespace HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime]

/-- The exponent-one prime-power parameter is the original conductor in
the fixed real cyclotomic field construction. -/
theorem realCyclotomicField_primePower_zero :
    realCyclotomicField (p ^ (0 + 1)) = realCyclotomicField p := by
  simp

/-- The prime-power completion at exponent one and the conductor
completion are the two canonical tensor realizations of the same field. -/
def realPrimePowerZeroCompletionEquiv :
    RealPrimePowerCompletion p 0 ≃ₐ[ℚ_[p]] RealCompletion p := by
  let e := Algebra.TensorProduct.congr
    (AlgEquiv.refl : ℚ_[p] ≃ₐ[ℚ_[p]] ℚ_[p])
    (IntermediateField.equivOfEq (realCyclotomicField_primePower_zero p))
  exact (realPrimePowerCompletionTensorEquiv p 0).symm.trans
    (e.trans (realCompletionTensorEquiv p))

/-- The canonical completion equivalence preserves the original real-field
coefficient embedding, including its exponent-zero field transport. -/
theorem realPrimePowerZeroCompletionEquiv_global
    (a : realCyclotomicField (p ^ (0 + 1))) :
    realPrimePowerZeroCompletionEquiv p
      (algebraMap (realCyclotomicField (p ^ (0 + 1)))
        (RealPrimePowerCompletion p 0) a) =
      algebraMap (realCyclotomicField p) (RealCompletion p)
        (IntermediateField.equivOfEq (realCyclotomicField_primePower_zero p) a) := by
  have ha : (realPrimePowerCompletionTensorEquiv p 0).symm
      (algebraMap (realCyclotomicField (p ^ (0 + 1)))
        (RealPrimePowerCompletion p 0) a) = (1 : ℚ_[p]) ⊗ₜ[ℚ] a := by
    apply (realPrimePowerCompletionTensorEquiv p 0).injective
    simp
  unfold realPrimePowerZeroCompletionEquiv
  simp only [AlgEquiv.trans_apply, ha]
  simp

/-- The normalized spectral norm agrees topologically with the native real
conductor completion. -/
theorem realConductor_spectralTopology_eq :
    (spectralNorm.normedField ℚ_[p] (RealCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (RealCompletion p)) := by
  exact spectralNorm.topology_eq_of_finiteDimensional ℚ_[p] (RealCompletion p)

/-- The real conductor completion retains its local-field structure under
the normalized spectral norm used by the lifting theorem. -/
theorem realConductor_isNonarchimedeanLocalField_spectral :
    letI : NormedField (RealCompletion p) :=
      spectralNorm.normedField ℚ_[p] (RealCompletion p)
    letI : TopologicalSpace (RealCompletion p) :=
      (spectralNorm.normedField ℚ_[p]
        (RealCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace
    IsNonarchimedeanLocalField (RealCompletion p) := by
  let : NormedField (RealCompletion p) :=
    spectralNorm.normedField ℚ_[p] (RealCompletion p)
  let : TopologicalSpace (RealCompletion p) :=
    (spectralNorm.normedField ℚ_[p]
      (RealCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace
  rw [realConductor_spectralTopology_eq p]
  exact NumberField.isNonarchimedeanLocalField_padicCompletion
    (realCyclotomicField p) (realPrimeAboveConductor p) p

/-- The actual full cyclotomic coefficient field at its conductor prime. -/
abbrev FullConductorAdicCompletion :=
  (primeAboveConductor p).adicCompletion (cyclotomicField p)

/-- The spectral norm gives the same topology as the native adic completion
topology on this finite `ℚₚ` extension. -/
theorem fullConductor_spectralTopology_eq :
    (spectralNorm.normedField ℚ_[p]
      (FullConductorAdicCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (FullConductorAdicCompletion p)) := by
  exact spectralNorm.topology_eq_of_finiteDimensional ℚ_[p]
    (FullConductorAdicCompletion p)

/-- With the normalized spectral norm, the canonical `ℚₚ` embedding is
continuous for the same local-field topology. This also fixes the exact
`NormedAlgebra` instance used by downstream lifting theorems. -/
theorem continuous_fullConductor_padicMap_spectral :
    letI : NormedField (FullConductorAdicCompletion p) :=
      spectralNorm.normedField ℚ_[p] (FullConductorAdicCompletion p)
    letI : TopologicalSpace (FullConductorAdicCompletion p) :=
      (spectralNorm.normedField ℚ_[p]
        (FullConductorAdicCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace
    letI : NormedAlgebra ℚ_[p] (FullConductorAdicCompletion p) :=
      spectralNorm.normedAlgebra ℚ_[p] (FullConductorAdicCompletion p)
    Continuous (NumberField.padicCompletionMap p (cyclotomicField p)
      (primeAboveConductor p)) := by
  let : NormedField (FullConductorAdicCompletion p) :=
    spectralNorm.normedField ℚ_[p] (FullConductorAdicCompletion p)
  let : TopologicalSpace (FullConductorAdicCompletion p) :=
    (spectralNorm.normedField ℚ_[p]
      (FullConductorAdicCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedAlgebra ℚ_[p] (FullConductorAdicCompletion p) :=
    spectralNorm.normedAlgebra ℚ_[p] (FullConductorAdicCompletion p)
  rw [fullConductor_spectralTopology_eq p]
  exact NumberField.continuous_padicCompletionMap p
    (cyclotomicField p) (primeAboveConductor p)

/-- The same underlying completion remains a nonarchimedean local field
after normalizing its norm. Its valuation and residue field are unchanged. -/
theorem fullConductor_isNonarchimedeanLocalField_spectral :
    letI : NormedField (FullConductorAdicCompletion p) :=
      spectralNorm.normedField ℚ_[p] (FullConductorAdicCompletion p)
    letI : TopologicalSpace (FullConductorAdicCompletion p) :=
      (spectralNorm.normedField ℚ_[p]
        (FullConductorAdicCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace
    IsNonarchimedeanLocalField (FullConductorAdicCompletion p) := by
  let : NormedField (FullConductorAdicCompletion p) :=
    spectralNorm.normedField ℚ_[p] (FullConductorAdicCompletion p)
  let : TopologicalSpace (FullConductorAdicCompletion p) :=
    (spectralNorm.normedField ℚ_[p]
      (FullConductorAdicCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace
  rw [fullConductor_spectralTopology_eq p]
  exact NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

end HilbertModularity.Cyclotomic
