/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorFinalCoordinates
public import HilbertModularity.NumberTheory.SpectralNormUniformity

/-! # Normalized conductor coefficients with the original uniformity -/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- Spectral normalization preserves the actual completion uniformity. -/
theorem fullConductor_spectralUniformSpace_eq (p : ℕ) [Fact p.Prime] :
    (spectralNorm.normedField ℚ_[p] (FullConductorCompletion p)).toMetricSpace.toUniformSpace =
      (inferInstance : UniformSpace (FullConductorCompletion p)) :=
  spectralNorm.uniformSpace_eq_of_finiteDimensional ℚ_[p] (FullConductorCompletion p)

/-- The normalized norm with the original completion uniformity. -/
@[expose, instance_reducible] def fullConductorCanonicalNormedField (p : ℕ) [Fact p.Prime] :
    NormedField (FullConductorCompletion p) :=
  spectralNorm.normedFieldWithUniformSpace ℚ_[p] (FullConductorCompletion p)

/-- Nontriviality of the normalized field, with the same original scalar data. -/
@[expose, instance_reducible] def fullConductorCanonicalNontriviallyNormedField
    (p : ℕ) [Fact p.Prime] : NontriviallyNormedField (FullConductorCompletion p) :=
  spectralNorm.nontriviallyNormedFieldWithUniformSpace ℚ_[p] (FullConductorCompletion p)

/-- The normalized norm extends the original p-adic coefficient norm. -/
@[expose, instance_reducible] def fullConductorCanonicalNormedAlgebra (p : ℕ) [Fact p.Prime] :
    @NormedAlgebra ℚ_[p] (FullConductorCompletion p) _
      (fullConductorCanonicalNormedField p).toNormedCommRing.toSeminormedCommRing.toSeminormedRing :=
  spectralNorm.normedAlgebraWithUniformSpace ℚ_[p] (FullConductorCompletion p)

section CanonicalNorm
variable (p : ℕ) [Fact p.Prime]
local instance : NormedField (FullConductorCompletion p) := fullConductorCanonicalNormedField p
local instance : NontriviallyNormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNontriviallyNormedField p
local instance : NormedAlgebra ℚ_[p] (FullConductorCompletion p) :=
  fullConductorCanonicalNormedAlgebra p
local instance : CompleteSpace (FullConductorCompletion p) := inferInstance
local instance : IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

/-- The actual covariant coordinate comparison with normalized coefficients
and the original topology used to construct the chosen local system. -/
def chosenConductorDarmonCoordinateEquiv_spectral
    (hp : 5 ≤ p) (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    (chosenConductorPlusCoordinateAction p hp m hm ξ).Equiv
      ((darmonLabelledTateFamily (realCyclotomicField p) p (by omega) p m hm
        (cyclotomicField p) (realCyclotomicNormalClosure_le_full p)
        (primeAboveConductor p) (FullConductorCompletion p)).arithmeticRepresentation
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) := by
  exact chosenConductorDarmonCoordinateEquiv p hp m hm ξ

end CanonicalNorm
end HilbertModularity.Hypergeometric
