/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorWeightTwo
public import HilbertModularity.RepresentationTheory.IrreducibilityReflection

/-! # Native irreducibility from the chosen full-conductor action

A proper native invariant subspace remains proper after extension of the
actual exponent-labelled coefficient map. This removes the independent native
irreducibility hypothesis once the chosen full action is absolutely irreducible.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- Absolute irreducibility of the full labelled integral Tate coordinates
reflects to the original native selected-plus Tate action. No source
irreducibility or comparison with an unrelated fibre is assumed. -/
theorem primePlusCanonicalNative_isIrreducible_of_chosenConductorAbsolute
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (habs : (Representation.baseChange
      (AlgebraicClosure (FullConductorCompletion p))
      ((primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).mapCoefficients
          (chosenConductorNativeMap p m hm).toRingHom)).IsIrreducible) :
    (primePlusTateFieldCoordinateAction p hp ξ
      (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).IsIrreducible := by
  let f := chosenConductorNativeMap p m hm
  let : Algebra (RealPrimePowerCompletion p 0) (FullConductorCompletion p) :=
    f.toAlgebra
  let ρ := primePlusTateFieldCoordinateAction p hp ξ
    (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom
  have hmap : (ρ.mapCoefficients f.toRingHom).IsIrreducible :=
    Representation.isIrreducible_of_baseChange _ habs
  exact Representation.isIrreducible_of_mapCoefficients ρ hmap

section Spectral

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] realFieldAlgebra

local instance fullConductorReflectionNormedField :
    NormedField (FullConductorCompletion p) :=
  spectralNorm.normedField ℚ_[p] (FullConductorCompletion p)

local instance fullConductorReflectionNontriviallyNormedField :
    NontriviallyNormedField (FullConductorCompletion p) :=
  spectralNorm.nontriviallyNormedField ℚ_[p] (FullConductorCompletion p)

local instance (priority := 1000) fullConductorReflectionUniformSpace :
    UniformSpace (FullConductorCompletion p) :=
  (spectralNorm.normedField ℚ_[p]
    (FullConductorCompletion p)).toMetricSpace.toUniformSpace

local instance (priority := 1000) fullConductorReflectionTopology :
    TopologicalSpace (FullConductorCompletion p) :=
  (spectralNorm.normedField ℚ_[p]
    (FullConductorCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace

local instance fullConductorReflectionNormedAlgebra :
    NormedAlgebra ℚ_[p] (FullConductorCompletion p) :=
  spectralNorm.normedAlgebra ℚ_[p] (FullConductorCompletion p)

local instance fullConductorReflectionCompleteSpace :
    CompleteSpace (FullConductorCompletion p) :=
  spectralNorm.completeSpace ℚ_[p] (FullConductorCompletion p)

local instance fullConductorReflectionLocalField :
    IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  fullConductor_isNonarchimedeanLocalField_spectral p

local instance fullConductorReflectionResidueCharP :
    CharP (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) p :=
  NumberField.adicCompletionResidueCharP
    (cyclotomicField p) (primeAboveConductor p) p

/-- The cubic-cusp checklist at spectral full-conductor coefficients needs
only absolute irreducibility of its actual full coordinate action. Native
irreducibility is a consequence of the same action through faithful scalar
extension, and the ordinary rows are constructed by coefficient transport. -/
def chosenConductorCubicWeightTwoInput_spectral_of_fullAbsolute
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (habs : (Representation.baseChange
      (AlgebraicClosure (FullConductorCompletion p))
      ((primePlusTateFieldCoordinateAction p hp
        (darmonRationalParameter p ξ₀)
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).mapCoefficients
          (chosenConductorNativeMap p m hm).toRingHom)).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (chosenConductorPlusCoordinateAction p hp m hm
        (darmonRationalParameter p ξ₀)) (cyclotomicField p) := by
  have hirred := primePlusCanonicalNative_isIrreducible_of_chosenConductorAbsolute
    p hp m hm (darmonRationalParameter p ξ₀) habs
  exact chosenConductorCubicWeightTwoInput_spectral p hp m hm ξ₀
    hξ hA hB hAB hdeep hirred habs

end Spectral

end HilbertModularity.Hypergeometric
