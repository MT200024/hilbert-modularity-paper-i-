/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorResidueComparison
public import HilbertModularity.Hypergeometric.PrimePlusConductorArithmeticComparison
public import HilbertModularity.Hypergeometric.PrimePlusCanonicalCubicOrdinary

/-! # The chosen full-conductor weight-two lifting action -/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- The fixed-label full-conductor integral Tate coordinates are exactly the
scalar extension of the canonical native integral coordinates. The integer
map in this equality is the same one used by the residue comparison. -/
theorem chosenConductorPlusCoordinateAction_eq_mapNative
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    chosenConductorPlusCoordinateAction p hp m hm ξ =
      (primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).mapCoefficients
          (chosenConductorNativeMap p m hm).toRingHom := by
  rw [chosenConductorPlusCoordinateAction_eq]
  rw [primePlusExtendedNativeIntegerMap_eq,
    ← chosenConductorNativeIntegerMap_eq]
  simpa only [chosenConductorNativeIntegerResidueComparison_integerMap] using
    (primePlusTateFieldCoordinateAction_mapLocalIntegerComparison
      p hp ξ (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom
      (chosenConductorNativeMap p m hm).toRingHom
      (chosenConductorNativeIntegerResidueComparison p m hm))

end HilbertModularity.Hypergeometric

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

section Spectral

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] realFieldAlgebra realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower

local instance chosenNativeResidueCharP :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

local instance fullConductorChosenNormedField : NormedField (FullConductorCompletion p) :=
  spectralNorm.normedField ℚ_[p] (FullConductorCompletion p)

local instance fullConductorChosenNontriviallyNormedField :
    NontriviallyNormedField (FullConductorCompletion p) :=
  spectralNorm.nontriviallyNormedField ℚ_[p] (FullConductorCompletion p)

local instance (priority := 1000) fullConductorChosenUniformSpace :
    UniformSpace (FullConductorCompletion p) :=
  (spectralNorm.normedField ℚ_[p]
    (FullConductorCompletion p)).toMetricSpace.toUniformSpace

local instance (priority := 1000) fullConductorChosenTopology :
    TopologicalSpace (FullConductorCompletion p) :=
  (spectralNorm.normedField ℚ_[p]
    (FullConductorCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace

local instance fullConductorChosenNormedAlgebra :
    NormedAlgebra ℚ_[p] (FullConductorCompletion p) :=
  spectralNorm.normedAlgebra ℚ_[p] (FullConductorCompletion p)

local instance fullConductorChosenCompleteSpace :
    CompleteSpace (FullConductorCompletion p) :=
  spectralNorm.completeSpace ℚ_[p] (FullConductorCompletion p)

local instance fullConductorChosenLocalField :
    IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  fullConductor_isNonarchimedeanLocalField_spectral p

local instance fullConductorChosenResidueCharP :
    CharP (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) p :=
  NumberField.adicCompletionResidueCharP
    (cyclotomicField p) (primeAboveConductor p) p

/-- The fixed exponent-labelled native coefficient map is continuous also
when the full conductor target carries the normalized spectral topology. -/
theorem continuous_chosenConductorNativeMap_spectral
    (m : ℕ) (hm : m.Coprime p) :
    Continuous (chosenConductorNativeMap p m hm) := by
  change @Continuous (RealPrimePowerCompletion p 0) (FullConductorCompletion p)
    (inferInstance : TopologicalSpace (RealPrimePowerCompletion p 0))
    ((spectralNorm.normedField ℚ_[p]
      (FullConductorCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace)
    (chosenConductorNativeMap p m hm)
  rw [fullConductor_spectralTopology_eq p]
  exact continuous_chosenConductorNativeMap p m hm

/-- Any native checklist for the actual selected integral Tate coordinates
extends to the fixed exponent-labelled full conductor action with the
spectral norm. The absolute irreducibility at the target remains the exact
application input required by coefficient extension. -/
def chosenConductorWeightTwoInput_spectral_of_native
    (hp : 5 ≤ p) (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (H : SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom)
      (cyclotomicField p))
    (habs : (Representation.baseChange
      (AlgebraicClosure (FullConductorCompletion p))
      ((primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).mapCoefficients
          (chosenConductorNativeMap p m hm).toRingHom)).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (chosenConductorPlusCoordinateAction p hp m hm ξ)
      (cyclotomicField p) := by
  let f := chosenConductorNativeMap p m hm
  have hf : Continuous f := continuous_chosenConductorNativeMap_spectral p m hm
  have hfp (x : ℚ_[p]) :
      f (algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) x) =
        algebraMap ℚ_[p] (FullConductorCompletion p) x := f.commutes x
  let Hfull := SkinnerWilesWeightTwoInput.mapLocalCoefficients_withOrdinary
    p (cyclotomicField p) H f.toRingHom hf hfp
    (chosenConductorNativeIntegerResidueComparison p m hm) habs
  rw [chosenConductorPlusCoordinateAction_eq_mapNative p hp m hm ξ]
  exact Hfull

/-- At either rational cubic cusp, native lifting data transport along the
actual fixed exponent label to the normalized full conductor action. The
source and target irreducibility hypotheses are kept explicit until the
selected Euler comparison supplies them. All local ordinary rows are
constructed by the generic coefficient-extension theorem. -/
def chosenConductorCubicWeightTwoInput_spectral
    (hp : 5 ≤ p) (m : ℕ) (hm : m.Coprime p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (hirred : (primePlusTateFieldCoordinateAction p hp
      (darmonRationalParameter p ξ₀)
      (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).IsIrreducible)
    (habs : (Representation.baseChange
      (AlgebraicClosure (FullConductorCompletion p))
      ((primePlusTateFieldCoordinateAction p hp
        (darmonRationalParameter p ξ₀)
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).mapCoefficients
          (chosenConductorNativeMap p m hm).toRingHom)).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (chosenConductorPlusCoordinateAction p hp m hm
        (darmonRationalParameter p ξ₀)) (cyclotomicField p) := by
  letI := primePlusCanonicalNativeAlgebra p hp
  let H := primePlusCanonicalCubicSkinnerWilesWeightTwoInput
    p hp ξ₀ hξ hA hB hAB hdeep hirred
  exact chosenConductorWeightTwoInput_spectral_of_native p hp m hm
    (darmonRationalParameter p ξ₀) H habs

end Spectral

end HilbertModularity.Hypergeometric
