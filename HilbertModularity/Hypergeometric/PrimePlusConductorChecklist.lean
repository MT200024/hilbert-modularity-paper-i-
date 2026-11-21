/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusExtendedChecklist
public import HilbertModularity.Hypergeometric.PrimePlusNativeChecklist
public import HilbertModularity.Hypergeometric.PrimePlusOrdinaryCoefficientExtension
public import HilbertModularity.NumberTheory.CyclotomicNormalizedCompletion
public import HilbertModularity.Geometry.GroupScheme.PrimeDarmonLocalSystemComparison
public import HilbertModularity.Geometry.GroupScheme.PrimeLabelledCompatibility

/-! # The selected prime checklist at canonical conductor coefficients

This module assembles the actual real and cyclotomic coefficient maps of the
same selected plus Jacobian. The spectral norm supplies the normalization
required by the weight-two lifting theorem, while the native valuation
integer rings and residue maps remain unchanged.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupScheme IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- A chosen global real coefficient label extends through the canonical
exponent-one prime-power completion. The tensor construction fixes the
`ℚₚ` scalar map and the original global embedding simultaneously. -/
def realPrimePowerZeroMapOfLabel
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
      [IsScalarTower ℚ ℚ_[p] L]
    (σ : realCyclotomicField p →ₐ[ℚ] L) :
    RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] L :=
  (AlgHom.liftEquiv ℚ ℚ_[p] (realCyclotomicField (p ^ (0 + 1))) L
    (σ.comp (IntermediateField.equivOfEq
      (realCyclotomicField_primePower_zero p)))).comp
    (realPrimePowerCompletionTensorEquiv p 0).symm.toAlgHom

/-- The extended local coefficient map restricts to precisely the supplied
global real label, transported across the exponent-one field equality. -/
theorem realPrimePowerZeroMapOfLabel_global
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
      [IsScalarTower ℚ ℚ_[p] L]
    (σ : realCyclotomicField p →ₐ[ℚ] L)
    (x : realCyclotomicField (p ^ (0 + 1))) :
    localTateCoefficientLabel p 0 L (realPrimePowerZeroMapOfLabel p L σ) x =
      σ ((IntermediateField.equivOfEq
        (realCyclotomicField_primePower_zero p)) x) := by
  have hx : (realPrimePowerCompletionTensorEquiv p 0).symm
      (algebraMap (realCyclotomicField (p ^ (0 + 1)))
        (RealPrimePowerCompletion p 0) x) =
      (1 : ℚ_[p]) ⊗ₜ[ℚ] x := by
    apply (realPrimePowerCompletionTensorEquiv p 0).injective
    simp
  change (AlgHom.liftEquiv ℚ ℚ_[p]
      (realCyclotomicField (p ^ (0 + 1))) L
      (σ.comp (IntermediateField.equivOfEq
        (realCyclotomicField_primePower_zero p))))
      ((realPrimePowerCompletionTensorEquiv p 0).symm
        (algebraMap (realCyclotomicField (p ^ (0 + 1)))
          (RealPrimePowerCompletion p 0) x)) = _
  rw [hx]
  simp

/-- Transport a selected labelled Tate factor through equality of the
coefficient field, its integral RM action, and the chosen coefficient label.
The source and target remain factors of the same plus-Jacobian fibre. -/
private def primePlusLabelledTateEquivOfFieldEq
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (x : Spec (CommRingCat.of (realCyclotomicField p)) ⟶
      ProjectiveLine.punctured (realCyclotomicField p))
    (F : IntermediateField ℚ Qbar) [NumberField F]
    (hF : F = realCyclotomicField p)
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
      [IsScalarTower ℚ ℚ_[p] L]
    (hFsplit : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (hRsplit : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (φ : 𝓞 F →+* End (primePlusFamily p hp))
    (hφ : Eq.mp (congrArg (fun F' : IntermediateField ℚ Qbar =>
      𝓞 F' →+* End (primePlusFamily p hp)) hF) φ =
        primePlusRealMultiplication p hp)
    (τ : F →ₐ[ℚ] L) (σ : realCyclotomicField p →ₐ[ℚ] L)
    (hτ : Eq.mp (congrArg (fun F' : IntermediateField ℚ Qbar =>
      F' →ₐ[ℚ] L) hF) τ = σ) :
    ((endomorphismLabelledTate (realCyclotomicField p)
      (fiber (realCyclotomicField p) (primePlusFamily p hp) x)
      p F L hFsplit
      ((fiberEndomorphismMap (realCyclotomicField p)
        (primePlusFamily p hp) x).comp φ) τ).toRepresentation).Equiv
    ((endomorphismLabelledTate (realCyclotomicField p)
      (fiber (realCyclotomicField p) (primePlusFamily p hp) x)
      p (realCyclotomicField p) L hRsplit
      ((fiberEndomorphismMap (realCyclotomicField p)
        (primePlusFamily p hp) x).comp (primePlusRealMultiplication p hp))
      σ).toRepresentation) := by
  cases hF
  cases hφ
  cases hτ
  exact Representation.Equiv.refl _

private theorem transportedAlgHom_comp_equivOfEq
    (F R : IntermediateField ℚ Qbar) (h : F = R)
    (L : Type*) [Field L] [Algebra ℚ L] (σ : R →ₐ[ℚ] L) :
    Eq.mp (congrArg (fun F' : IntermediateField ℚ Qbar =>
      F' →ₐ[ℚ] L) h) (σ.comp (IntermediateField.equivOfEq h)) = σ := by
  cases h
  rfl

private theorem splits_minpoly_of_intermediateField_eq
    (F R : IntermediateField ℚ Qbar) (h : F = R)
    (L : Type*) [Field L] [Algebra ℚ L]
    (hsplit : ∀ a : R, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits) :
    ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits := by
  cases h
  exact hsplit

/-- The canonical real completion is the fraction field of the selected
adic integer ring under its actual integer embedding. This property is used
only at the real completion, never at the larger cyclotomic completion. -/
theorem realConductor_isFractionRing
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    letI : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealCompletion p) :=
      ((𝒪[RealCompletion p]).subtype.comp
        (realPrimeGeneratorAdicIntegersEquiv p hp).toRingHom).toAlgebra
    IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealCompletion p) := by
  let : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealCompletion p) :=
    ((𝒪[RealCompletion p]).subtype.comp
      (realPrimeGeneratorAdicIntegersEquiv p hp).toRingHom).toAlgebra
  apply IsFractionRing.of_ringEquiv_left (realPrimeGeneratorAdicIntegersEquiv p hp)
  intro x
  rfl

/-- Reduction of the selected global real-prime integers agrees with
reduction in the actual native completion. -/
def realConductorAdicResidueEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealCompletion p] ⧸ 𝓂[RealCompletion p]) := by
  rw [span_realPrimeGenerator p (by omega)]
  exact NumberField.adicCompletionResidueEquiv
    (realCyclotomicField p) (realPrimeAboveConductor p)

/-- The global real-prime residue also identifies canonically with the
full cyclotomic completion's residue through the actual extension map. -/
def fullConductorAdicResidueEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) :=
  (realConductorAdicResidueEquiv p hp).trans (realToFullConductorResidueEquiv p)

theorem realCyclotomicNormalClosure_le_full
    (p : ℕ) [Fact p.Prime] :
    IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤
      cyclotomicField p :=
  IntermediateField.normalClosure_le_iff_of_normal.mpr (realCyclotomicField_le p)

/-- The manuscript's fixed exponent label in the actual full cyclotomic
conductor completion. The global real field is embedded through the chosen
cyclotomic place rather than an arbitrary coefficient isomorphism. -/
def chosenConductorRealLabel
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    realCyclotomicField p →ₐ[ℚ]
      (primeAboveConductor p).adicCompletion (cyclotomicField p) :=
  coefficientEmbeddingAtPrime p m hm (cyclotomicField p)
    (realCyclotomicField_le p)
    (primeAboveConductor p)

/-- The selected completion label sends the standard real cyclotomic
generator to the exponent-`m` generator at the actual conductor place. -/
@[simp] theorem chosenConductorRealLabel_tau_one
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    chosenConductorRealLabel p m hm (tau p 1) =
      algebraMap (cyclotomicField p) (FullConductorCompletion p)
        (IntermediateField.inclusion (realCyclotomicField_le p) (tau p m)) :=
  coefficientEmbeddingAtPrime_tau_one p m hm (cyclotomicField p)
    (realCyclotomicField_le p) (primeAboveConductor p)

/-- The above-prime label specializes to the chosen exponent label in the
actual conductor completion. -/
theorem chosenConductorRealLabel_eq_abovePrime
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    chosenConductorRealLabel p m hm =
      coefficientEmbeddingAbovePrime p m hm (cyclotomicField p)
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans
          (realCyclotomicNormalClosure_le_full p))
        (primeAboveConductor p) (FullConductorCompletion p) := by
  ext x
  simp [chosenConductorRealLabel, coefficientEmbeddingAbovePrime,
    coefficientEmbeddingAtPrime, Algebra.algHom]

/-- The corresponding `ℚₚ`-linear map on the actual prime-power completion
has the same fixed exponent label after restriction to global coefficients. -/
def chosenConductorNativeMap
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]]
      (primeAboveConductor p).adicCompletion (cyclotomicField p) :=
  realPrimePowerZeroMapOfLabel p
    ((primeAboveConductor p).adicCompletion (cyclotomicField p))
    (chosenConductorRealLabel p m hm)

theorem chosenConductorNativeMap_global
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p)
    (x : realCyclotomicField (p ^ (0 + 1))) :
    localTateCoefficientLabel p 0
      ((primeAboveConductor p).adicCompletion (cyclotomicField p))
      (chosenConductorNativeMap p m hm) x =
    chosenConductorRealLabel p m hm
      ((IntermediateField.equivOfEq
        (realCyclotomicField_primePower_zero p)) x) :=
  realPrimePowerZeroMapOfLabel_global p
    ((primeAboveConductor p).adicCompletion (cyclotomicField p))
    (chosenConductorRealLabel p m hm) x

/-- The chosen local completion map retains exactly the original global
real coefficient label after the exponent-one field identification. -/
theorem chosenConductorNativeMap_label
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    (localTateCoefficientLabel p 0 (FullConductorCompletion p)
      (chosenConductorNativeMap p m hm)).comp
        (IntermediateField.equivOfEq
          (realCyclotomicField_primePower_zero p)).symm.toAlgHom =
      chosenConductorRealLabel p m hm := by
  apply AlgHom.ext
  intro x
  simpa using chosenConductorNativeMap_global p m hm
    ((IntermediateField.equivOfEq
      (realCyclotomicField_primePower_zero p)).symm x)

/-- The same label equation in the dependent field-equality form used by
the native Tate factor and the selected RM local system. -/
theorem chosenConductorNativeMap_label_transport
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    Eq.mp (congrArg (fun F : IntermediateField ℚ Qbar =>
      F →ₐ[ℚ] FullConductorCompletion p)
      (realCyclotomicField_primePower_zero p))
      (localTateCoefficientLabel p 0 (FullConductorCompletion p)
        (chosenConductorNativeMap p m hm)) =
      chosenConductorRealLabel p m hm := by
  have hcomp : localTateCoefficientLabel p 0 (FullConductorCompletion p)
      (chosenConductorNativeMap p m hm) =
      (chosenConductorRealLabel p m hm).comp
        (IntermediateField.equivOfEq
          (realCyclotomicField_primePower_zero p)).toAlgHom := by
    apply AlgHom.ext
    intro x
    exact chosenConductorNativeMap_global p m hm x
  rw [hcomp]
  exact transportedAlgHom_comp_equivOfEq
    (realCyclotomicField (p ^ (0 + 1))) (realCyclotomicField p)
    (realCyclotomicField_primePower_zero p)
    (FullConductorCompletion p) (chosenConductorRealLabel p m hm)

/-- The chosen coefficient label is continuous for the native completion
topologies, by finite dimensionality over `ℚ_[p]`. -/
theorem continuous_chosenConductorNativeMap
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    Continuous (chosenConductorNativeMap p m hm) :=
  (chosenConductorNativeMap p m hm).toLinearMap.continuous_of_finiteDimensional

/-- The selected plus-Jacobian Tate local system at its actual cyclotomic
conductor place. It is constructed in the native completion topology; the
spectral topology used for lifting is proved equal to it above. -/
@[expose] def chosenConductorPlusTateFamily
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p) :
    Scheme.EtaleLocalSystem (realCyclotomicField p)
      (ProjectiveLine.punctured (realCyclotomicField p))
      (FullConductorCompletion p) := by
  let L := (primeAboveConductor p).adicCompletion (cyclotomicField p)
  letI : NontriviallyNormedField L :=
    Valued.toNontriviallyNormedField L (WithZero (Multiplicative ℤ))
  letI : ContinuousSMul L L := ⟨by
    change Continuous (fun x : L × L => x.1 * x.2)
    exact continuous_mul⟩
  exact primePlusLabelledTateFamily p hp (realCyclotomicField p) m hm
    (cyclotomicField p) (realCyclotomicNormalClosure_le_full p)
    (primeAboveConductor p) L

/-- The chosen conductor family is the selected plus-family local system at
its actual full-conductor coefficient label. -/
theorem chosenConductorPlusTateFamily_eq_labelled
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p) :
    letI : NontriviallyNormedField (FullConductorCompletion p) :=
      Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
    letI : ContinuousSMul (FullConductorCompletion p) (FullConductorCompletion p) :=
      ⟨by change Continuous (fun x : FullConductorCompletion p × FullConductorCompletion p =>
        x.1 * x.2); exact continuous_mul⟩
    chosenConductorPlusTateFamily p hp m hm =
      primePlusLabelledTateFamily p hp (realCyclotomicField p) m hm
        (cyclotomicField p) (realCyclotomicNormalClosure_le_full p)
        (primeAboveConductor p) (FullConductorCompletion p) := by
  rfl

/-- The actual arithmetic Tate carrier at the chosen rational fibre. -/
@[expose] def chosenConductorPlusTateCarrier
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) : Type :=
  (chosenConductorPlusTateFamily p hp m hm).toFunctor.obj
    (Scheme.etaleFiberPoint (realCyclotomicField p) _
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ))

instance chosenConductorPlusTateCarrier_addCommGroup
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    AddCommGroup (chosenConductorPlusTateCarrier p hp m hm ξ) := by
  unfold chosenConductorPlusTateCarrier
  infer_instance

instance chosenConductorPlusTateCarrier_module
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Module (FullConductorCompletion p)
      (chosenConductorPlusTateCarrier p hp m hm ξ) := by
  unfold chosenConductorPlusTateCarrier
  infer_instance

section NormalizedCoefficients

variable (p : ℕ) [Fact p.Prime]

local instance realConductorNormedField : NormedField (RealCompletion p) :=
  spectralNorm.normedField ℚ_[p] (RealCompletion p)

local instance realConductorNontriviallyNormedField :
    NontriviallyNormedField (RealCompletion p) :=
  spectralNorm.nontriviallyNormedField ℚ_[p] (RealCompletion p)

local instance (priority := 1000) realConductorUniformSpace : UniformSpace (RealCompletion p) :=
  (spectralNorm.normedField ℚ_[p]
    (RealCompletion p)).toMetricSpace.toUniformSpace

local instance (priority := 1000) realConductorTopology : TopologicalSpace (RealCompletion p) :=
  (spectralNorm.normedField ℚ_[p]
    (RealCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace

local instance realConductorNormedAlgebra : NormedAlgebra ℚ_[p] (RealCompletion p) :=
  spectralNorm.normedAlgebra ℚ_[p] (RealCompletion p)

local instance realConductorCompleteSpace : CompleteSpace (RealCompletion p) :=
  spectralNorm.completeSpace ℚ_[p] (RealCompletion p)

local instance realConductorLocalField : IsNonarchimedeanLocalField (RealCompletion p) :=
  realConductor_isNonarchimedeanLocalField_spectral p

local instance realConductorResidueCharP : CharP (𝒪[RealCompletion p] ⧸ 𝓂[RealCompletion p]) p :=
  NumberField.adicCompletionResidueCharP
    (realCyclotomicField p) (realPrimeAboveConductor p) p

local instance fullConductorNormedField : NormedField (FullConductorCompletion p) :=
  spectralNorm.normedField ℚ_[p] (FullConductorCompletion p)

local instance fullConductorNontriviallyNormedField :
    NontriviallyNormedField (FullConductorCompletion p) :=
  spectralNorm.nontriviallyNormedField ℚ_[p] (FullConductorCompletion p)

local instance (priority := 1000) fullConductorUniformSpace : UniformSpace (FullConductorCompletion p) :=
  (spectralNorm.normedField ℚ_[p]
    (FullConductorCompletion p)).toMetricSpace.toUniformSpace

local instance (priority := 1000) fullConductorTopology : TopologicalSpace (FullConductorCompletion p) :=
  (spectralNorm.normedField ℚ_[p]
    (FullConductorCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace

local instance fullConductorNormedAlgebra : NormedAlgebra ℚ_[p] (FullConductorCompletion p) :=
  spectralNorm.normedAlgebra ℚ_[p] (FullConductorCompletion p)

local instance fullConductorCompleteSpace : CompleteSpace (FullConductorCompletion p) :=
  spectralNorm.completeSpace ℚ_[p] (FullConductorCompletion p)

local instance fullConductorLocalField : IsNonarchimedeanLocalField
    (FullConductorCompletion p) :=
  fullConductor_isNonarchimedeanLocalField_spectral p

local instance fullConductorResidueCharP :
    CharP (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) p :=
  NumberField.adicCompletionResidueCharP
    (cyclotomicField p) (primeAboveConductor p) p

attribute [local instance] HilbertModularity.Cyclotomic.realFieldAlgebra

/-- The native checklist passes to the SAME selected plus Jacobian action at
the full cyclotomic conductor completion with the canonical spectral norms.
Only absolute irreducibility after enlargement
remains as an explicit application input; the ratio field, finite ramification,
oddness, distinguishedness, determinant and continuity are transported. -/
def selectedPlusFullConductorWeightTwoInput_spectral_of_native
    (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (H : SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)) (cyclotomicField p))
    (habs : (Representation.baseChange (AlgebraicClosure (FullConductorCompletion p))
      ((primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)).mapCoefficients
          (realToFullConductorCompletionMap p))).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToFullIntegers p hp)) (cyclotomicField p) := by
  have hf : Continuous (realToFullConductorCompletionMap p) := by
    change @Continuous (RealCompletion p) (FullConductorCompletion p)
      ((spectralNorm.normedField ℚ_[p]
        (RealCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace)
      ((spectralNorm.normedField ℚ_[p]
        (FullConductorCompletion p)).toMetricSpace.toUniformSpace.toTopologicalSpace)
      (realToFullConductorCompletionMap p)
    rw [realConductor_spectralTopology_eq p,
      fullConductor_spectralTopology_eq p]
    exact continuous_realToFullConductorCompletionMap p
  rw [selectedPlusFullConductorAction_eq_mapNative p hp ξ]
  exact HilbertModularity.Hypergeometric.SkinnerWilesWeightTwoInput.mapLocalCoefficients_withOrdinary
    p (cyclotomicField p) H (realToFullConductorCompletionMap p) hf
    (realToFullConductorCompletionMap_padic p)
    (realToFullConductorIntegerResidueComparison p) habs

end NormalizedCoefficients

end HilbertModularity.Hypergeometric
