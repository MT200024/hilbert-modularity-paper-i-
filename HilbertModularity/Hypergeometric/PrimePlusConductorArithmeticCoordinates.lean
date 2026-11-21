/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorCoordinates
public import HilbertModularity.Hypergeometric.PrimePlusConductorNativeBaseChange
import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficientTensor

import Mathlib.Tactic.FastInstance

/-! # Arithmetic conductor coordinates for the same selected plus Jacobian

The fixed exponent label at the full conductor completion is the restriction
of its chosen local coefficient embedding. The labelled arithmetic Tate
fibre is therefore the base change of the selected native Tate factor.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupScheme IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

local instance fullConductorArithmeticNativeNorm (p : ℕ) [Fact p.Prime] :
    NontriviallyNormedField (FullConductorCompletion p) :=
  fast_instance% Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))

local instance fullConductorArithmeticLocalField (p : ℕ) [Fact p.Prime] :
    IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

/-- Relabelling the multiplication field, its integral action and its
coefficient embedding transports the native scalar-extension comparison
without changing the original abelian scheme or arithmetic fibre. -/
private def localCoefficientLabelledTateEquivOfFieldEq
    (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] {S : Scheme} (A : CommGrp (Over S))
    (x : Spec (CommRingCat.of K) ⟶ S)
    (R : IntermediateField ℚ Qbar) [NumberField R]
    (hF : realCyclotomicField (p ^ (0 + 1)) = R)
    (φ₀ : 𝓞 (realCyclotomicField (p ^ (0 + 1))) →+* End A)
    (φ : 𝓞 R →+* End A)
    (hφ : Eq.mp (congrArg (fun F : IntermediateField ℚ Qbar =>
      𝓞 F →+* End A) hF) φ₀ = φ)
    (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
    (f : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] L)
    (σ : R →ₐ[ℚ] L)
    (hσ : Eq.mp (congrArg (fun F : IntermediateField ℚ Qbar =>
      F →ₐ[ℚ] L) hF)
      (localTateCoefficientLabel p 0 L f) = σ)
    (hL : ∀ a : R, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits) :
    letI : Module (RealPrimePowerCompletion p 0)
      (rationalTate K (fiber K A x).X p) :=
        Module.compHom _ (localCoefficientTateAction K A x p 0 φ₀).toRingHom
    letI : Algebra (RealPrimePowerCompletion p 0) L := f.toAlgebra
    ((localCoefficientTateRepresentation K A x p 0 φ₀).baseChange L).Equiv
      (labelledTateSubrepresentation K (fiber K A x).X p R L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 R) φ)
      (fiberPointsAction_realized K (AlgebraicClosure K) A x (𝓞 R) φ)
        σ).toRepresentation := by
  letI : Module (RealPrimePowerCompletion p 0)
      (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (localCoefficientTateAction K A x p 0 φ₀).toRingHom
  letI : Algebra (RealPrimePowerCompletion p 0) L := f.toAlgebra
  cases hF
  cases hφ
  cases hσ
  exact localCoefficientLabelledTateRepresentationEquiv p 0 L f K A x φ₀ hL

/-- The chosen arithmetic fibre identifies with its projector summand on
the selected plus-Jacobian Tate module. -/
def chosenConductorArithmeticEquivSummand
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :=
  primePlusLabelledTateFamily_arithmeticEquiv p hp
    (realCyclotomicField p) m hm (cyclotomicField p)
    (realCyclotomicNormalClosure_le_full p) (primeAboveConductor p)
    (FullConductorCompletion p)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)

/-- The same projector summand identifies with the selected native factor
after its actual fixed-label coefficient extension. -/
def chosenConductorNativeEquivSummand
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) := by
  let L := FullConductorCompletion p
  let f := chosenConductorNativeMap p m hm
  letI : Algebra (RealPrimePowerCompletion p 0) L := f.toAlgebra
  let hsplit := splits_minpoly_above_coefficientPrime p
    (cyclotomicField p) (primeAboveConductor p) L
    (realCyclotomicNormalClosure_le_full p)
  have hlabel : Eq.mp (congrArg (fun F : IntermediateField ℚ Qbar =>
      F →ₐ[ℚ] L) (primePlusPrimePowerField_eq p))
      (localTateCoefficientLabel p 0 L f) =
      coefficientEmbeddingAbovePrime p m hm (cyclotomicField p)
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans
          (realCyclotomicNormalClosure_le_full p))
        (primeAboveConductor p) L := by
    rw [← chosenConductorRealLabel_eq_abovePrime p m hm]
    exact chosenConductorNativeMap_label_transport p m hm
  exact localCoefficientLabelledTateEquivOfFieldEq p
    (realCyclotomicField p) (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    (realCyclotomicField p) (primePlusPrimePowerField_eq p)
    (primePlusPrimePowerRealMultiplication p hp)
    (primePlusRealMultiplication p hp)
    (primePlusPrimePowerRealMultiplication_eq p hp)
    L f (coefficientEmbeddingAbovePrime p m hm (cyclotomicField p)
      ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans
        (realCyclotomicNormalClosure_le_full p))
      (primeAboveConductor p) L) hlabel hsplit

/-- The named chosen arithmetic fibre reaches the selected labelled Tate
summand through equality with the fixed plus-family local system. -/
def chosenConductorActualArithmeticEquivSummand
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :=
  (chosenConductorPlusArithmeticEquivLabelled p hp m hm ξ).trans
    (chosenConductorArithmeticEquivSummand p hp m hm ξ)

/-- The canonical comparison gives integral Tate coordinates at the chosen
native coefficient map before the arithmetic projector is identified. -/
def chosenConductorNativeCoordinateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    let f := chosenConductorNativeMap p m hm
    let hf := continuous_chosenConductorNativeMap p m hm
    letI := primePlusExtendedNativeAlgebra p hp f hf
    letI : Algebra (RealPrimePowerCompletion p 0) (FullConductorCompletion p) :=
      f.toAlgebra
    (chosenConductorNativeBaseChangeAction p hp m hm ξ).Equiv
      (primePlusTateFieldCoordinateAction p hp ξ
        (primePlusExtendedNativeIntegerMap p hp f hf)) := by
  let f := chosenConductorNativeMap p m hm
  let hf := continuous_chosenConductorNativeMap p m hm
  letI := primePlusExtendedNativeAlgebra p hp f hf
  letI : Algebra (RealPrimePowerCompletion p 0) (FullConductorCompletion p) :=
    f.toAlgebra
  rw [chosenConductorNativeBaseChangeAction_eq p hp m hm ξ]
  exact primePlusCanonicalCoefficientCoordinateEquiv p hp ξ f hf

/-- The same coordinate comparison with the scheme-induced rational Tate
presentation used by the labelled arithmetic projector. -/
def chosenConductorGenericCoordinateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    letI : Module (RealPrimePowerCompletion p 0)
        (rationalTate (realCyclotomicField p)
          (fiber (realCyclotomicField p) (primePlusFamily p hp)
            (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).X p) :=
      Module.compHom _ (localCoefficientTateAction (realCyclotomicField p)
        (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) p 0
        (primePlusPrimePowerRealMultiplication p hp)).toRingHom
    let f := chosenConductorNativeMap p m hm
    let hf := continuous_chosenConductorNativeMap p m hm
    letI := primePlusExtendedNativeAlgebra p hp f hf
    letI : Algebra (RealPrimePowerCompletion p 0) (FullConductorCompletion p) :=
      f.toAlgebra
    ((localCoefficientTateRepresentation (realCyclotomicField p)
      (primePlusFamily p hp)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) p 0
      (primePlusPrimePowerRealMultiplication p hp)).baseChange
        (FullConductorCompletion p)).Equiv
      (primePlusTateFieldCoordinateAction p hp ξ
        (primePlusExtendedNativeIntegerMap p hp f hf)) := by
  letI : Module (RealPrimePowerCompletion p 0)
      (rationalTate (realCyclotomicField p)
        (fiber (realCyclotomicField p) (primePlusFamily p hp)
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).X p) :=
    Module.compHom _ (localCoefficientTateAction (realCyclotomicField p)
      (primePlusFamily p hp)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) p 0
      (primePlusPrimePowerRealMultiplication p hp)).toRingHom
  let f := chosenConductorNativeMap p m hm
  let hf := continuous_chosenConductorNativeMap p m hm
  letI := primePlusExtendedNativeAlgebra p hp f hf
  letI : Algebra (RealPrimePowerCompletion p 0) (FullConductorCompletion p) :=
    f.toAlgebra
  change ((localCoefficientTateRep (realCyclotomicField p)
    (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) p 0
    (primePlusPrimePowerRealMultiplication p hp)).ρ.baseChange
      (FullConductorCompletion p)).Equiv
        (primePlusTateFieldCoordinateAction p hp ξ
          (primePlusExtendedNativeIntegerMap p hp f hf))
  rw [← primePlusLocalTateAction_eq_generic p hp ξ]
  exact primePlusCanonicalCoefficientCoordinateEquiv p hp ξ f hf

end HilbertModularity.Hypergeometric
