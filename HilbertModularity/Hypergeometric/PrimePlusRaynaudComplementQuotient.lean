/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusRaynaudStableApplication
public import HilbertModularity.Geometry.GroupScheme.PrimePlusComplementTate
public import HilbertModularity.RepresentationTheory.SpecifiedFiniteTwistQuotient

/-! # The specified period quotient at the complementary cusp -/

public noncomputable section

open AlgebraicGeometry HilbertModularity.Cyclotomic HilbertModularity.Hyperelliptic
open scoped NumberField ValuativeRel TensorProduct

namespace HilbertModularity.Hypergeometric

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusDecompositionRationalModule
  primePlusDecompositionScalarTower

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- The actual selected stable-model certificate yields its specified native
period quotient with trivial local Galois action. In the complementary
application, the certificate is `of_cubicDifference` at `1 - ξ`. -/
theorem exists_primePlusBaseOrdinaryQuotient_of_stableModel
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (H : PrimePlusScaledStableModelData p hp ξ) :
    ∃ W : HodgeTate.WeightZeroQuotient p
        (realPrimePowerLocalPeriodAction p 0)
        (realPrimePowerLocalPeriodAction_fixes p 0)
        (primePlusDecompositionRepresentation p hp ξ).ρ,
      ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
        (v : (primePlusDecompositionRepresentation p hp ξ) ⧸
          W.kernel.toSubmodule),
        (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
          W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v = v := by
  have hparameter : (H.T : realCyclotomicField p) =
      ξ.val / (2 - tau p 1) ^ p := H.field_parameter
  obtain ⟨D⟩ := exists_primePlusRaynaudUniformization_of_scaledModel p hp ξ
    H.T H.special_geometry hparameter (primePlusRealScaledFiberJacobian p hp ξ)
  exact D.existsBaseOrdinaryQuotientWithFixed p hp ξ

/-- A finite twist of one selected stable model has a specified quotient
whose Galois action is exactly the twisting character. This is applied to
the stable model at `1 - ξ` before the Darmon–Mestre equivalence. -/
theorem exists_primePlusTwistedBaseOrdinaryQuotient_of_stableModel
    (η : ProjectiveLine.Parameter (realCyclotomicField p))
    (H : PrimePlusScaledStableModelData p hp η)
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ)
    (hχ : Continuous χ) (horder : IsOfFinOrder χ) :
    ∃ W : HodgeTate.WeightZeroQuotient p
        (realPrimePowerLocalPeriodAction p 0)
        (realPrimePowerLocalPeriodAction_fixes p 0)
        ((Representation.ofCharacter χ).tprod
          (primePlusDecompositionRepresentation p hp η).ρ),
      ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
        (v : ((RealPrimePowerCompletion p 0) ⊗[RealPrimePowerCompletion p 0]
          (primePlusDecompositionRepresentation p hp η)) ⧸
          W.kernel.toSubmodule),
        (((Representation.ofCharacter χ).tprod
          (primePlusDecompositionRepresentation p hp η).ρ).quotient
          W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v) =
            (χ g : RealPrimePowerCompletion p 0) • v := by
  obtain ⟨W, hfixed⟩ := exists_primePlusBaseOrdinaryQuotient_of_stableModel
    p hp η H
  exact HodgeTate.exists_characterTensorWeightZeroQuotient_with_action
    p (primePlusDecompositionRepresentation p hp η).ρ χ hχ horder W hfixed

/-- A specified twisted quotient transports across the actual
Darmon–Mestre Tate equivalence without losing its quotient character. -/
theorem exists_primePlusBaseOrdinaryQuotient_of_twistedEquiv
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ).Equiv
      (primePlusDecompositionRepresentation p hp ξ).ρ))
    (WT : HodgeTate.WeightZeroQuotient p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0)
      ((Representation.ofCharacter χ).tprod
        (primePlusDecompositionRepresentation p hp
          (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ))
    (hWT : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : ((RealPrimePowerCompletion p 0) ⊗[RealPrimePowerCompletion p 0]
        (primePlusDecompositionRepresentation p hp
          (ProjectiveLine.complementParameter (realCyclotomicField p) ξ))) ⧸
          WT.kernel.toSubmodule),
      (((Representation.ofCharacter χ).tprod
        (primePlusDecompositionRepresentation p hp
          (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ).quotient
          WT.kernel.toSubmodule WT.kernel.apply_mem_toSubmodule g v) =
            (χ g : RealPrimePowerCompletion p 0) • v) :
    ∃ W : HodgeTate.WeightZeroQuotient p
        (realPrimePowerLocalPeriodAction p 0)
        (realPrimePowerLocalPeriodAction_fixes p 0)
        (primePlusDecompositionRepresentation p hp ξ).ρ,
      ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
        (v : (primePlusDecompositionRepresentation p hp ξ) ⧸
          W.kernel.toSubmodule),
        (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
          W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v =
            (χ g : RealPrimePowerCompletion p 0) • v := by
  exact HodgeTate.exists_weightZeroQuotient_equiv_with_character p
    (realPrimePowerLocalPeriodAction p 0)
    (realPrimePowerLocalPeriodAction_fixes p 0) e χ WT hWT

/-- The actual stable model at `1 - ξ` and one finite-character Tate
comparison give a weight-zero quotient at the original selected fibre whose
character is exactly that finite twist. -/
theorem exists_primePlusBaseOrdinaryQuotient_of_complementTwist
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (H : PrimePlusScaledStableModelData p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ))
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ)
    (hχ : Continuous χ) (horder : IsOfFinOrder χ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ).Equiv
      (primePlusDecompositionRepresentation p hp ξ).ρ)) :
    ∃ W : HodgeTate.WeightZeroQuotient p
        (realPrimePowerLocalPeriodAction p 0)
        (realPrimePowerLocalPeriodAction_fixes p 0)
        (primePlusDecompositionRepresentation p hp ξ).ρ,
      ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
        (v : (primePlusDecompositionRepresentation p hp ξ) ⧸
          W.kernel.toSubmodule),
        (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
          W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v =
            (χ g : RealPrimePowerCompletion p 0) • v := by
  obtain ⟨WT, hWT⟩ := exists_primePlusTwistedBaseOrdinaryQuotient_of_stableModel
    p hp (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)
      H χ hχ horder
  exact exists_primePlusBaseOrdinaryQuotient_of_twistedEquiv p hp ξ χ e WT hWT


end HilbertModularity.Hypergeometric
