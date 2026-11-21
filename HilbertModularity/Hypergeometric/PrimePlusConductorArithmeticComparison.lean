/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorArithmeticCoordinates

/-! # Arithmetic comparison for the fixed conductor label -/

public noncomputable section

open AlgebraicGeometry
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

local instance fullConductorArithmeticComparisonLocalField (p : ℕ) [Fact p.Prime] :
    IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

/-- The selected canonical integral Tate action at the fixed full-conductor
coefficient embedding, on two coordinates. -/
def chosenConductorPlusCoordinateAction
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Representation (FullConductorCompletion p)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → FullConductorCompletion p) :=
  primePlusTateFieldCoordinateAction p hp ξ
    (primePlusExtendedNativeIntegerMap p hp
      (chosenConductorNativeMap p m hm)
      (continuous_chosenConductorNativeMap p m hm))

theorem chosenConductorPlusCoordinateAction_eq
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    chosenConductorPlusCoordinateAction p hp m hm ξ =
      primePlusTateFieldCoordinateAction p hp ξ
        (primePlusExtendedNativeIntegerMap p hp
          (chosenConductorNativeMap p m hm)
          (continuous_chosenConductorNativeMap p m hm)) := (rfl)

/-- The chosen full-conductor arithmetic fibre of the selected plus family
is the scalar extension of its same native completed Tate representation.
The field, RM action and coefficient label are all the specified ones. -/
def chosenConductorPlusArithmeticEquivNative
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :=
  (chosenConductorArithmeticEquivSummand p hp m hm ξ).trans
    (chosenConductorNativeEquivSummand p hp m hm ξ).symm

/-- The exact named arithmetic fibre, rather than only its labelled-family
presentation, is the scalar extension of the selected native Tate factor. -/
def chosenConductorPlusArithmeticActionEquivNative
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :=
  (chosenConductorActualArithmeticEquivSummand p hp m hm ξ).trans
    (chosenConductorNativeEquivSummand p hp m hm ξ).symm


end HilbertModularity.Hypergeometric
