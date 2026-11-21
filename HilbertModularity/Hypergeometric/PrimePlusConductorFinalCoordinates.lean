/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorArithmeticComparison
public import HilbertModularity.Geometry.GroupScheme.PrimeDarmonLocalSystemComparison
import Mathlib.Tactic.FastInstance

/-! # Fixed-label integral coordinates for the actual arithmetic Tate fibre -/

public noncomputable section

open AlgebraicGeometry
open scoped NumberField

namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic HilbertModularForms

local instance fullConductorFinalCoordinatesNorm (p : ℕ) [Fact p.Prime] :
    NontriviallyNormedField (FullConductorCompletion p) :=
  fast_instance% Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))

local instance fullConductorFinalCoordinatesLocalField (p : ℕ) [Fact p.Prime] :
    IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

/-- Compose the checked same-fibre arithmetic and native comparisons with
the canonical integral Tate coordinates, retaining the fixed exponent label. -/
def chosenConductorPlusArithmeticCoordinateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    (chosenConductorPlusArithmeticAction p hp m hm ξ).Equiv
      (chosenConductorPlusCoordinateAction p hp m hm ξ) := by
  rw [chosenConductorPlusCoordinateAction_eq]
  exact (chosenConductorPlusArithmeticActionEquivNative p hp m hm ξ).trans
    (chosenConductorGenericCoordinateEquiv p hp m hm ξ)

/-- The canonical integral coordinates identify with the chosen Darmon
arithmetic Tate fibre at the fixed conductor coefficient label. This is the
covariant coordinate comparison consumed by the Euler modularity endpoints. -/
def chosenConductorDarmonCoordinateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    (chosenConductorPlusCoordinateAction p hp m hm ξ).Equiv
      ((darmonLabelledTateFamily (realCyclotomicField p) p (by omega) p m hm
        (cyclotomicField p) (realCyclotomicNormalClosure_le_full p)
        (primeAboveConductor p) (FullConductorCompletion p)).arithmeticRepresentation
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) := by
  let L := FullConductorCompletion p
  let F := darmonLabelledTateFamily (realCyclotomicField p) p (by omega) p m hm
    (cyclotomicField p) (realCyclotomicNormalClosure_le_full p)
    (primeAboveConductor p) L
  have hF : F = chosenConductorPlusTateFamily p hp m hm := by
    exact (darmonLabelledTateFamily_eq_primePlus p (by omega) hp
      (realCyclotomicField p) m hm (cyclotomicField p)
      (realCyclotomicNormalClosure_le_full p) (primeAboveConductor p) L).trans
        (chosenConductorPlusTateFamily_eq_labelled p hp m hm).symm
  let e := arithmeticLocalSystemEquivOfEq (realCyclotomicField p) L F
    (chosenConductorPlusTateFamily p hp m hm) hF
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
  have ec := chosenConductorPlusArithmeticCoordinateEquiv p hp m hm ξ
  rw [chosenConductorPlusArithmeticAction_eq] at ec
  exact (e.trans ec).symm

end HilbertModularity.Hypergeometric
