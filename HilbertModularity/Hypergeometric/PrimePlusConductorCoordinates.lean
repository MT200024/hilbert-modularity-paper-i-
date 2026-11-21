/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorChecklist
public import HilbertModularity.Geometry.GroupScheme.PrimeCohomologicalCoordinates
public import HilbertModularity.RepresentationTheory.Duality

import Mathlib.Tactic.FastInstance

/-! # Coordinates for the selected conductor fibre

The fixed exponent label on the selected plus Jacobian gives a cohomological
action in two coordinates. Biduality identifies its dual with the native
endomorphism-labelled Tate factor. The arithmetic local-system action is
named separately while its direct comparison with these coordinates remains
to be constructed.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupScheme IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

local instance fullConductorNativeNontriviallyNormedField
    (p : ℕ) [Fact p.Prime] :
    NontriviallyNormedField (FullConductorCompletion p) :=
  fast_instance% Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))

/-- The selected cohomological action at the actual cyclotomic conductor
completion, in two coordinates and at the fixed exponent label. -/
def chosenConductorPlusCohomologicalAction
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Representation (FullConductorCompletion p)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → FullConductorCompletion p) := by
  let L := FullConductorCompletion p
  let hE := realCyclotomicNormalClosure_le_full p
  let hL := splits_minpoly_above_coefficientPrime p (cyclotomicField p)
    (primeAboveConductor p) L hE
  let σ := coefficientEmbeddingAbovePrime p m hm (cyclotomicField p)
    ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
    (primeAboveConductor p) L
  exact primePlusCohomologicalAction p hp ξ p L hL σ

/-- Arithmetic action on the selected Tate fibre at the conductor place. -/
def chosenConductorPlusArithmeticAction
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Representation (FullConductorCompletion p)
      (AbsoluteGalois (realCyclotomicField p))
      (chosenConductorPlusTateCarrier p hp m hm ξ) :=
  (chosenConductorPlusTateFamily p hp m hm).arithmeticRepresentation
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)

/-- The named arithmetic action retains the specified local-system fibre. -/
theorem chosenConductorPlusArithmeticAction_eq
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    chosenConductorPlusArithmeticAction p hp m hm ξ =
      (chosenConductorPlusTateFamily p hp m hm).arithmeticRepresentation
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) := (rfl)

/-- Equality of the chosen local system with the selected plus family gives
an equivalence of their arithmetic fibres at the same rational parameter. -/
def chosenConductorPlusArithmeticEquivLabelled
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    (chosenConductorPlusArithmeticAction p hp m hm ξ).Equiv
      ((primePlusLabelledTateFamily p hp (realCyclotomicField p) m hm
        (cyclotomicField p) (realCyclotomicNormalClosure_le_full p)
        (primeAboveConductor p) (FullConductorCompletion p)).arithmeticRepresentation
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) := by
  let L := FullConductorCompletion p
  letI : ContinuousSMul L L := ⟨by
    change Continuous (fun x : L × L => x.1 * x.2)
    exact continuous_mul⟩
  exact arithmeticLocalSystemEquivOfEq (realCyclotomicField p) L
    (chosenConductorPlusTateFamily p hp m hm)
    (primePlusLabelledTateFamily p hp (realCyclotomicField p) m hm
      (cyclotomicField p) (realCyclotomicNormalClosure_le_full p)
      (primeAboveConductor p) L)
    (chosenConductorPlusTateFamily_eq_labelled p hp m hm)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)

/-- Continuity of each matrix entry of the selected cohomological action at
the canonical conductor completion and fixed exponent label. -/
theorem continuous_chosenConductorPlusCohomologicalAction_entry
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) (i j : Fin 2) :
    Continuous (fun g =>
      chosenConductorPlusCohomologicalAction p hp m hm ξ g
        (Pi.single j 1) i) := by
  unfold chosenConductorPlusCohomologicalAction
  exact continuous_primePlusCohomologicalAction_entry p hp ξ p
    (FullConductorCompletion p)
    (splits_minpoly_above_coefficientPrime p (cyclotomicField p)
      (primeAboveConductor p) (FullConductorCompletion p)
      (realCyclotomicNormalClosure_le_full p))
    (coefficientEmbeddingAbovePrime p m hm (cyclotomicField p)
      ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans
        (realCyclotomicNormalClosure_le_full p))
      (primeAboveConductor p) (FullConductorCompletion p)) i j

/-- Duality gives an equivariant comparison of the native labelled Tate
factor with the two-coordinate cohomological action of the same plus fibre. -/
def primePlusTateEquivCohomologicalCoordinates
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L) :
    ((endomorphismLabelledTate (realCyclotomicField p)
      (primePlusFiber p hp ξ) ℓ (realCyclotomicField p) L hL
      (primePlusFiberRealMultiplication p hp ξ) σ).toRepresentation).Equiv
      (primePlusCohomologicalAction p hp ξ ℓ L hL σ).dual := by
  letI : Module.Finite L
      (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toSubmodule :=
    primePlusFiberLabelledTate_finite p hp ξ ℓ L hL σ
  exact (HilbertModularity.dualEquivOfEquivDual
    (K := L) (G := AbsoluteGalois (realCyclotomicField p))
    (V := Fin 2 → L)
    (W := (endomorphismLabelledTate (realCyclotomicField p)
      (primePlusFiber p hp ξ) ℓ (realCyclotomicField p) L hL
      (primePlusFiberRealMultiplication p hp ξ) σ).toSubmodule)
    (ρ := primePlusCohomologicalAction p hp ξ ℓ L hL σ)
    (σ := (endomorphismLabelledTate (realCyclotomicField p)
      (primePlusFiber p hp ξ) ℓ (realCyclotomicField p) L hL
      (primePlusFiberRealMultiplication p hp ξ) σ).toRepresentation)
    (primePlusCohomologicalActionEquiv p hp ξ ℓ L hL σ)).symm

end HilbertModularity.Hypergeometric
