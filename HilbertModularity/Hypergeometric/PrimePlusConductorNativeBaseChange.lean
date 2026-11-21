/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorChecklist
public import HilbertModularity.Geometry.GroupScheme.PrimePlusCanonicalCoefficientComparison

/-! # Native Tate action at the fixed full-conductor coefficient label -/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

/-- The selected native Tate action is the scheme-induced completed-coefficient
action on the same fibre and with the same real-multiplication map. -/
theorem primePlusLocalTateAction_eq_generic
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    primePlusLocalTateRepresentation p hp ξ =
      localCoefficientTateRep (realCyclotomicField p)
        (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) p 0
        (primePlusPrimePowerRealMultiplication p hp) := (rfl)

/-- Scalar extension of the same selected plus-Jacobian native Tate factor
through the fixed exponent-labelled completion embedding. -/
def chosenConductorNativeBaseChangeAction
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) := by
  letI : Algebra (RealPrimePowerCompletion p 0) (FullConductorCompletion p) :=
    (chosenConductorNativeMap p m hm).toAlgebra
  exact (primePlusLocalTateRepresentation p hp ξ).ρ.baseChange
    (FullConductorCompletion p)

/-- The coefficient map in this action is exactly the chosen local label. -/
theorem chosenConductorNativeBaseChangeAction_eq
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    letI : Algebra (RealPrimePowerCompletion p 0) (FullConductorCompletion p) :=
      (chosenConductorNativeMap p m hm).toAlgebra
    chosenConductorNativeBaseChangeAction p hp m hm ξ =
      (primePlusLocalTateRepresentation p hp ξ).ρ.baseChange
      (FullConductorCompletion p) := (rfl)


end HilbertModularity.Hypergeometric
