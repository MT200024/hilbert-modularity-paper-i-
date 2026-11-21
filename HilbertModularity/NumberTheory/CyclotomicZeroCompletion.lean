/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicNormalizedCompletion
public import HilbertModularity.NumberTheory.LocalFieldMorphisms

/-! # Coefficient compatibility at the exponent-zero conductor completion -/

public noncomputable section

open scoped NumberField ValuativeRel TensorProduct

namespace HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime]

local instance : IsNonarchimedeanLocalField (RealCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (realCyclotomicField p) (realPrimeAboveConductor p) p

/-- A linear equivalence of these finite-dimensional local fields is
continuous for their original valuation topologies. -/
theorem continuous_realPrimePowerZeroCompletionEquiv :
    Continuous (realPrimePowerZeroCompletionEquiv p) :=
  (realPrimePowerZeroCompletionEquiv p).toLinearMap.continuous_of_finiteDimensional

theorem continuous_realPrimePowerZeroCompletionEquiv_symm :
    Continuous (realPrimePowerZeroCompletionEquiv p).symm :=
  (realPrimePowerZeroCompletionEquiv p).symm.toLinearMap.continuous_of_finiteDimensional

/-- The integer rings are compared by restricting that same canonical
field equivalence, rather than choosing an independent ring isomorphism. -/
def realPrimePowerZeroIntegerEquiv :
    𝒪[RealPrimePowerCompletion p 0] ≃+* 𝒪[RealCompletion p] :=
  IsNonarchimedeanLocalField.integerEquiv
    (realPrimePowerZeroCompletionEquiv p).toRingEquiv
    (continuous_realPrimePowerZeroCompletionEquiv p)
    (continuous_realPrimePowerZeroCompletionEquiv_symm p)

@[simp] theorem coe_realPrimePowerZeroIntegerEquiv
    (a : 𝒪[RealPrimePowerCompletion p 0]) :
    (realPrimePowerZeroIntegerEquiv p a : RealCompletion p) =
      realPrimePowerZeroCompletionEquiv p (a : RealPrimePowerCompletion p 0) := by
  exact (rfl)

end HilbertModularity.Cyclotomic
