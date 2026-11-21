/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Canonical identification of completions at equal ideals -/

public noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R]

/-- Identify completed coefficient rings along an equality of ideals. -/
def idealEqRingEquiv {I J : Ideal R} (h : I = J) :
    AdicCompletion I R ≃+* AdicCompletion J R := by
  subst J
  exact RingEquiv.refl _

@[simp] theorem idealEqRingEquiv_algebraMap {I J : Ideal R}
    (h : I = J) (a : R) :
    idealEqRingEquiv h (algebraMap R (AdicCompletion I R) a) =
      algebraMap R (AdicCompletion J R) a := by
  subst J
  rfl

end AdicCompletion
