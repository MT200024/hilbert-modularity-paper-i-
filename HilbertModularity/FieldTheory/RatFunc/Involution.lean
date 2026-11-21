/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.RatFunc.Basic

/-! # The rational parameter involution -/

@[expose] public noncomputable section

namespace Polynomial
variable (R : Type*) [CommRing R]

/-- Substitution by `1 - X` is an involution of the polynomial algebra. -/
def complementAlgEquiv : Polynomial R ≃ₐ[R] Polynomial R :=
  algEquivOfCompEqX (1 - X) (1 - X) (by simp) (by simp)

@[simp]
theorem complementAlgEquiv_apply (f : Polynomial R) :
    complementAlgEquiv R f = f.comp (1 - X) := by
  simp [complementAlgEquiv, ← comp_eq_aeval]

@[simp]
theorem complementAlgEquiv_symm : (complementAlgEquiv R).symm = complementAlgEquiv R := rfl

end Polynomial

namespace RatFunc
variable (K : Type*) [Field K]

/-- The ground-field automorphism of `K(X)` sending `X` to `1 - X`. -/
def complementAlgEquiv : RatFunc K ≃ₐ[K] RatFunc K :=
  IsFractionRing.algEquivOfAlgEquiv (Polynomial.complementAlgEquiv K)

@[simp]
theorem complementAlgEquiv_algebraMap (f : Polynomial K) :
    complementAlgEquiv K (algebraMap (Polynomial K) (RatFunc K) f) =
      algebraMap (Polynomial K) (RatFunc K) (f.comp (1 - Polynomial.X)) := by
  simp [complementAlgEquiv]

@[simp]
theorem complementAlgEquiv_symm : (complementAlgEquiv K).symm = complementAlgEquiv K := by
  simp [complementAlgEquiv]

/-- Applying the rational parameter substitution twice restores the original function. -/
@[simp]
theorem complementAlgEquiv_twice (f : RatFunc K) :
    complementAlgEquiv K (complementAlgEquiv K f) = f := by
  simpa only [complementAlgEquiv_symm] using (complementAlgEquiv K).symm_apply_apply f

end RatFunc
