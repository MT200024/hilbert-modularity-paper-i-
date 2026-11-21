/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-! # Differential identity for the rescaled Chebyshev polynomials

The identities are integral, so they apply directly after reduction to a residue field.
-/

namespace Polynomial.Chebyshev

variable {R : Type*} [CommRing R]

/-- The derivative of the rescaled polynomial of the first kind. -/
theorem C_derivative_eq_S (n : ℤ) :
    derivative (C R n) = n * S R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := congr_arg derivative (C_add_two R n)
    have h₂ := S_sub_one R n
    have h₃ := C_eq_S_sub_X_mul_S R (n + 1)
    simp only [derivative_sub, derivative_mul, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      h₁ - ih2 + (X : R[X]) * ih1 + h₃ - n * h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := congr_arg derivative (C_sub_one R (-n))
    have h₂ := S_sub_two R (-n)
    have h₃ := C_eq_S_sub_X_mul_S R (-n)
    simp only [derivative_sub, derivative_mul, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      -ih2 + (X : R[X]) * ih1 + h₁ + h₃ + (n + 1) * h₂

/-- The quadratic relation between the two rescaled Chebyshev families. -/
theorem X_sq_sub_four_mul_S_sq (n : ℤ) :
    (X ^ 2 - 4) * S R (n - 1) ^ 2 = C R n ^ 2 - 4 := by
  rw [C_eq_S_sub_X_mul_S]
  have h := S_sq_add_S_sq R (n - 1)
  simp only [sub_add_cancel] at h
  linear_combination -4 * h

/-- The Chebyshev differential identity, valid over every commutative ring. -/
theorem C_differential_identity (n : ℤ) :
    (X ^ 2 - 4) * derivative (C R n) ^ 2 = (n : R[X]) ^ 2 * (C R n ^ 2 - 4) := by
  rw [C_derivative_eq_S, mul_pow, ← mul_assoc, mul_comm (X ^ 2 - 4), mul_assoc,
    X_sq_sub_four_mul_S_sq]

/-- The positive-index rescaled Chebyshev polynomial is monic of its index degree. -/
theorem C_isMonicOfDegree [Nontrivial R] (n : ℕ) (hn : n ≠ 0) :
    (C R n).IsMonicOfDegree n := by
  induction n using Nat.twoStepInduction with
  | zero => exact (hn rfl).elim
  | one => simpa using isMonicOfDegree_X R
  | more n ih₀ ih₁ =>
    have hdeg : (C R n).natDegree ≤ n := by
      by_cases h : n = 0
      · subst n; simp
      · exact (ih₀ h).natDegree_eq.le
    have h := ((isMonicOfDegree_X R).mul (ih₁ (by omega))).sub
      (hdeg.trans_lt (by omega))
    simpa [Nat.cast_add, C_add_two, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using h

/-- A level set of the rescaled Chebyshev polynomial is separable unless the
level is a critical value `±2`, when the index is nonzero in the coefficient field. -/
theorem C_sub_separable {K : Type*} [Field K] (n : ℤ) (hn : (n : K) ≠ 0)
    (a : K) (ha : a ^ 2 - 4 ≠ 0) : (C K n - Polynomial.C a).Separable := by
  let u : K[X] := Polynomial.C (((n : K) ^ 2 * (a ^ 2 - 4))⁻¹)
  have hu : u * ((n : K[X]) ^ 2 * (Polynomial.C a ^ 2 - 4)) = 1 := by
    have h := congrArg Polynomial.C (inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero 2 hn) ha))
    simpa only [map_mul, map_pow, map_sub, map_ofNat, map_intCast, map_one] using h
  refine ⟨-u * (n : K[X]) ^ 2 * (C K n + Polynomial.C a),
    u * (X ^ 2 - 4) * derivative (C K n), ?_⟩
  rw [derivative_sub, derivative_C, sub_zero]
  linear_combination u * C_differential_identity (R := K) n + hu

/-- The rescaled Chebyshev polynomial evaluated on a reciprocal pair. -/
theorem C_eval_add_inv {K : Type*} [Field K] (n : ℕ) (z : K) (hz : z ≠ 0) :
    (C K n).eval (z + z⁻¹) = z ^ n + z⁻¹ ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [← two_mul]
  | one => simp
  | more n ih₀ ih₁ =>
    have h := C_add_two K (n : ℤ)
    push_cast at ih₁ ⊢
    rw [h, eval_sub, eval_mul, eval_X, ih₀, ih₁]
    simp only [pow_succ]
    linear_combination (z ^ n + z⁻¹ ^ n) * mul_inv_cancel₀ hz

end Polynomial.Chebyshev
