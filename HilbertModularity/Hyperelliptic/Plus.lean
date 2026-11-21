/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Polynomial.Chebyshev

@[expose] public section

/-! # Polynomial of the plus family

The double cover has equation `y² = (x + 2)(Cₚ(x) + 2 - 4t)`.
-/

namespace HilbertModularity.Hyperelliptic

open Polynomial

/-- The polynomial defining the plus-family double cover. -/
noncomputable def plusPolynomial {R : Type*} [CommRing R] (p : ℕ) (t : R) : R[X] :=
  (X + 2) * (Chebyshev.C R p - C (4 * t - 2))

private theorem isCoprime_X_sub_C_of_eval_ne_zero {K : Type*} [Field K]
    (f : K[X]) (a : K) (ha : f.eval a ≠ 0) : IsCoprime (X - C a) f := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (p := f) (a := a)
  have hi : C (f.eval a)⁻¹ * C (f.eval a) = (1 : K[X]) := by
    rw [← C_mul, inv_mul_cancel₀ ha, C_1]
  refine ⟨-C (f.eval a)⁻¹ * q, C (f.eval a)⁻¹, ?_⟩
  linear_combination C (f.eval a)⁻¹ * hq + hi

/-- Monicity and degree of the plus-family polynomial. -/
theorem plusPolynomial_isMonicOfDegree {R : Type*} [CommRing R] [Nontrivial R]
    (p : ℕ) (hp : p ≠ 0) (t : R) : (plusPolynomial p t).IsMonicOfDegree (p + 1) := by
  have h := (Chebyshev.C_isMonicOfDegree (R := R) p hp).sub
    (show (C (4 * t - 2)).natDegree < p by rw [natDegree_C]; omega)
  have hlin : (X + 2 : R[X]).IsMonicOfDegree 1 := by
    simpa only [map_ofNat] using isMonicOfDegree_X_add_one (2 : R)
  simpa only [plusPolynomial, Nat.add_comm] using hlin.mul h

/-- Away from `t = 0, 1`, the plus-family polynomial is separable when the
odd index and `2` are nonzero in the coefficient field. Primality is unnecessary. -/
theorem plusPolynomial_separable {K : Type*} [Field K] (p : ℕ) (hp : Odd p)
    (h2 : (2 : K) ≠ 0) (hpc : (p : K) ≠ 0) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (plusPolynomial p t).Separable := by
  have h4 : (4 : K) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1; ring
  have h16 : (16 : K) ≠ 0 := by
    convert mul_ne_zero h4 h4 using 1; ring
  have ha : (4 * t - 2) ^ 2 - 4 ≠ 0 := by
    rw [show (4 * t - 2) ^ 2 - 4 = 16 * t * (t - 1) by ring]
    exact mul_ne_zero (mul_ne_zero h16 ht0) (sub_ne_zero.mpr ht1)
  have hsep := Chebyshev.C_sub_separable (p : ℤ) (by exact_mod_cast hpc) (4 * t - 2) ha
  have heval : (Chebyshev.C K p - C (4 * t - 2)).eval (-2) ≠ 0 := by
    rw [eval_sub, Chebyshev.C_eval_neg_two, eval_C]
    have hodd : (p : ℤ).negOnePow = -1 := by
      exact Int.negOnePow_odd _ (by exact_mod_cast hp)
    rw [hodd]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    convert neg_ne_zero.mpr (mul_ne_zero h4 ht0) using 1; ring
  have hcop := isCoprime_X_sub_C_of_eval_ne_zero _ (-2) heval
  have hlin : (X + 2 : K[X]).Separable := by
    simpa only [map_ofNat] using separable_X_add_C (2 : K)
  exact hlin.mul hsep (by simpa only [C_neg, map_ofNat, sub_neg_eq_add] using hcop)

end HilbertModularity.Hyperelliptic
