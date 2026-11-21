/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveFrobenius
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! # Unordered RM traces from the worked local polynomials

Once the actual fixed RM decomposition factors the genus-two polynomial into
its two determinant-q factors, comparison of coefficients determines the
unordered traces. The separate Euler comparison then selects the fixed label.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Examples

/-- The factorization of the eleven-prime polynomial gives exactly the
unordered conjugate pair of RM traces. -/
theorem unorderedTracePair_of_localPolynomial_11
    (a b : ℂ)
    (hpoly : (1 - C a * X + 11 * X ^ 2) *
      (1 - C b * X + 11 * X ^ 2) =
        (1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 : ℂ[X])) :
    (a = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧
      b = (-1 - (Real.sqrt 5 : ℂ)) / 2) ∨
    (a = (-1 - (Real.sqrt 5 : ℂ)) / 2 ∧
      b = ((Real.sqrt 5 : ℂ) - 1) / 2) := by
  have hpoly' : (1 - C (a + b) * X + C (a * b + 22) * X ^ 2 -
      C (11 * (a + b)) * X ^ 3 + 121 * X ^ 4 : ℂ[X]) =
        1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 := by
    calc
      _ = (1 - C a * X + 11 * X ^ 2) *
          (1 - C b * X + 11 * X ^ 2) := by
        simp only [map_add, map_mul, map_ofNat]
        ring
      _ = _ := hpoly
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) hpoly'
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) hpoly'
  simp only [coeff_add,
    coeff_sub,
    coeff_C_mul_X_pow,
    coeff_C_mul_X,
    coeff_X,
    coeff_one] at h1 h2
  norm_num at h1 h2
  have hs : a + b = -1 := by linear_combination -h1
  have hp : a * b = -1 := by linear_combination h2
  have hr : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  apply unordered_complex_pair_of_sum_product
  · linear_combination hs
  · linear_combination hp + (1 / 4 : ℂ) * hr

/-- The forty-one-prime factorization gives the second unordered conjugate
pair, before the fixed RM label is selected. -/
theorem unorderedTracePair_of_localPolynomial_41
    (a b : ℂ)
    (hpoly : (1 - C a * X + 41 * X ^ 2) *
      (1 - C b * X + 41 * X ^ 2) =
        (1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 : ℂ[X])) :
    (a = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧
      b = (-1 + 5 * (Real.sqrt 5 : ℂ)) / 2) ∨
    (a = (-1 + 5 * (Real.sqrt 5 : ℂ)) / 2 ∧
      b = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2) := by
  have hpoly' : (1 - C (a + b) * X + C (a * b + 82) * X ^ 2 -
      C (41 * (a + b)) * X ^ 3 + 1681 * X ^ 4 : ℂ[X]) =
        1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 := by
    calc
      _ = (1 - C a * X + 41 * X ^ 2) *
          (1 - C b * X + 41 * X ^ 2) := by
        simp only [map_add, map_mul, map_ofNat]
        ring
      _ = _ := hpoly
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) hpoly'
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) hpoly'
  simp only [coeff_add,
    coeff_sub,
    coeff_C_mul_X_pow,
    coeff_C_mul_X,
    coeff_X,
    coeff_one] at h1 h2
  norm_num at h1 h2
  have hs : a + b = -1 := by linear_combination -h1
  have hp : a * b = -31 := by linear_combination h2
  have hr : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  apply unordered_complex_pair_of_sum_product
  · linear_combination hs
  · linear_combination hp + (25 / 4 : ℂ) * hr

end HilbertModularity.Examples
