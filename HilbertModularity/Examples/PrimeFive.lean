/- Assembled by AxiomProver. -/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! # Affine point counts and polynomial calculations at level five -/

@[expose] public section

namespace HilbertModularity.Examples

open Polynomial

/-- [TripathiGoswami], Example 7.1: `C_5^+(125)` has `11` affine points over `𝔽₁₁`; with the two points at
infinity of the monic degree-six model this gives `#C(𝔽₁₁) = 13`. -/
theorem c5_affine_count_11 :
    (Finset.univ.filter (fun xy : ZMod 11 × ZMod 11 =>
      xy.2 ^ 2 = (xy.1 + 2) * (xy.1 ^ 5 - 5 * xy.1 ^ 3 + 5 * xy.1 + 2 - 500))).card = 11 := by
  decide

/-- [TripathiGoswami], Example 7.1: `C_5^+(125)` has `41` affine points over `𝔽₄₁`, so `#C(𝔽₄₁) = 43`. -/
theorem c5_affine_count_41 :
    (Finset.univ.filter (fun xy : ZMod 41 × ZMod 41 =>
      xy.2 ^ 2 = (xy.1 + 2) * (xy.1 ^ 5 - 5 * xy.1 ^ 3 + 5 * xy.1 + 2 - 500))).card = 41 := by
  decide +kernel

open Real in
/-- [TripathiGoswami], Example 7.1: the local polynomial at `11` factors as
`1 + T + 21T² + 11T³ + 121T⁴ = (1 - aT + 11T²)(1 - a'T + 11T²)` with
`a, a' = (-1 ± √5)/2`. -/
theorem local_poly_11 :
    (1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 : ℝ[X]) =
      (1 - C ((-1 + √5) / 2) * X + 11 * X ^ 2) * (1 - C ((-1 - √5) / 2) * X + 11 * X ^ 2) := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : C ((-1 + √5) / 2) + C ((-1 - √5) / 2) = (-1 : ℝ[X]) := by
    rw [← C_add, show (-1 + √5) / 2 + (-1 - √5) / 2 = -1 by ring, C_neg, C_1]
  have hp : C ((-1 + √5) / 2) * C ((-1 - √5) / 2) = (-1 : ℝ[X]) := by
    rw [← C_mul, show (-1 + √5) / 2 * ((-1 - √5) / 2) = -1 by linear_combination (-1/4) * h5,
      C_neg, C_1]
  linear_combination (X + 11 * X ^ 3) * hs - X ^ 2 * hp

open Real in
/-- [TripathiGoswami], Example 7.1: the local polynomial at `41` factors as
`1 + T + 51T² + 41T³ + 1681T⁴ = (1 - bT + 41T²)(1 - b'T + 41T²)` with
`b, b' = (-1 ± 5√5)/2`. -/
theorem local_poly_41 :
    (1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 : ℝ[X]) =
      (1 - C ((-1 + 5 * √5) / 2) * X + 41 * X ^ 2) *
        (1 - C ((-1 - 5 * √5) / 2) * X + 41 * X ^ 2) := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : C ((-1 + 5 * √5) / 2) + C ((-1 - 5 * √5) / 2) = (-1 : ℝ[X]) := by
    rw [← C_add, show (-1 + 5 * √5) / 2 + (-1 - 5 * √5) / 2 = -1 by ring, C_neg, C_1]
  have hp : C ((-1 + 5 * √5) / 2) * C ((-1 - 5 * √5) / 2) = (-31 : ℝ[X]) := by
    rw [← C_mul, show (-1 + 5 * √5) / 2 * ((-1 - 5 * √5) / 2) = -31 by
      linear_combination (-25/4) * h5, C_neg, map_ofNat]
  linear_combination (X + 41 * X ^ 3) * hs - X ^ 2 * hp

/-- [TripathiGoswami], Example 7.1: the only real roots of unity are `±1`. -/
theorem real_root_of_unity {z : ℝ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) : z = 1 ∨ z = -1 := by
  have h : |z| = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (abs_nonneg z) hn, pow_abs, hz, abs_one]
  exact (abs_eq zero_le_one).mp h

open Real in
/-- [TripathiGoswami], Example 7.1: at `11` the ratio of `(√5 - 1)/2` to its conjugate `(-1 - √5)/2` is not a
root of unity. -/
theorem ratio_11_not_root_of_unity (n : ℕ) (hn : n ≠ 0) :
    (((√5 - 1) / 2) / ((-1 - √5) / 2)) ^ n ≠ 1 := by
  intro h
  have hpos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (-1 - √5) / 2 ≠ 0 := by intro h'; linarith
  rcases real_root_of_unity hn h with h | h
  · rw [div_eq_iff hden] at h; linarith
  · rw [div_eq_iff hden] at h; linarith

open Real in
/-- [TripathiGoswami], Example 7.1: at `41` the ratio of `(-1 - 5√5)/2` to its conjugate `(-1 + 5√5)/2` is not
a root of unity. -/
theorem ratio_41_not_root_of_unity (n : ℕ) (hn : n ≠ 0) :
    (((-1 - 5 * √5) / 2) / ((-1 + 5 * √5) / 2)) ^ n ≠ 1 := by
  intro h
  have hpos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num)
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hgt : 1 < 5 * √5 := by nlinarith
  have hden : (-1 + 5 * √5) / 2 ≠ 0 := by intro h'; linarith
  rcases real_root_of_unity hn h with h | h
  · rw [div_eq_iff hden] at h; linarith
  · rw [div_eq_iff hden] at h; linarith

end HilbertModularity.Examples
