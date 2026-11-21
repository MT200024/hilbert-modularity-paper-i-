/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveComparison
public import HilbertModularity.Hyperelliptic.PrimeFiveQuadraticPoints
public import HilbertModularity.LinearAlgebra.RankTwoTrace

/-! # Frobenius recovery from the level-five projective point counts

For actual rank-two matrices, the determinant and two point-count trace
identities recover the unordered labelled traces and the local polynomial.
The cohomological trace identities remain explicit arithmetic inputs.
See [TripathiGoswami, Example 7.1].
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry

namespace HilbertModularity.Examples

open Hyperelliptic

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩

private theorem pair_of_sum_product {K : Type*} [Field K] {a b r s : K}
    (hs : a + b = r + s) (hp : a * b = r * s) :
    (a = r ∧ b = s) ∨ (a = s ∧ b = r) := by
  have h : (a - r) * (a - s) = 0 := by linear_combination a * hs - hp
  rcases mul_eq_zero.mp h with h | h
  · left
    have ha := sub_eq_zero.mp h
    exact ⟨ha, by linear_combination hs - ha⟩
  · right
    have ha := sub_eq_zero.mp h
    exact ⟨ha, by linear_combination hs - ha⟩

/-- Two traces over a field with a prescribed sum and product form the indicated
unordered pair. -/
theorem unordered_pair_of_sum_product {K : Type*} [Field K] {a b r s : K}
    (hs : a + b = r + s) (hp : a * b = r * s) :
    (a = r ∧ b = s) ∨ (a = s ∧ b = r) :=
  pair_of_sum_product hs hp

/-- Complex specialization used by the numerical worked example. -/
theorem unordered_complex_pair_of_sum_product {a b r s : ℂ}
    (hs : a + b = r + s) (hp : a * b = r * s) :
    (a = r ∧ b = s) ∨ (a = s ∧ b = r) :=
  unordered_pair_of_sum_product hs hp

/-- The actual reverse characteristic polynomial of a rank-two matrix. -/
theorem charpolyRev_fin_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.charpolyRev = 1 - C M.trace * X + C M.det * X ^ 2 := by
  simp [Matrix.charpolyRev, Matrix.det_fin_two, Matrix.trace_fin_two,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply]
  ring

/-- The checked projective counts at eleven determine the two conjugate Frobenius traces. -/
theorem frobenius_trace_pair_11
    (M N : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 11) (hN : N.det = 11)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 11))) : ℂ) = 11 + 1 - (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField11))) : ℂ) =
      11 ^ 2 + 1 - ((M ^ 2).trace + (N ^ 2).trace)) :
    (M.trace = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧ N.trace = (-1 - (Real.sqrt 5 : ℂ)) / 2) ∨
    (M.trace = (-1 - (Real.sqrt 5 : ℂ)) / 2 ∧ N.trace = ((Real.sqrt 5 : ℂ) - 1) / 2) := by
  rw [primeFive_count_11] at h₁
  rw [primeFive_count_121] at h₂
  have hs : M.trace + N.trace = -1 := by linear_combination h₁
  have hm := two_mul_det_eq_sq_trace_sub_trace_sq M
  have hn := two_mul_det_eq_sq_trace_sub_trace_sq N
  rw [hM] at hm
  rw [hN] at hn
  have hsq : M.trace ^ 2 + N.trace ^ 2 = 3 := by linear_combination -hm - hn + h₂
  have hp : M.trace * N.trace = -1 := by
    linear_combination (1 / 2 : ℂ) * (M.trace + N.trace - 1) * hs - (1 / 2 : ℂ) * hsq
  have hr : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  apply pair_of_sum_product
  · linear_combination hs
  · linear_combination hp + (1 / 4 : ℂ) * hr

/-- The checked projective counts at forty-one determine the two conjugate Frobenius traces. -/
theorem frobenius_trace_pair_41
    (M N : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 41) (hN : N.det = 41)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 41))) : ℂ) = 41 + 1 - (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField41))) : ℂ) =
      41 ^ 2 + 1 - ((M ^ 2).trace + (N ^ 2).trace)) :
    (M.trace = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧
      N.trace = (-1 + 5 * (Real.sqrt 5 : ℂ)) / 2) ∨
    (M.trace = (-1 + 5 * (Real.sqrt 5 : ℂ)) / 2 ∧
      N.trace = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2) := by
  rw [primeFive_count_41] at h₁
  rw [primeFive_count_1681] at h₂
  have hs : M.trace + N.trace = -1 := by linear_combination h₁
  have hm := two_mul_det_eq_sq_trace_sub_trace_sq M
  have hn := two_mul_det_eq_sq_trace_sub_trace_sq N
  rw [hM] at hm
  rw [hN] at hn
  have hsq : M.trace ^ 2 + N.trace ^ 2 = 63 := by linear_combination -hm - hn + h₂
  have hp : M.trace * N.trace = -31 := by
    linear_combination (1 / 2 : ℂ) * (M.trace + N.trace - 1) * hs - (1 / 2 : ℂ) * hsq
  have hr : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  apply pair_of_sum_product
  · linear_combination hs
  · linear_combination hp + (25 / 4 : ℂ) * hr

/-- The actual block Frobenius matrix has the product of the two local factors. -/
theorem charpolyRev_fromBlocks (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    (Matrix.fromBlocks M 0 0 N).charpolyRev = M.charpolyRev * N.charpolyRev := by
  rw [← Matrix.reverse_charpoly, Matrix.charpoly_fromBlocks_zero₁₂,
    Polynomial.reverse_mul_of_domain, Matrix.reverse_charpoly, Matrix.reverse_charpoly]

private theorem charpolyRev_product_of_sum_product
    (M N : Matrix (Fin 2) (Fin 2) ℂ) (q r : ℂ)
    (hM : M.det = q) (hN : N.det = q)
    (hs : M.trace + N.trace = -1) (hp : M.trace * N.trace = r) :
    M.charpolyRev * N.charpolyRev =
      1 + X + C (r + 2 * q) * X ^ 2 + C q * X ^ 3 + C (q ^ 2) * X ^ 4 := by
  have hsC : C M.trace + C N.trace = (-1 : ℂ[X]) := by
    simpa only [map_add, map_neg, map_one] using congrArg (C : ℂ →+* ℂ[X]) hs
  have hpC : C M.trace * C N.trace = (C r : ℂ[X]) := by
    simpa only [map_mul] using congrArg (C : ℂ →+* ℂ[X]) hp
  rw [charpolyRev_fin_two, charpolyRev_fin_two, hM, hN]
  simp only [map_add, map_mul, map_ofNat, map_pow]
  linear_combination -(X + C q * X ^ 3) * hsC + X ^ 2 * hpC

/-- The actual reverse characteristic polynomials recover the local polynomial at 11. -/
theorem frobenius_local_polynomial_11
    (M N : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 11) (hN : N.det = 11)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 11))) : ℂ) = 11 + 1 - (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField11))) : ℂ) =
      11 ^ 2 + 1 - ((M ^ 2).trace + (N ^ 2).trace)) :
    (Matrix.fromBlocks M 0 0 N).charpolyRev =
      1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 := by
  rw [charpolyRev_fromBlocks]
  have ht := frobenius_trace_pair_11 M N hM hN h₁ h₂
  have hr : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hs : M.trace + N.trace = -1 := by
    rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> ring
  have hp : M.trace * N.trace = -1 := by
    rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;>
      linear_combination (-1 / 4 : ℂ) * hr
  convert charpolyRev_product_of_sum_product M N 11 (-1) hM hN hs hp using 1
  norm_num [map_ofNat]

/-- The actual reverse characteristic polynomials recover the local polynomial at 41. -/
theorem frobenius_local_polynomial_41
    (M N : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 41) (hN : N.det = 41)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 41))) : ℂ) = 41 + 1 - (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField41))) : ℂ) =
      41 ^ 2 + 1 - ((M ^ 2).trace + (N ^ 2).trace)) :
    (Matrix.fromBlocks M 0 0 N).charpolyRev =
      1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 := by
  rw [charpolyRev_fromBlocks]
  have ht := frobenius_trace_pair_41 M N hM hN h₁ h₂
  have hr : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hs : M.trace + N.trace = -1 := by
    rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> ring
  have hp : M.trace * N.trace = -31 := by
    rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;>
      linear_combination (-25 / 4 : ℂ) * hr
  convert charpolyRev_product_of_sum_product M N 41 (-31) hM hN hs hp using 1
  norm_num [map_ofNat]

/-- The point-count identities and fixed comparison equation force the actual finite
comparison character at 11 to be trivial, without a separately assumed trace-pair conclusion. -/
theorem frobenius_comparison_character_11
    (M N : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 11) (hN : N.det = 11)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 11))) : ℂ) = 11 + 1 - (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField11))) : ℂ) =
      11 ^ 2 + 1 - ((M ^ 2).trace + (N ^ 2).trace))
    {G : Type*} [Group G] (ν : G →* ℂˣ) (hν : (Set.range ν).Finite) (g : G)
    (A : MulChar (ZMod 11) ℂ) (hA : A 2 = fifthRoot)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1)
    (he : Hypergeometric.rankTwoMcCarthySum θ A 125 = (ν g : ℂ) * M.trace) :
    M.trace = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧ ν g = 1 := by
  have ht := frobenius_trace_pair_11 M N hM hN h₁ h₂
  exact finite_comparison_character_11 ν hν g A hA θ hθ M.trace
    (ht.imp And.left And.left) he

/-- The point-count identities and fixed comparison equation force the actual finite
comparison character at 41 to be trivial, without a separately assumed trace-pair conclusion. -/
theorem frobenius_comparison_character_41
    (M N : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 41) (hN : N.det = 41)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 41))) : ℂ) = 41 + 1 - (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField41))) : ℂ) =
      41 ^ 2 + 1 - ((M ^ 2).trace + (N ^ 2).trace))
    {G : Type*} [Group G] (ν : G →* ℂˣ) (hν : (Set.range ν).Finite) (g : G)
    (A : MulChar (ZMod 41) ℂ) (hA : A 6 = fifthRoot)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1)
    (he : Hypergeometric.rankTwoMcCarthySum θ A 125 = (ν g : ℂ) * M.trace) :
    M.trace = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧ ν g = 1 := by
  have ht := frobenius_trace_pair_41 M N hM hN h₁ h₂
  exact finite_comparison_character_41 ν hν g A hA θ hθ M.trace
    (ht.imp And.left And.left) he

end HilbertModularity.Examples
