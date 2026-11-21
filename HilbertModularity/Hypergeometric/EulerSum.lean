/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FiniteFieldInvolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Euler character sums for symmetric hypergeometric data

The quadratic-root count of four Gauss sums is the Euler character sum after
solving its equation for the character-weight variable. This proves the direct
normalization in [TripathiGoswamiRevised, the argument after equation (2.4)],
with the character value at minus one retained and no Jacobi-motive convention.
-/

@[expose] public noncomputable section

namespace MulChar

variable {F C : Type*} [Field F] [Fintype F] [DecidableEq F] [Field C]

/-- A nontrivial character summed on the fibre of a linear polynomial evaluates at its root;
the zero-slope case is supplied by character orthogonality. -/
theorem sum_linear_fiber (A : MulChar F C) (hA : A ≠ 1) (a b : F) :
    (∑ s : F, if a * s + b = 0 then A s else 0) = A (-b / a) := by
  classical
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0 <;> simp [hb, MulChar.sum_eq_zero_of_ne_one hA]
  · have h (s : F) : a * s + b = 0 ↔ s = -b / a := by
      rw [add_eq_zero_iff_eq_neg, eq_div_iff ha, mul_comm a s]
    simp_rw [h]
    simp

end MulChar

namespace HilbertModularity.Hypergeometric

variable {F C : Type*} [Field F] [Fintype F] [DecidableEq F] [Field C]

/-- The actual Euler character sum for the symmetric datum. All characters vanish at zero. -/
def eulerCharacterSum (A : MulChar F C) (x : F) : C :=
  ∑ y : F, A y * A⁻¹ (1 - y) * A (1 - x * y)

omit [DecidableEq F] in
/-- At a primitive exponent, the Euler character sum is the character evaluated on
the actual cyclic-cover polynomial, including its branch points. -/
theorem eulerCharacterSum_pow_eq (χ : MulChar F C) (N m : ℕ)
    (hm : 0 < m) (hmN : m < N) (hχ : χ ^ N = 1) (x : F) :
    eulerCharacterSum (χ ^ m) x =
      ∑ y : F, χ (y ^ m * (1 - y) ^ (N - m) * (1 - x * y) ^ m) := by
  have hi : (χ ^ m)⁻¹ = χ ^ (N - m) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, Nat.add_sub_cancel' hmN.le, hχ]
  unfold eulerCharacterSum
  rw [hi]
  apply Finset.sum_congr rfl
  intro y _
  simp only [χ.pow_apply' (Nat.ne_of_gt hm),
    χ.pow_apply' (Nat.sub_ne_zero_of_lt hmN), map_mul, map_pow]

private theorem sum_units_of_zero (f : F → C) (hf : f 0 = 0) :
    (∑ u : Fˣ, f u) = ∑ y : F, f y := by
  rw [Fintype.sum_units_eq_sum_nonzero]
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : F))
  simpa only [hf, add_zero] using h

/-- Solving the quadratic-root equation for its weight gives precisely the Euler sum. -/
theorem weightedQuadraticRoots_eq_eulerCharacterSum (A : MulChar F C) (hA : A ≠ 1)
    (x : F) (hx : x ≠ 0) :
    (∑ s : Fˣ, A s * (Finset.univ.filter (fun t : Fˣ =>
      (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card) =
        eulerCharacterSum A x := by
  classical
  have hc (s : Fˣ) :
      A s * (Finset.univ.filter (fun t : Fˣ =>
        (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card =
      ∑ t : Fˣ, if (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0
        then A s else 0 := by
    rw [← Finset.sum_filter]
    simp [nsmul_eq_mul, mul_comm]
  simp_rw [hc]
  rw [Finset.sum_comm]
  have hs (t : Fˣ) :
      (∑ s : Fˣ, if (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0
        then A s else 0) = A (-((t : F) ^ 2 + t) / ((t : F) + x)) := by
    rw [sum_units_of_zero (fun s : F => if (t : F) ^ 2 + (s + 1) * t + s * x = 0
      then A s else 0) (by simp [MulChar.map_zero])]
    have h (s : F) : (t : F) ^ 2 + (s + 1) * t + s * x =
        ((t : F) + x) * s + ((t : F) ^ 2 + t) := by ring
    simp_rw [h]
    exact A.sum_linear_fiber hA _ _
  simp_rw [hs]
  rw [sum_units_of_zero (fun t : F => A (-(t ^ 2 + t) / (t + x))) (by simp [MulChar.map_zero])]
  have hchange := Equiv.sum_comp (Equiv.mulLeft₀ (-x) (neg_ne_zero.mpr hx))
    (fun t : F => A (-(t ^ 2 + t) / (t + x)))
  rw [← hchange]
  unfold eulerCharacterSum
  apply Finset.sum_congr rfl
  intro y _
  change A (-((-x * y) ^ 2 + (-x * y)) / (-x * y + x)) = _
  have hfrac : -((-x * y) ^ 2 + (-x * y)) / (-x * y + x) =
      y * (1 - x * y) / (1 - y) := by
    by_cases hy : y = 1
    · simp [hy]
    · have hy' : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
      have hd : -x * y + x = x * (1 - y) := by ring
      rw [hd]
      (field_simp; ring)
  rw [hfrac]
  simp only [div_eq_mul_inv, map_mul, ← MulChar.inv_apply']
  ring

/-- McCarthy's symmetric normalization is the Euler character sum with its exact sign factor. -/
theorem rankTwoMcCarthySum_eq_eulerCharacterSum [CharZero C] [IsAlgClosed C]
    (A : MulChar F C) (hA : A ≠ 1) (θ : AddChar F C) (hθ : θ ≠ 1)
    (x : F) (hx : x ≠ 0) :
    rankTwoMcCarthySum θ A x = -A (-1) * eulerCharacterSum A x := by
  rw [rankTwoMcCarthySum_eq_character_weighted_roots A hA θ hθ x hx,
    weightedQuadraticRoots_eq_eulerCharacterSum A hA x hx]
  have hsign : (A (-1))⁻¹ = A (-1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← map_mul]
    simp
  rw [hsign]
  ring

end HilbertModularity.Hypergeometric
