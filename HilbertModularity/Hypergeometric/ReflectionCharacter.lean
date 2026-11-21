/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.QuadraticCharacter
public import HilbertModularity.NumberTheory.Cyclotomic
import Mathlib.Tactic.LinearCombination

/-! # A quadratic character over the real cyclotomic field

The square root of `2 + ζ_N + ζ_N⁻¹` gives an actual finite character of the
absolute Galois group of the real cyclotomic field. It is trivial at odd
levels. Comparison with the hypergeometric system and identification of
Frobenius values are separate obligations of [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N]

/-- The real cyclotomic element whose square root controls reflection. -/
def reflectionRadicand : realCyclotomicField N := 2 + tau N 1

/-- The radicand does not vanish at levels at least three. -/
theorem reflectionRadicand_ne_zero (hN : 3 ≤ N) : reflectionRadicand N ≠ 0 := by
  intro ha
  have hz := (zeta_isPrimitiveRoot N).ne_zero (NeZero.ne N)
  have h : (2 : Qbar) + (zeta N + (zeta N)⁻¹) = 0 := by
    have h' := congrArg (realCyclotomicField N).val ha
    change (2 : Qbar) + ((zeta N) ^ 1 + ((zeta N)⁻¹) ^ 1) = 0 at h'
    simpa only [pow_one] using h'
  have hsq : (zeta N + 1) ^ 2 = 0 := by
    calc
      _ = zeta N * (2 + (zeta N + (zeta N)⁻¹)) := by field_simp [hz]; ring
      _ = 0 := by rw [h, mul_zero]
  have heq : zeta N = -1 := eq_neg_of_add_eq_zero_left ((pow_eq_zero_iff two_ne_zero).mp hsq)
  apply (zeta_isPrimitiveRoot N).pow_ne_one_of_pos_of_lt (by decide : 2 ≠ 0) (by omega)
  rw [heq]
  ring

/-- A square root in the fixed algebraic closure; the attached character is
independent of this choice. -/
def reflectionRoot : Qbar :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (realCyclotomicField N) Qbar (reflectionRadicand N)) zero_lt_two).choose

/-- The chosen root has the specified square in the actual coefficient tower. -/
theorem reflectionRoot_sq : reflectionRoot N ^ 2 =
    algebraMap (realCyclotomicField N) Qbar (reflectionRadicand N) :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (realCyclotomicField N) Qbar (reflectionRadicand N)) zero_lt_two).choose_spec

/-- The chosen square root is nonzero. -/
theorem reflectionRoot_ne_zero (hN : 3 ≤ N) : reflectionRoot N ≠ 0 := by
  intro h
  apply (map_ne_zero (algebraMap (realCyclotomicField N) Qbar)).mpr
    (reflectionRadicand_ne_zero N hN)
  rw [← reflectionRoot_sq, h]
  simp

/-- A genuine quadratic algebraic character over the real cyclotomic field. -/
def reflectionCharacter (hN : 3 ≤ N) :
    (Qbar ≃ₐ[realCyclotomicField N] Qbar) →* Qbarˣ :=
  Galois.quadraticCharacter (reflectionRadicand N) (reflectionRoot N)
    (reflectionRoot_ne_zero N hN) (reflectionRoot_sq N)

/-- The global character has order dividing two. -/
theorem reflectionCharacter_sq (hN : 3 ≤ N) : reflectionCharacter N hN ^ 2 = 1 :=
  Galois.quadraticCharacter_sq _ _ _ _

/-- Its actual image is finite. -/
theorem reflectionCharacter_finite_range (hN : 3 ≤ N) :
    Set.Finite (Set.range (reflectionCharacter N hN)) :=
  Galois.quadraticCharacter_finite_range _ _ _ _

/-- The character is locally constant for the standard Krull topology. -/
theorem reflectionCharacter_isLocallyConstant (hN : 3 ≤ N) :
    IsLocallyConstant (reflectionCharacter N hN) := by
  have : Algebra.IsIntegral (realCyclotomicField N) Qbar := Algebra.IsIntegral.tower_top ℚ
  exact Galois.quadraticCharacter_isLocallyConstant _ _ _ _

/-- At an odd level an explicit trace parameter is a square root already in
the real cyclotomic field. -/
theorem tau_half_sq_reflectionRadicand (hodd : Odd N) :
    tau N ((N + 1) / 2) ^ 2 = reflectionRadicand N := by
  have hk : 2 * ((N + 1) / 2) = N + 1 := by obtain ⟨k, hk⟩ := hodd; omega
  have hz := (zeta_isPrimitiveRoot N).ne_zero (NeZero.ne N)
  have hp : ((zeta N) ^ ((N + 1) / 2)) ^ 2 = zeta N := by
    rw [← pow_mul, Nat.mul_comm _ 2, hk, pow_succ, (zeta_isPrimitiveRoot N).pow_eq_one,
      one_mul]
  have hi : (((zeta N)⁻¹) ^ ((N + 1) / 2)) ^ 2 = (zeta N)⁻¹ := by
    rw [← pow_mul, Nat.mul_comm _ 2, hk, pow_succ,
      (zeta_isPrimitiveRoot N).inv.pow_eq_one, one_mul]
  have hm : (zeta N) ^ ((N + 1) / 2) * ((zeta N)⁻¹) ^ ((N + 1) / 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  apply Subtype.ext
  change ((zeta N) ^ ((N + 1) / 2) + ((zeta N)⁻¹) ^ ((N + 1) / 2)) ^ 2 =
    2 + ((zeta N) ^ 1 + ((zeta N)⁻¹) ^ 1)
  simp only [pow_one]
  linear_combination hp + hi + 2 * hm

/-- The actual global quadratic character is trivial at odd levels. -/
theorem reflectionCharacter_eq_one_of_odd (hN : 3 ≤ N) (hodd : Odd N) :
    reflectionCharacter N hN = 1 := by
  let b := tau N ((N + 1) / 2)
  have hb : b ^ 2 = reflectionRadicand N := tau_half_sq_reflectionRadicand N hodd
  have heq : reflectionRoot N ^ 2 =
      (algebraMap (realCyclotomicField N) Qbar b) ^ 2 := by
    rw [reflectionRoot_sq, ← map_pow, hb]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
  · exact Galois.quadraticCharacter_eq_one_of_root _ _ _ _ b h.symm
  · apply Galois.quadraticCharacter_eq_one_of_root _ _ _ _ (-b)
    simpa only [map_neg] using h.symm

end HilbertModularity.Cyclotomic
