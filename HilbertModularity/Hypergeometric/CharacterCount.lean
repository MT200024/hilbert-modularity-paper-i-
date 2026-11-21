/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FiniteField
public import HilbertModularity.NumberTheory.CharacterOrthogonality

/-! # Quadratic-root counts from symmetric hypergeometric sums

We use the rank-two normalization of [TripathiGoswami, equation (2.3)].
Expanding four Gauss sums and applying character orthogonality gives an exact
weighted quadratic-root count, including at the parameter value one.
-/

@[expose] public section

namespace HilbertModularity.Hypergeometric

variable {F C : Type*} [Field F] [Fintype F] [DecidableEq F] [Field C]

/-- A Gauss sum may be indexed by the multiplicative group because its zero
summand vanishes, including for the trivial multiplicative character. -/
theorem gaussSum_eq_sum_units (χ : MulChar F C) (θ : AddChar F C) :
    gaussSum χ θ = ∑ u : Fˣ, χ u * θ u := by
  classical
  rw [Fintype.sum_units_eq_sum_nonzero (fun u : F => χ u * θ u)]
  have h := Finset.sum_erase_add Finset.univ (fun u : F => χ u * θ u)
    (Finset.mem_univ (0 : F))
  simpa only [gaussSum, MulChar.map_zero, zero_mul, add_zero] using h.symm

/-- Expanding the four Gauss sums separates their common multiplicative
character from the additive phase. -/
theorem four_gaussSums_expansion (A χ : MulChar F C) (θ : AddChar F C) (x : F) :
    gaussSum (A * χ) θ * gaussSum (A⁻¹ * χ) θ * gaussSum χ⁻¹ θ ^ 2 * χ x =
      ∑ u : Fˣ, ∑ v : Fˣ, ∑ w : Fˣ, ∑ z : Fˣ,
        A ((u : F) / v) * χ ((u : F) * v * x / ((w : F) * z)) *
          θ ((u : F) + v + w + z) := by
  simp only [gaussSum_eq_sum_units, pow_two, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext
    rw [Finset.sum_comm]
    arg 2; ext
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro z _
  simp only [MulChar.mul_apply, MulChar.inv_apply, Ring.inverse_eq_inv,
    div_eq_mul_inv, mul_inv_rev, map_mul, AddChar.map_add_eq_mul]
  ring

/-- Summation over all multiplicative characters imposes the multiplicative
constraint on the four Gauss-sum variables. -/
theorem sum_four_gaussSums_eq_constrained_sum [CharZero C] [IsAlgClosed C]
    [Fintype (MulChar F C)] (A : MulChar F C) (θ : AddChar F C) (x : F) :
    (∑ χ : MulChar F C,
      gaussSum (A * χ) θ * gaussSum (A⁻¹ * χ) θ * gaussSum χ⁻¹ θ ^ 2 * χ x) =
      ((Fintype.card F : C) - 1) *
        ∑ u : Fˣ, ∑ v : Fˣ, ∑ w : Fˣ, ∑ z : Fˣ,
          if (u : F) * v * x = (w : F) * z then
            A ((u : F) / v) * θ ((u : F) + v + w + z) else 0 := by
  simp only [four_gaussSums_expansion]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext
    rw [Finset.sum_comm]
    arg 2; ext
    rw [Finset.sum_comm]
    arg 2; ext
    rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro z _
  calc
    _ = (A ((u : F) / v) * θ ((u : F) + v + w + z)) *
        ∑ χ : MulChar F C, χ ((u : F) * v * x / ((w : F) * z)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by
      rw [MulChar.sum_apply_finiteField]
      by_cases h : (u : F) * v * x = (w : F) * z <;>
        simp [div_eq_one_iff_eq (mul_ne_zero w.ne_zero z.ne_zero), h]
      ring

/-- The multiplicative constraint uniquely determines the fourth nonzero
Gauss-sum variable. -/
theorem constrained_sum_eq_triple_sum (A : MulChar F C) (θ : AddChar F C)
    (x : Fˣ) :
    (∑ u : Fˣ, ∑ v : Fˣ, ∑ w : Fˣ, ∑ z : Fˣ,
      if (u : F) * v * x = (w : F) * z then
        A ((u : F) / v) * θ ((u : F) + v + w + z) else 0) =
      ∑ u : Fˣ, ∑ v : Fˣ, ∑ w : Fˣ,
        A ((u : F) / v) * θ ((u : F) + v + w + (u : F) * v * x / w) := by
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  have hc (z : Fˣ) : (u : F) * v * x = (w : F) * z ↔ z = u * v * x / w := by
    rw [← Units.val_inj]
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    rw [eq_div_iff_mul_eq w.ne_zero]
    constructor <;> intro h <;> simpa only [mul_comm (z : F) (w : F)] using h.symm
  simp_rw [hc]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Units.val_div_eq_div_val,
    Units.val_mul]

/-- Scaling the first and third variables by the second separates the additive
phase into a nonzero scalar and a quadratic-root expression. -/
theorem triple_sum_eq_scaled_sum (A : MulChar F C) (θ : AddChar F C) (x : F) :
    (∑ u : Fˣ, ∑ v : Fˣ, ∑ w : Fˣ,
      A ((u : F) / v) * θ ((u : F) + v + w + (u : F) * v * x / w)) =
      ∑ s : Fˣ, ∑ t : Fˣ, A s *
        ∑ v : Fˣ, θ ((v : F) * ((s : F) + 1 + t + (s : F) * x / t)) := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ v : Fˣ, ∑ s : Fˣ, ∑ t : Fˣ,
        A s * θ ((v : F) * ((s : F) + 1 + t + (s : F) * x / t)) := by
      apply Finset.sum_congr rfl
      intro v _
      symm
      refine Fintype.sum_bijective (fun s : Fˣ => s * v)
        (Group.mulRight_bijective v) _ _ ?_
      intro s
      refine Fintype.sum_bijective (fun t : Fˣ => t * v)
        (Group.mulRight_bijective v) _ _ ?_
      intro t
      simp only [Units.val_mul, mul_div_cancel_right₀ _ v.ne_zero]
      congr 2
      field_simp
    _ = _ := by
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2; ext
        rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

omit [Fintype F] [DecidableEq F] in
/-- Clearing the nonzero third variable identifies the zero additive phase
with the quadratic equation. -/
theorem scaled_phase_eq_zero_iff (s t : Fˣ) (x : F) :
    (s : F) + 1 + t + (s : F) * x / t = 0 ↔
      (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0 := by
  have h : ((s : F) + 1 + t + (s : F) * x / t) * t =
      (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x := by
    field_simp
    ring
  rw [← h]
  simp only [mul_eq_zero, t.ne_zero, or_false]

/-- Additive orthogonality counts the zeroes of the quadratic phase, with the
constant correction caused by summing over nonzero scalars. -/
theorem sum_units_quadratic_phase (θ : AddChar F C) (hθ : θ ≠ 1)
    (s t : Fˣ) (x : F) :
    (∑ v : Fˣ, θ ((v : F) * ((s : F) + 1 + t + (s : F) * x / t))) =
      (Fintype.card F : C) *
        (if (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0 then 1 else 0) - 1 := by
  rw [AddChar.sum_units_mul θ hθ]
  simp only [scaled_phase_eq_zero_iff]
  split_ifs <;> ring

/-- Summing the additive phase over the remaining nonzero variable gives the
number of nonzero roots of the quadratic, with its constant correction. -/
theorem sum_quadratic_phases (θ : AddChar F C) (hθ : θ ≠ 1) (s : Fˣ) (x : F) :
    (∑ t : Fˣ, ∑ v : Fˣ,
      θ ((v : F) * ((s : F) + 1 + t + (s : F) * x / t))) =
      (Fintype.card F : C) *
        (Finset.univ.filter (fun t : Fˣ =>
          (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card -
        Fintype.card Fˣ := by
  simp_rw [sum_units_quadratic_phase θ hθ]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- The nontrivial multiplicative character cancels the constant correction
in additive orthogonality, leaving the weighted quadratic-root count. -/
theorem scaled_sum_eq_weighted_root_count (A : MulChar F C) (hA : A ≠ 1)
    (θ : AddChar F C) (hθ : θ ≠ 1) (x : F) :
    (∑ s : Fˣ, ∑ t : Fˣ, A s *
      ∑ v : Fˣ, θ ((v : F) * ((s : F) + 1 + t + (s : F) * x / t))) =
      (Fintype.card F : C) * ∑ s : Fˣ, A s *
        (Finset.univ.filter (fun t : Fˣ =>
          (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card := by
  simp_rw [← Finset.mul_sum, sum_quadratic_phases θ hθ]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, MulChar.sum_units_eq_zero hA, zero_mul, sub_zero,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Four Gauss sums, averaged over all multiplicative characters, count roots
of a quadratic with a multiplicative-character weight. -/
theorem sum_four_gaussSums_eq_weighted_root_count [CharZero C] [IsAlgClosed C]
    [Fintype (MulChar F C)] (A : MulChar F C) (hA : A ≠ 1)
    (θ : AddChar F C) (hθ : θ ≠ 1) (x : F) (hx : x ≠ 0) :
    (∑ χ : MulChar F C,
      gaussSum (A * χ) θ * gaussSum (A⁻¹ * χ) θ * gaussSum χ⁻¹ θ ^ 2 * χ x) =
      (Fintype.card F : C) * ((Fintype.card F : C) - 1) *
        ∑ s : Fˣ, A s * (Finset.univ.filter (fun t : Fˣ =>
          (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card := by
  have h := constrained_sum_eq_triple_sum A θ (Units.mk0 x hx)
  simp only [Units.val_mk0] at h
  rw [sum_four_gaussSums_eq_constrained_sum]
  erw [h]
  rw [triple_sum_eq_scaled_sum,
    scaled_sum_eq_weighted_root_count A hA θ hθ]
  ring

/-- The normalized character-sum formula for the weighted quadratic-root
count. This holds for every nontrivial multiplicative character; the further
hypothesis `A (-1) = 1` identifies it with the rank-two McCarthy function. -/
theorem normalized_gaussSum_eq_neg_weighted_root_count [CharZero C] [IsAlgClosed C]
    [Fintype (MulChar F C)] (A : MulChar F C) (hA : A ≠ 1)
    (θ : AddChar F C) (hθ : θ ≠ 1) (x : F) (hx : x ≠ 0) :
    -((Fintype.card F : C) * ((Fintype.card F : C) - 1))⁻¹ *
      (∑ χ : MulChar F C,
        gaussSum (A * χ) θ * gaussSum (A⁻¹ * χ) θ * gaussSum χ⁻¹ θ ^ 2 * χ x) =
      -∑ s : Fˣ, A s * (Finset.univ.filter (fun t : Fˣ =>
        (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card := by
  rw [sum_four_gaussSums_eq_weighted_root_count A hA θ hθ x hx]
  have hq : (Fintype.card F : C) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hq1 : (Fintype.card F : C) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast ne_of_gt (Fintype.one_lt_card : 1 < Fintype.card F)
  rw [neg_mul, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hq hq1), one_mul]

/-- For an even nontrivial multiplicative character, the rank-two McCarthy
function is the negative weighted count of nonzero roots of the quadratic. -/
theorem rankTwoMcCarthySum_eq_neg_weighted_root_count [CharZero C] [IsAlgClosed C]
    (A : MulChar F C) (hA : A ≠ 1) (hneg : A (-1) = 1)
    (θ : AddChar F C) (hθ : θ ≠ 1) (x : F) (hx : x ≠ 0) :
    rankTwoMcCarthySum θ A x =
      -∑ s : Fˣ, A s * (Finset.univ.filter (fun t : Fˣ =>
        (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card := by
  have hpow : A ^ (orderOf A - 1) = A⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos A.orderOf_pos, pow_orderOf_eq_one]
  have hden := gaussSum_mul_gaussSum_pow_orderOf_sub_one hA
    (AddChar.IsPrimitive.of_ne_one hθ)
  rw [hpow, hneg, one_mul] at hden
  rw [rankTwoMcCarthySum_eq θ hθ, hden]
  calc
    _ = -((Fintype.card F : C) * ((Fintype.card F : C) - 1))⁻¹ *
        ∑ χ : MulChar F C,
          gaussSum (A * χ) θ * gaussSum (A⁻¹ * χ) θ * gaussSum χ⁻¹ θ ^ 2 * χ x := by
      simp only [Finset.mul_sum, div_eq_mul_inv, mul_inv_rev]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := normalized_gaussSum_eq_neg_weighted_root_count A hA θ hθ x hx

end HilbertModularity.Hypergeometric
