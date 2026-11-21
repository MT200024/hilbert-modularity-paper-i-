/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.CharacterCount
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Reflection of the finite hypergeometric trace values

The weighted quadratic-root formula for the McCarthy normalization in
[TripathiGoswami] is invariant under `x ↦ 1-x` for even characters.
The change of variables is `(s,t) ↦ (-s,t+s)`.
-/

@[expose] public noncomputable section

namespace HilbertModularity.Hypergeometric

variable {F : Type*} [Field F]

/-- Translation identifies the two quadratic root sets under reflection. -/
def quadraticRootsComplement (s x : F) :
    {t : F // t ^ 2 + (s + 1) * t + s * x = 0} ≃
    {t : F // t ^ 2 + (-s + 1) * t + (-s) * (1 - x) = 0} where
  toFun t := ⟨t.val + s, by linear_combination t.property⟩
  invFun t := ⟨t.val - s, by linear_combination t.property⟩
  left_inv t := by apply Subtype.ext; simp
  right_inv t := by apply Subtype.ext; simp

/-- If the constant term is nonzero, every quadratic root is a unit. -/
def quadraticUnitRootsEquiv (s x : F) (h : s * x ≠ 0) :
    {t : Fˣ // (t : F) ^ 2 + (s + 1) * t + s * x = 0} ≃
    {t : F // t ^ 2 + (s + 1) * t + s * x = 0} where
  toFun t := ⟨t.val, t.property⟩
  invFun t := ⟨Units.mk0 t.val (by
    intro ht
    apply h
    simpa only [ht, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] using t.property),
    by simpa only [Units.val_mk0] using t.property⟩
  left_inv t := by apply Subtype.ext; apply Units.ext; rfl
  right_inv t := by apply Subtype.ext; rfl

/-- The nonzero-root counts at reflected parameters agree after negating the
weight variable. Both excluded parameters are needed for the unit condition. -/
theorem quadraticUnitRoots_card_complement [Fintype F] [DecidableEq F]
    (s : Fˣ) (x : F) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    (Finset.univ.filter (fun t : Fˣ =>
      (t : F) ^ 2 + ((-s : Fˣ) + 1 : F) * t + (-s : Fˣ) * (1 - x) = 0)).card =
    (Finset.univ.filter (fun t : Fˣ =>
      (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card := by
  let e := (quadraticUnitRootsEquiv (s : F) x (mul_ne_zero s.ne_zero hx)).trans
    ((quadraticRootsComplement (s : F) x).trans
      (quadraticUnitRootsEquiv (-(s : F)) (1 - x)
        (mul_ne_zero (neg_ne_zero.mpr s.ne_zero) (sub_ne_zero.mpr hx1.symm))).symm)
  simpa only [Fintype.card_subtype, Units.val_neg] using (Fintype.card_congr e).symm

/-- Every character annihilated by an odd power is even. -/
theorem character_neg_one_of_odd_power {C : Type*} [Field C]
    (A : MulChar F C) (N : ℕ) (hN : Odd N) (hA : A ^ N = 1) : A (-1) = 1 := by
  calc
    A (-1) = A ((-1 : F) ^ N) := congrArg A hN.neg_one_pow.symm
    _ = A (-1) ^ N := map_pow A _ _
    _ = 1 := by
      rw [← A.pow_apply' (by obtain ⟨k, rfl⟩ := hN; omega), hA]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))

variable {C : Type*} [Field C] [CharZero C] [IsAlgClosed C]
  [Fintype F] [DecidableEq F]

omit [CharZero C] [IsAlgClosed C] in
/-- Reflection multiplies the weighted quadratic-root count by the character
value at minus one. -/
theorem weightedQuadraticRoots_complement (A : MulChar F C)
    (x : F) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    (∑ s : Fˣ, A s * (Finset.univ.filter (fun t : Fˣ =>
      (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * (1 - x) = 0)).card) =
    A (-1) * ∑ s : Fˣ, A s * (Finset.univ.filter (fun t : Fˣ =>
      (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card := by
  calc
    _ = ∑ s : Fˣ, A (-s) * (Finset.univ.filter (fun t : Fˣ =>
        (t : F) ^ 2 + ((-s : Fˣ) + 1 : F) * t + (-s : Fˣ) * (1 - x) = 0)).card :=
      (Equiv.sum_comp (Equiv.neg Fˣ) (fun s : Fˣ => A (s : F) *
        ((Finset.univ.filter (fun t : Fˣ =>
          (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * (1 - x) = 0)).card : C))).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [quadraticUnitRoots_card_complement s x hx hx1, neg_eq_neg_one_mul, map_mul]
      ring

/-- The weighted-root formula with the exact character factor retained; no
parity condition is imposed on the multiplicative character. -/
theorem rankTwoMcCarthySum_eq_character_weighted_roots
    (A : MulChar F C) (hA : A ≠ 1) (θ : AddChar F C) (hθ : θ ≠ 1)
    (x : F) (hx : x ≠ 0) :
    rankTwoMcCarthySum θ A x = (A (-1))⁻¹ *
      (-∑ s : Fˣ, A s * (Finset.univ.filter (fun t : Fˣ =>
        (t : F) ^ 2 + ((s : F) + 1) * t + (s : F) * x = 0)).card) := by
  have hpow : A ^ (orderOf A - 1) = A⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos A.orderOf_pos, pow_orderOf_eq_one]
  have hden := gaussSum_mul_gaussSum_pow_orderOf_sub_one hA
    (AddChar.IsPrimitive.of_ne_one hθ)
  rw [hpow] at hden
  rw [rankTwoMcCarthySum_eq θ hθ, hden]
  calc
    _ = (A (-1))⁻¹ * (-((Fintype.card F : C) * ((Fintype.card F : C) - 1))⁻¹ *
        ∑ χ : MulChar F C,
          gaussSum (A * χ) θ * gaussSum (A⁻¹ * χ) θ * gaussSum χ⁻¹ θ ^ 2 * χ x) := by
      simp only [Finset.mul_sum, div_eq_mul_inv, mul_inv_rev]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by
      rw [normalized_gaussSum_eq_neg_weighted_root_count A hA θ hθ x hx]

/-- At arbitrary character order, reflection has the explicit scalar `A(-1)`. -/
theorem rankTwoMcCarthySum_complement_eq (A : MulChar F C) (hA : A ≠ 1)
    (θ : AddChar F C) (hθ : θ ≠ 1) (x : F) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    rankTwoMcCarthySum θ A (1 - x) = A (-1) * rankTwoMcCarthySum θ A x := by
  rw [rankTwoMcCarthySum_eq_character_weighted_roots A hA θ hθ
      (1 - x) (sub_ne_zero.mpr hx1.symm),
    rankTwoMcCarthySum_eq_character_weighted_roots A hA θ hθ x hx,
    weightedQuadraticRoots_complement A x hx hx1]
  ring

/-- The exact McCarthy value is invariant under reflection for an even
nontrivial character, at every parameter away from zero and one. -/
theorem rankTwoMcCarthySum_complement (A : MulChar F C) (hA : A ≠ 1)
    (hneg : A (-1) = 1) (θ : AddChar F C) (hθ : θ ≠ 1)
    (x : F) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    rankTwoMcCarthySum θ A (1 - x) = rankTwoMcCarthySum θ A x := by
  simpa only [hneg, one_mul] using rankTwoMcCarthySum_complement_eq A hA θ hθ x hx hx1

/-- Odd-order characters satisfy the reflection identity with no separate
parity assumption. -/
theorem rankTwoMcCarthySum_complement_of_odd_power (A : MulChar F C) (hA : A ≠ 1)
    (N : ℕ) (hN : Odd N) (hpow : A ^ N = 1)
    (θ : AddChar F C) (hθ : θ ≠ 1) (x : F) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    rankTwoMcCarthySum θ A (1 - x) = rankTwoMcCarthySum θ A x :=
  rankTwoMcCarthySum_complement A hA (character_neg_one_of_odd_power A N hN hpow)
    θ hθ x hx hx1

/-- Every nontrivial labelled power of an odd-order character has the same
symmetric McCarthy value at complementary parameters. -/
theorem symmetricMcCarthySum_complement (χ : MulChar F C) (hodd : Odd (orderOf χ))
    (m : ℕ) (hm : m ≠ 0) (hmorder : m < orderOf χ)
    (θ : AddChar F C) (hθ : θ ≠ 1) (x : F) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    symmetricMcCarthySum θ χ m (1 - x) = symmetricMcCarthySum θ χ m x := by
  apply rankTwoMcCarthySum_complement_of_odd_power (χ ^ m)
    (pow_ne_one_of_lt_orderOf hm hmorder) (orderOf χ) hodd _ θ hθ x hx hx1
  rw [← pow_mul, Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

/-- The general reflection factor for a specified nontrivial character label. -/
theorem symmetricMcCarthySum_complement_eq (χ : MulChar F C)
    (m : ℕ) (hm : m ≠ 0) (hmorder : m < orderOf χ)
    (θ : AddChar F C) (hθ : θ ≠ 1) (x : F) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    symmetricMcCarthySum θ χ m (1 - x) =
      (χ ^ m) (-1) * symmetricMcCarthySum θ χ m x :=
  rankTwoMcCarthySum_complement_eq (χ ^ m) (pow_ne_one_of_lt_orderOf hm hmorder)
    θ hθ x hx hx1

end HilbertModularity.Hypergeometric
