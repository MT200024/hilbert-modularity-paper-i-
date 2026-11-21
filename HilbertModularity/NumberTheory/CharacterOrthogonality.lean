/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.LinearCombination

/-! # Orthogonality of finite-field multiplicative characters -/

@[expose] public section

namespace MulChar

variable {M R : Type*} [CommMonoid M] [Finite M] [CommRing R] [IsDomain R]
  [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)] [Fintype (MulChar M R)]

/-- Characters sum to zero away from the identity whenever they separate points. -/
theorem sum_apply_eq_zero {a : M} (ha : a ≠ 1) :
    ∑ χ : MulChar M R, χ a = 0 := by
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity M R ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun _ => rfl

/-- The evaluation sum is supported at the identity. -/
theorem sum_apply_eq_ite [DecidableEq M] (a : M) :
    ∑ χ : MulChar M R, χ a = if a = 1 then (Fintype.card (MulChar M R) : R) else 0 := by
  classical
  by_cases ha : a = 1
  · simp [ha]
  · simp [ha, sum_apply_eq_zero ha]

/-- Over an algebraically closed characteristic-zero field, the full character
sum on a finite field has value `q-1` at one and zero elsewhere. -/
theorem sum_apply_finiteField {F C : Type*} [Field F] [Fintype F] [Field C]
    [CharZero C] [IsAlgClosed C] [Fintype (MulChar F C)] [DecidableEq F] (a : F) :
    ∑ χ : MulChar F C, χ a = if a = 1 then (Fintype.card F : C) - 1 else 0 := by
  classical
  rw [sum_apply_eq_ite]
  have hc : Fintype.card (MulChar F C) = Fintype.card F - 1 := by
    rw [← Nat.card_eq_fintype_card, MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity,
      Nat.card_eq_fintype_card, Fintype.card_units]
  rw [hc, Nat.cast_sub Fintype.card_pos, Nat.cast_one]

end MulChar

namespace Fintype

/-- Summation over units is summation over the nonzero elements of a field. -/
theorem sum_units_eq_sum_nonzero {F A : Type*} [GroupWithZero F] [Fintype F]
    [DecidableEq F] [AddCommMonoid A] (f : F → A) :
    ∑ u : Fˣ, f u = ∑ a ∈ Finset.univ.erase 0, f a := by
  calc
    _ = ∑ a : {a : F // a ≠ 0}, f a :=
      Fintype.sum_equiv unitsEquivNeZero _ _ fun _ => rfl
    _ = _ := (Finset.sum_subtype _ (by simp) f).symm

/-- An element of full order enumerates a finite group without repetition. -/
theorem sum_eq_sum_powers {G A : Type*} [Group G] [Fintype G] [AddCommMonoid A]
    (g : G) (hg : orderOf g = Fintype.card G) (f : G → A) :
    ∑ x : G, f x = ∑ j ∈ Finset.range (Fintype.card G), f (g ^ j) := by
  classical
  have hi : Set.InjOn (fun j : ℕ => g ^ j)
      (Finset.range (Fintype.card G) : Set ℕ) := by
    rw [Finset.coe_range, ← hg]
    exact pow_injOn_Iio_orderOf
  have he : (Finset.range (Fintype.card G)).image (fun j : ℕ => g ^ j) =
      Finset.univ := Finset.eq_univ_of_card _ (by
        rw [Finset.card_image_of_injOn hi, Finset.card_range])
  rw [← he, Finset.sum_image hi]

end Fintype

namespace AddChar

/-- Summing a nontrivial additive character over the nonzero field elements
subtracts the zero term from the usual orthogonality relation. -/
theorem sum_nonzero_mul {F C : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Field C] (θ : AddChar F C) (hθ : θ ≠ 1) (b : F) :
    ∑ v ∈ Finset.univ.erase 0, θ (v * b) =
      if b = 0 then (Fintype.card F : C) - 1 else -1 := by
  have h := AddChar.sum_mulShift b (AddChar.IsPrimitive.of_ne_one hθ)
  rw [← Finset.sum_erase_add Finset.univ (fun x : F => θ (x * b)) (Finset.mem_univ (0 : F))] at h
  by_cases hb : b = 0 <;> simp [hb] at h ⊢ <;> linear_combination h

/-- The additive orthogonality formula indexed by the multiplicative group. -/
theorem sum_units_mul {F C : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Field C] (θ : AddChar F C) (hθ : θ ≠ 1) (b : F) :
    ∑ v : Fˣ, θ (v * b) = if b = 0 then (Fintype.card F : C) - 1 else -1 := by
  rw [Fintype.sum_units_eq_sum_nonzero (fun v : F => θ (v * b))]
  exact sum_nonzero_mul θ hθ b

end AddChar

namespace MulChar

/-- A nontrivial multiplicative character sums to zero on the unit group of a
finite field. -/
theorem sum_units_eq_zero {F C : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Field C] {A : MulChar F C} (hA : A ≠ 1) : ∑ s : Fˣ, A s = 0 := by
  rw [Fintype.sum_units_eq_sum_nonzero (fun s : F => A s)]
  have h := Finset.sum_erase_add Finset.univ (fun s : F => A s)
    (Finset.mem_univ (0 : F))
  rw [MulChar.map_zero, add_zero] at h
  exact h.trans (MulChar.sum_eq_zero_of_ne_one hA)

end MulChar
