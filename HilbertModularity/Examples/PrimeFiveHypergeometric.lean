/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.CharacterCount
public import HilbertModularity.NumberTheory.CharacterGenerator
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Exact finite hypergeometric values at level five

The character-count formula gives exact algebraic evaluations of the two sums
in [TripathiGoswami, Example 7.1].
-/

@[expose] public section

namespace HilbertModularity.Examples

open scoped BigOperators

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The indicated generator of the multiplicative group of `𝔽₁₁`. -/
def generator11 : (ZMod 11)ˣ := Units.mk0 (2 : ZMod 11) (by decide)

/-- The indicated generator of the multiplicative group of `𝔽₄₁`. -/
def generator41 : (ZMod 41)ˣ := Units.mk0 (6 : ZMod 41) (by decide)

/-- Two has exact multiplicative order ten modulo eleven. -/
theorem generator11_isPrimitiveRoot : IsPrimitiveRoot generator11 10 := by
  apply (IsPrimitiveRoot.iff (by decide)).mpr
  constructor
  · decide
  · intro j hj0 hj10
    interval_cases j <;> decide

/-- Six has exact multiplicative order forty modulo forty-one. -/
theorem generator41_isPrimitiveRoot : IsPrimitiveRoot generator41 40 := by
  apply (IsPrimitiveRoot.iff (by decide)).mpr
  constructor
  · decide
  · intro j hj0 hj40
    interval_cases j <;> decide

/-- The nonzero quadratic-root counts, indexed by successive powers of two. -/
theorem quadratic_root_counts_11 :
    (fun j : Fin 10 => (Finset.univ.filter (fun t : (ZMod 11)ˣ =>
      (t : ZMod 11) ^ 2 + ((generator11 ^ (j : ℕ) : (ZMod 11)ˣ) + 1 : ZMod 11) * t +
        (generator11 ^ (j : ℕ) : (ZMod 11)ˣ) * (125 : ZMod 11) = 0)).card) =
      ![0, 0, 2, 0, 1, 2, 1, 0, 2, 0] := by
  decide +kernel

/-- The nonzero quadratic-root counts, indexed by successive powers of six. -/
theorem quadratic_root_counts_41 :
    (fun j : Fin 40 => (Finset.univ.filter (fun t : (ZMod 41)ˣ =>
      (t : ZMod 41) ^ 2 + ((generator41 ^ (j : ℕ) : (ZMod 41)ˣ) + 1 : ZMod 41) * t +
        (generator41 ^ (j : ℕ) : (ZMod 41)ˣ) * (125 : ZMod 41) = 0)).card) =
      ![2, 2, 0, 0, 2, 0, 0, 0, 1, 2, 0, 2, 0, 2, 0, 2, 0, 0, 2, 2,
        2, 2, 2, 0, 0, 2, 0, 2, 0, 2, 0, 2, 1, 0, 0, 0, 2, 0, 0, 2] := by
  decide +kernel

/-- The weighted root count over `𝔽₁₁`, with the generator convention fixed. -/
theorem neg_weighted_root_count_11 (A : MulChar (ZMod 11) ℂ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ 5) (hA : A 2 = ζ) :
    -(∑ s : (ZMod 11)ˣ, A s * (Finset.univ.filter (fun t : (ZMod 11)ˣ =>
      (t : ZMod 11) ^ 2 + ((s : ZMod 11) + 1) * t + (s : ZMod 11) * 125 = 0)).card) =
      ζ + ζ ^ 4 := by
  classical
  have hg : orderOf generator11 = Fintype.card (ZMod 11)ˣ := by
    rw [← generator11_isPrimitiveRoot.eq_orderOf, ZMod.card_units]
  rw [Fintype.sum_eq_sum_powers generator11 hg]
  simp only [ZMod.card_units]
  rw [← Fin.sum_univ_eq_sum_range]
  have hv (j : ℕ) : A (generator11 ^ j : (ZMod 11)ˣ) = ζ ^ (j % 5) := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    change A 2 ^ j = _
    rw [hA, pow_eq_pow_mod j hζ.pow_eq_one]
  simp_rw [hv]
  have hc := quadratic_root_counts_11
  change (fun j : Fin 10 => _) = _ at hc
  simp_rw [congrFun hc]
  norm_num [Fin.sum_univ_succ]
  have hs := hζ.geom_sum_eq_zero (by decide)
  norm_num [Finset.sum_range_succ] at hs
  linear_combination -2 * hs

/-- The weighted root count over `𝔽₄₁`, with the generator convention fixed. -/
theorem neg_weighted_root_count_41 (A : MulChar (ZMod 41) ℂ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ 5) (hA : A 6 = ζ) :
    -(∑ s : (ZMod 41)ˣ, A s * (Finset.univ.filter (fun t : (ZMod 41)ˣ =>
      (t : ZMod 41) ^ 2 + ((s : ZMod 41) + 1) * t + (s : ZMod 41) * 125 = 0)).card) =
      -3 - 5 * (ζ + ζ ^ 4) := by
  classical
  have hg : orderOf generator41 = Fintype.card (ZMod 41)ˣ := by
    rw [← generator41_isPrimitiveRoot.eq_orderOf, ZMod.card_units]
  rw [Fintype.sum_eq_sum_powers generator41 hg]
  simp only [ZMod.card_units]
  rw [← Fin.sum_univ_eq_sum_range]
  have hv (j : ℕ) : A (generator41 ^ j : (ZMod 41)ˣ) = ζ ^ (j % 5) := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    change A 6 ^ j = _
    rw [hA, pow_eq_pow_mod j hζ.pow_eq_one]
  simp_rw [hv]
  have hc := quadratic_root_counts_41
  change (fun j : Fin 40 => _) = _ at hc
  simp_rw [congrFun hc]
  norm_num [Fin.sum_univ_succ]
  have hs := hζ.geom_sum_eq_zero (by decide)
  norm_num [Finset.sum_range_succ] at hs
  linear_combination -5 * hs

/-- The complex fifth root of unity selected in the numerical examples. -/
noncomputable def fifthRoot : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 5)

/-- The selected complex root has exact order five. -/
theorem fifthRoot_isPrimitiveRoot : IsPrimitiveRoot fifthRoot 5 :=
  Complex.isPrimitiveRoot_exp 5 (by decide)

/-- The real trace of the selected fifth root gives the positive square root
of five with the manuscript's sign convention. -/
theorem fifthRoot_add_fourth_pow :
    fifthRoot + fifthRoot ^ 4 = ((Real.sqrt 5 : ℂ) - 1) / 2 := by
  have hi : fifthRoot ^ 4 = fifthRoot⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact fifthRoot_isPrimitiveRoot.pow_eq_one
  have hc : Real.cos (2 * (Real.pi / 5)) = (Real.sqrt 5 - 1) / 4 := by
    rw [Real.cos_two_mul, Real.cos_pi_div_five]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have ht : fifthRoot + fifthRoot⁻¹ =
      2 * Complex.cos ((2 * (Real.pi / 5) : ℝ) : ℂ) := by
    rw [Complex.cos, fifthRoot, ← Complex.exp_neg]
    push_cast
    ring
  rw [hi, ht, ← Complex.ofReal_cos, hc]
  push_cast
  ring

/-- The McCarthy sum over `𝔽₁₁` in terms of its specified fifth root. -/
theorem rankTwoMcCarthySum_11 (A : MulChar (ZMod 11) ℂ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ 5) (hA : A 2 = ζ)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) :
    Hypergeometric.rankTwoMcCarthySum θ A 125 = ζ + ζ ^ 4 := by
  have hA1 : A ≠ 1 := by
    intro h
    apply hζ.ne_one (by decide)
    rw [← hA, h]
    exact MulChar.one_apply_coe generator11
  have hneg : A (-1) = 1 := by
    rw [← show (generator11 : ZMod 11) ^ 5 = -1 from by decide, map_pow]
    change A 2 ^ 5 = 1
    rw [hA, hζ.pow_eq_one]
  rw [Hypergeometric.rankTwoMcCarthySum_eq_neg_weighted_root_count
    A hA1 hneg θ hθ 125 (by decide)]
  exact neg_weighted_root_count_11 A ζ hζ hA

/-- The McCarthy sum over `𝔽₄₁` in terms of its specified fifth root. -/
theorem rankTwoMcCarthySum_41 (A : MulChar (ZMod 41) ℂ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ 5) (hA : A 6 = ζ)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) :
    Hypergeometric.rankTwoMcCarthySum θ A 125 = -3 - 5 * (ζ + ζ ^ 4) := by
  have hA1 : A ≠ 1 := by
    intro h
    apply hζ.ne_one (by decide)
    rw [← hA, h]
    exact MulChar.one_apply_coe generator41
  have hneg : A (-1) = 1 := by
    rw [← show (generator41 : ZMod 41) ^ 20 = -1 from by decide, map_pow]
    change A 6 ^ 20 = 1
    rw [hA, show 20 = 5 * 4 from rfl, pow_mul, hζ.pow_eq_one, one_pow]
  rw [Hypergeometric.rankTwoMcCarthySum_eq_neg_weighted_root_count
    A hA1 hneg θ hθ 125 (by decide)]
  exact neg_weighted_root_count_41 A ζ hζ hA

/-- The exact value at eleven in [TripathiGoswami, Example 7.1]. -/
theorem rankTwoMcCarthySum_11_eq_sqrt (A : MulChar (ZMod 11) ℂ)
    (hA : A 2 = fifthRoot) (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) :
    Hypergeometric.rankTwoMcCarthySum θ A 125 = ((Real.sqrt 5 : ℂ) - 1) / 2 := by
  rw [rankTwoMcCarthySum_11 A fifthRoot fifthRoot_isPrimitiveRoot hA θ hθ,
    fifthRoot_add_fourth_pow]

/-- The exact value at forty-one in [TripathiGoswami, Example 7.1]. -/
theorem rankTwoMcCarthySum_41_eq_sqrt (A : MulChar (ZMod 41) ℂ)
    (hA : A 6 = fifthRoot) (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) :
    Hypergeometric.rankTwoMcCarthySum θ A 125 = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 := by
  rw [rankTwoMcCarthySum_41 A fifthRoot fifthRoot_isPrimitiveRoot hA θ hθ,
    fifthRoot_add_fourth_pow]
  ring

/-- The prescribed character over `𝔽₁₁` exists and has order five. -/
theorem exists_character_11 :
    ∃ A : MulChar (ZMod 11) ℂ, A 2 = fifthRoot ∧ orderOf A = 5 := by
  have hg : orderOf generator11 = Fintype.card (ZMod 11)ˣ := by
    rw [← generator11_isPrimitiveRoot.eq_orderOf, ZMod.card_units]
  exact MulChar.exists_apply_eq_of_orderOf_eq_card hg fifthRoot_isPrimitiveRoot
    (by rw [ZMod.card_units]; decide)

/-- The prescribed character over `𝔽₄₁` exists and has order five. -/
theorem exists_character_41 :
    ∃ A : MulChar (ZMod 41) ℂ, A 6 = fifthRoot ∧ orderOf A = 5 := by
  have hg : orderOf generator41 = Fintype.card (ZMod 41)ˣ := by
    rw [← generator41_isPrimitiveRoot.eq_orderOf, ZMod.card_units]
  exact MulChar.exists_apply_eq_of_orderOf_eq_card hg fifthRoot_isPrimitiveRoot
    (by rw [ZMod.card_units]; decide)

end HilbertModularity.Examples
