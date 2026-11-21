/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFive
public import HilbertModularity.Examples.PrimeFiveHypergeometric

/-! # Label selection in the level-five comparison

The exact McCarthy evaluations and the unordered real-multiplication trace
pairs force the finite comparison factor to be one at both worked primes.
The actual trace-pair and comparison identities remain explicit inputs, as in
[TripathiGoswami, Example 7.1].
-/

@[expose] public section

namespace HilbertModularity.Examples

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩

private theorem select_real_trace {a b : ℝ} {t ν : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t = a ∨ t = b)
    (hν : IsOfFinOrder ν) (he : (a : ℂ) = ν * t)
    (hab : ∀ n : ℕ, n ≠ 0 → (a / b) ^ n ≠ 1) : t = a ∧ ν = 1 := by
  obtain ⟨n, hn, hpow⟩ := hν.exists_pow_eq_one
  rcases ht with rfl | rfl
  · have hνa : ν = (a : ℂ) / a :=
      (eq_div_iff (Complex.ofReal_ne_zero.mpr ha)).mpr he.symm
    exact ⟨rfl, hνa.trans (div_self (Complex.ofReal_ne_zero.mpr ha))⟩
  · have hνb : ν = ((a / b : ℝ) : ℂ) := by
      rw [Complex.ofReal_div]
      exact (eq_div_iff (Complex.ofReal_ne_zero.mpr hb)).mpr he.symm
    rw [hνb] at hpow
    have hreal : (a / b) ^ n = 1 := by exact_mod_cast hpow
    exact False.elim (hab n (Nat.ne_of_gt hn) hreal)

/-- At eleven, the exact McCarthy value selects the positive-square-root-labelled trace
and forces the finite comparison factor to be one. -/
theorem comparison_character_11
    (A : MulChar (ZMod 11) ℂ) (hA : A 2 = fifthRoot)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) {t ν : ℂ}
    (ht : t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∨ t = (-1 - (Real.sqrt 5 : ℂ)) / 2)
    (hν : IsOfFinOrder ν)
    (he : Hypergeometric.rankTwoMcCarthySum θ A 125 = ν * t) :
    t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧ ν = 1 := by
  have hs : 1 < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have ha : (Real.sqrt 5 - 1) / 2 ≠ 0 := by linarith
  have hb : (-1 - Real.sqrt 5) / 2 ≠ 0 := by linarith
  rw [rankTwoMcCarthySum_11_eq_sqrt A hA θ hθ] at he
  have ht' : t = (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ) ∨
      t = (((-1 - Real.sqrt 5) / 2 : ℝ) : ℂ) := by simpa using ht
  have he' : (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ) = ν * t := by simpa using he
  simpa using select_real_trace ha hb ht' hν he' ratio_11_not_root_of_unity

/-- At forty-one, the exact McCarthy value selects the negative-square-root-labelled trace
and forces the finite comparison factor to be one. -/
theorem comparison_character_41
    (A : MulChar (ZMod 41) ℂ) (hA : A 6 = fifthRoot)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) {t ν : ℂ}
    (ht : t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∨
      t = (-1 + 5 * (Real.sqrt 5 : ℂ)) / 2)
    (hν : IsOfFinOrder ν)
    (he : Hypergeometric.rankTwoMcCarthySum θ A 125 = ν * t) :
    t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧ ν = 1 := by
  have hs : 1 < 5 * Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have ha : (-1 - 5 * Real.sqrt 5) / 2 ≠ 0 := by linarith
  have hb : (-1 + 5 * Real.sqrt 5) / 2 ≠ 0 := by linarith
  rw [rankTwoMcCarthySum_41_eq_sqrt A hA θ hθ] at he
  have ht' : t = (((-1 - 5 * Real.sqrt 5) / 2 : ℝ) : ℂ) ∨
      t = (((-1 + 5 * Real.sqrt 5) / 2 : ℝ) : ℂ) := by simpa using ht
  have he' : (((-1 - 5 * Real.sqrt 5) / 2 : ℝ) : ℂ) = ν * t := by simpa using he
  simpa using select_real_trace ha hb ht' hν he' ratio_41_not_root_of_unity

private theorem finite_character_value_isOfFinOrder
    {G : Type*} [Group G] (ν : G →* ℂˣ) (hν : (Set.range ν).Finite) (g : G) :
    IsOfFinOrder (ν g : ℂ) := by
  let : Finite ν.range := hν.to_subtype
  obtain ⟨n, hn, hp⟩ := (isOfFinOrder_of_finite (ν.rangeRestrict g)).exists_pow_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n, hn, ?_⟩
  simpa using congrArg (fun x : ν.range => ((x : ℂˣ) : ℂ)) hp

/-- The actual finite comparison character evaluates to one at the chosen eleven Frobenius,
provided its trace-pair and comparison identities are those of the fixed labelled factor. -/
theorem finite_comparison_character_11
    {G : Type*} [Group G] (ν : G →* ℂˣ) (hν : (Set.range ν).Finite) (g : G)
    (A : MulChar (ZMod 11) ℂ) (hA : A 2 = fifthRoot)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) (t : ℂ)
    (ht : t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∨ t = (-1 - (Real.sqrt 5 : ℂ)) / 2)
    (he : Hypergeometric.rankTwoMcCarthySum θ A 125 = (ν g : ℂ) * t) :
    t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧ ν g = 1 := by
  obtain ⟨ht, hn⟩ := comparison_character_11 A hA θ hθ ht
    (finite_character_value_isOfFinOrder ν hν g) he
  exact ⟨ht, Units.ext hn⟩

/-- The actual finite comparison character evaluates to one at the chosen forty-one Frobenius,
with the negative-square-root-labelled trace selected by the exact McCarthy evaluation. -/
theorem finite_comparison_character_41
    {G : Type*} [Group G] (ν : G →* ℂˣ) (hν : (Set.range ν).Finite) (g : G)
    (A : MulChar (ZMod 41) ℂ) (hA : A 6 = fifthRoot)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) (t : ℂ)
    (ht : t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∨
      t = (-1 + 5 * (Real.sqrt 5 : ℂ)) / 2)
    (he : Hypergeometric.rankTwoMcCarthySum θ A 125 = (ν g : ℂ) * t) :
    t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧ ν g = 1 := by
  obtain ⟨ht, hn⟩ := comparison_character_41 A hA θ hθ ht
    (finite_character_value_isOfFinOrder ν hν g) he
  exact ⟨ht, Units.ext hn⟩

end HilbertModularity.Examples
