/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! # Rational valuation criteria for deep cusp parameters -/

@[expose] public section

namespace HilbertModularity.Cusp

/-- [TripathiGoswami], Proof of Proposition 4.7: for `p ≥ 5` and `d = (p-1)/2`, a parameter with
`ord_𝔭(t) ≥ 3d` has `ord_𝔭(t / ϖ^p) ≥ 3d - p = (p-3)/2 > 0`. -/
theorem depth_three_pos {p : ℕ} (hp : 5 ≤ p) (hodd : Odd p) :
    (3 * ((p - 1) / 2) : ℤ) - p = ((p : ℤ) - 3) / 2 ∧ 0 < (3 * ((p - 1) / 2) : ℤ) - p := by
  obtain ⟨k, rfl⟩ := hodd
  push_cast
  omega

/-- [TripathiGoswami], Appendix A: depth two gives `ord_𝔭(t/ϖ^p) = 2d - p = -1`. -/
theorem depth_two_neg {p : ℕ} (hodd : Odd p) : (2 * ((p - 1) / 2) : ℤ) - p = -1 := by
  obtain ⟨k, rfl⟩ := hodd
  push_cast
  omega

/-- For an odd conductor at least five, scaled positive depth begins exactly at depth three. -/
theorem scaled_depth_pos_iff {p : ℕ} (hp : 5 ≤ p) (hodd : Odd p) (z : ℤ) :
    0 < (((p - 1) / 2 : ℕ) : ℤ) * z - p ↔ 3 ≤ z := by
  have hd : (2 : ℤ) ≤ (((p - 1) / 2 : ℕ) : ℤ) := by omega
  have htwo := depth_two_neg hodd
  have hthree := (depth_three_pos hp hodd).2
  constructor
  · intro h
    by_contra hz
    have hz' : z ≤ 2 := by omega
    have hm := mul_le_mul_of_nonneg_left hz' (le_trans (by norm_num) hd)
    omega
  · intro hz
    have hm := mul_le_mul_of_nonneg_left hz (le_trans (by norm_num) hd)
    omega

/-- [TripathiGoswami], Proposition 4.7: for `ξ = A/B` in lowest terms with `A ≠ 0`,
`v_p(ξ) ≥ 3 ↔ p³ ∣ A`. -/
theorem padicValRat_ge_three_iff {p : ℕ} [Fact p.Prime] {A : ℤ} {B : ℕ} (hA : A ≠ 0)
    (hB : B ≠ 0) (hAB : Int.gcd A B = 1) :
    3 ≤ padicValRat p ((A : ℚ) / B) ↔ (p : ℤ) ^ 3 ∣ A := by
  have hp := (Fact.out : p.Prime)
  rw [padicValRat.div (by exact_mod_cast hA) (by exact_mod_cast hB), padicValRat.of_int,
    padicValRat.of_nat]
  by_cases hpB : p ∣ B
  · have hpA : ¬ (p : ℤ) ∣ A := by
      intro hpA
      have h1 := Int.dvd_gcd hpA (Int.natCast_dvd_natCast.mpr hpB)
      rw [hAB] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    have h0 : padicValInt p A = 0 := padicValInt.eq_zero_of_not_dvd hpA
    rw [h0]
    constructor
    · intro h; omega
    · intro h
      exact absurd ((dvd_pow_self _ (by norm_num)).trans h) hpA
  · rw [padicValNat.eq_zero_of_not_dvd hpB, padicValInt_dvd_iff]
    simp [hA]

/-- [TripathiGoswami], Proposition 4.7: for `ξ = A/B` in lowest terms with `ξ ≠ 1`,
`v_p(1 - ξ) ≥ 3 ↔ p³ ∣ (B - A)`. -/
theorem padicValRat_one_sub_ge_three_iff {p : ℕ} [Fact p.Prime] {A : ℤ} {B : ℕ}
    (hB : B ≠ 0) (hAB : Int.gcd A B = 1) (hξ : (A : ℚ) / B ≠ 1) :
    3 ≤ padicValRat p (1 - (A : ℚ) / B) ↔ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A) := by
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have e : 1 - (A : ℚ) / B = (((B : ℤ) - A : ℤ) : ℚ) / B := by
    push_cast
    field_simp
  rw [e]
  have hne : (B : ℤ) - A ≠ 0 := by
    intro h0
    apply hξ
    have : (A : ℚ) = B := by
      have : (A : ℤ) = B := by linarith
      exact_mod_cast this
    rw [this, div_self hBq]
  refine padicValRat_ge_three_iff hne hB ?_
  rw [← Int.isCoprime_iff_gcd_eq_one] at hAB ⊢
  obtain ⟨u, v, huv⟩ := hAB
  exact ⟨-u, v + u, by linear_combination huv⟩


/-- [TripathiGoswami], Remark 5.11: `ξ = p³/(p³+1)` has `v_p(ξ) = 3`. -/
theorem padicValRat_cubic_prime_parameter {p : ℕ} [Fact p.Prime] :
    padicValRat p ((p : ℚ) ^ 3 / ((p : ℚ) ^ 3 + 1)) = 3 := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 : (p : ℚ) ^ 3 + 1 = ((p ^ 3 + 1 : ℕ) : ℚ) := by push_cast; ring
  have hne : ((p ^ 3 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [h1, padicValRat.div (by positivity) hne, padicValRat.pow _, padicValRat.self hp.one_lt,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro hd
    have : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p (by norm_num))).mp hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- [TripathiGoswami], Remark 5.11: for every prime `q ≠ p`, `ξ = p³/(p³+1)` has
`v_q(ξ(ξ - 1)) = -2 v_q(p³ + 1) ≤ 0`. -/
theorem padicValRat_cubic_prime_parameter_mul_sub_one {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hqp : q ≠ p) :
    let ξ : ℚ := (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 + 1)
    padicValRat q (ξ * (ξ - 1)) = -2 * padicValRat q ((p : ℚ) ^ 3 + 1) ∧
      padicValRat q (ξ * (ξ - 1)) ≤ 0 := by
  intro ξ
  have hp := (Fact.out : p.Prime)
  have hq := (Fact.out : q.Prime)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 : (p : ℚ) ^ 3 + 1 = ((p ^ 3 + 1 : ℕ) : ℚ) := by push_cast; ring
  have hne : ((p : ℚ) ^ 3 + 1) ≠ 0 := by positivity
  have hξ : ξ * (ξ - 1) = -((p : ℚ) ^ 3 / ((p : ℚ) ^ 3 + 1) ^ 2) := by
    simp only [ξ]
    field_simp
    ring
  have hvp : padicValRat q ((p : ℚ) ^ 3) = 0 := by
    rw [padicValRat.pow _, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
    · simp
    · intro hd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd)
  have hpos : 0 ≤ padicValRat q ((p : ℚ) ^ 3 + 1) := by
    rw [h1, padicValRat.of_nat]; exact Int.natCast_nonneg _
  have key : padicValRat q (ξ * (ξ - 1)) = -2 * padicValRat q ((p : ℚ) ^ 3 + 1) := by
    rw [hξ, padicValRat.neg, padicValRat.div (by positivity) (by positivity),
      padicValRat.pow ((p : ℚ) ^ 3 + 1), hvp]
    push_cast; ring
  exact ⟨key, by rw [key]; linarith⟩

end HilbertModularity.Cusp
