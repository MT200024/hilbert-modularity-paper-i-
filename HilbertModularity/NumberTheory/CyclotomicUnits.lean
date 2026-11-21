/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.LinearCombination

/-! # Cyclotomic unit identities and their reductions -/

@[expose] public section

namespace HilbertModularity.Cyclotomic

open Polynomial Finset

section Cyclotomic

variable {K : Type*} [Field K]

/-- `ω_j = ζ^j + ζ^{-j}`. -/
def rootTrace (ζ : K) (j : ℕ) : K := ζ ^ j + ζ⁻¹ ^ j

/-- `ϖ = (1 - ζ)(1 - ζ⁻¹) = 2 - ω₁`. -/
def realCyclotomicParameter (ζ : K) : K := (1 - ζ) * (1 - ζ⁻¹)

/-- `r_j = ((1-ζ^j)/(1-ζ)) · ((1-ζ^{-j})/(1-ζ^{-1}))`, written as a product of two
geometric sums so that it is visibly integral. -/
def cyclotomicUnitRatio (ζ : K) (j : ℕ) : K := (∑ i ∈ range j, ζ ^ i) * (∑ i ∈ range j, ζ⁻¹ ^ i)

theorem realCyclotomicParameter_eq (ζ : K) (hζ : ζ ≠ 0) : realCyclotomicParameter ζ = 2 - rootTrace ζ 1 := by
  unfold realCyclotomicParameter rootTrace
  linear_combination mul_inv_cancel₀ hζ

/-- [TripathiGoswami], Lemma 4.6: `2 - ω_j = (1 - ζ^j)(1 - ζ^{-j})`. -/
theorem two_sub_rootTrace (ζ : K) (hζ : ζ ≠ 0) (j : ℕ) :
    2 - rootTrace ζ j = (1 - ζ ^ j) * (1 - ζ⁻¹ ^ j) := by
  have h : ζ ^ j * ζ⁻¹ ^ j = 1 := by rw [← mul_pow, mul_inv_cancel₀ hζ, one_pow]
  unfold rootTrace
  linear_combination (-1 : K) * h

/-- [TripathiGoswami], Lemma 4.6: `r_j = (2 - ω_j) / ϖ`. -/
theorem cyclotomicUnitRatio_mul_realCyclotomicParameter (ζ : K) (hζ : ζ ≠ 0) (j : ℕ) : cyclotomicUnitRatio ζ j * realCyclotomicParameter ζ = 2 - rootTrace ζ j := by
  rw [two_sub_rootTrace ζ hζ j, ← mul_neg_geom_sum, ← mul_neg_geom_sum]
  unfold cyclotomicUnitRatio realCyclotomicParameter
  ring

/-- The integral geometric-sum expression agrees with the quotient defining
the scaled roots whenever the scaling parameter is nonzero. -/
theorem cyclotomicUnitRatio_eq_div (ζ : K) (hζ : ζ ≠ 0) (hϖ : realCyclotomicParameter ζ ≠ 0) (j : ℕ) :
    cyclotomicUnitRatio ζ j = (2 - rootTrace ζ j) / realCyclotomicParameter ζ :=
  (eq_div_iff hϖ).mpr (cyclotomicUnitRatio_mul_realCyclotomicParameter ζ hζ j)

end Cyclotomic

section Integral

variable {R : Type*} [CommRing R] [IsDomain R]

/-- [TripathiGoswami], Lemma 4.6: for `ζ` a primitive `p`-th root of unity in a domain and `j` prime to
`p`, the geometric sum `(1 - ζ^j)/(1 - ζ) = ∑_{i<j} ζ^i` is a unit (a cyclotomic unit). -/
theorem isUnit_geomSum {p : ℕ} (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p) {j : ℕ}
    (hj : j.Coprime p) : IsUnit (∑ i ∈ range j, ζ ^ i) :=
  hζ.geom_sum_isUnit hp.two_le hj

omit [IsDomain R] in
/-- [TripathiGoswami], Lemma 4.6: modulo `1 - ζ`, the geometric sum `∑_{i<j} ζ^i` reduces to `j`. -/
theorem geomSum_sub_mem (ζ : R) (j : ℕ) :
    (∑ i ∈ range j, ζ ^ i) - j ∈ Ideal.span {1 - ζ} := by
  rw [Ideal.mem_span_singleton]
  have h : (∑ i ∈ range j, ζ ^ i) - j = ∑ i ∈ range j, (ζ ^ i - 1) := by
    simp [Finset.sum_sub_distrib]
  rw [h]
  refine Finset.dvd_sum fun i _ => ?_
  have := sub_dvd_pow_sub_pow (1 : R) ζ i
  rw [one_pow] at this
  rw [← dvd_neg, neg_sub]
  exact this

/-- [TripathiGoswami], Lemma 4.6, integral form: `r_j = S_j(ζ) S_j(ζ^{-1})` with `ζ^{-1} = ζ^{p-1}`; it is a
unit, and `r_j ≡ j² (mod 1 - ζ)`. -/
theorem cyclotomicUnitRatio_isUnit_and_mod {p : ℕ} (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p) {j : ℕ}
    (hj : j.Coprime p) :
    IsUnit ((∑ i ∈ range j, ζ ^ i) * (∑ i ∈ range j, (ζ ^ (p - 1)) ^ i)) ∧
      (∑ i ∈ range j, ζ ^ i) * (∑ i ∈ range j, (ζ ^ (p - 1)) ^ i) - (j : R) ^ 2 ∈
        Ideal.span {1 - ζ} := by
  have hcop : (p - 1).Coprime p := by
    have h1 : 1 ≤ p := hp.one_lt.le
    have : p = (p - 1) + 1 := by omega
    conv => rhs; rw [this]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hζ' : IsPrimitiveRoot (ζ ^ (p - 1)) p := hζ.pow_of_coprime _ hcop
  refine ⟨(isUnit_geomSum hp hζ hj).mul (isUnit_geomSum hp hζ' hj), ?_⟩
  have h1 := geomSum_sub_mem ζ j
  have h2 := geomSum_sub_mem (ζ ^ (p - 1)) j
  rw [Ideal.mem_span_singleton] at h1 h2 ⊢
  have h3 : (1 - ζ) ∣ 1 - ζ ^ (p - 1) := by
    have := sub_dvd_pow_sub_pow (1 : R) ζ (p - 1)
    rwa [one_pow] at this
  have h2' := h3.trans h2
  have e : (∑ i ∈ range j, ζ ^ i) * (∑ i ∈ range j, (ζ ^ (p - 1)) ^ i) - (j : R) ^ 2 =
      (∑ i ∈ range j, ζ ^ i) * ((∑ i ∈ range j, (ζ ^ (p - 1)) ^ i) - j) +
        j * ((∑ i ∈ range j, ζ ^ i) - j) := by ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right h2' _) (dvd_mul_of_dvd_right h1 _)

end Integral

/-- [TripathiGoswami], Lemma 4.6: the reductions `0, 1², 2², …, d²` (`d = (p-1)/2`) are pairwise distinct in
`𝔽_p`. -/
theorem sq_injOn {p : ℕ} [Fact p.Prime] {i j : ℕ} (hi : 1 ≤ i) (hi' : i ≤ (p - 1) / 2)
    (hj : 1 ≤ j) (hj' : j ≤ (p - 1) / 2) (h : ((i : ZMod p)) ^ 2 = (j : ZMod p) ^ 2) : i = j := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hfac : ((i : ZMod p) - j) * ((i : ZMod p) + j) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h1
  · have h2 : ((i : ℕ) : ZMod p) = (j : ℕ) := sub_eq_zero.mp h1
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  · have h2 : (((i + j : ℕ)) : ZMod p) = 0 := by push_cast; exact h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by omega) h2
    omega

theorem sq_ne_zero {p : ℕ} [Fact p.Prime] {j : ℕ} (hj : 1 ≤ j) (hj' : j ≤ (p - 1) / 2) :
    ((j : ZMod p)) ^ 2 ≠ 0 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  refine pow_ne_zero 2 ?_
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  omega

end HilbertModularity.Cyclotomic
