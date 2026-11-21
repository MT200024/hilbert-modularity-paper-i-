/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicUnits
public import HilbertModularity.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.FieldTheory.KummerExtension

/-! # Cyclotomic factorization of the plus-family polynomial -/

@[expose] public section

namespace HilbertModularity.Hyperelliptic

open Polynomial Finset Cyclotomic

variable {K : Type*} [Field K]

/-- `g(X) = ∏_{j=1}^{d} (X + ω_j)`, the characteristic polynomial of `-(ζ + ζ⁻¹)`
(its roots are the conjugates `-ω_j`, `1 ≤ j ≤ d = (p-1)/2`). It is also the
polynomial `g₀` of the proof of Proposition 4.7. -/
noncomputable def negTracePolynomial (ζ : K) (p : ℕ) : K[X] :=
  ∏ j ∈ Icc 1 ((p - 1) / 2), (X + C (rootTrace ζ j))

/-- `f(x) = x · g(x² - 2)` (paper, (4.2)). -/
noncomputable def cyclotomicChebyshevPolynomial (ζ : K) (p : ℕ) : K[X] := X * (negTracePolynomial ζ p).comp (X ^ 2 - 2)

/-- Reindex a product over `Icc 1 d` as a product over `range d`. -/
private lemma prod_Icc_one_eq_prod_range {M : Type*} [CommMonoid M] (F : ℕ → M) (d : ℕ) :
    ∏ j ∈ Icc 1 d, F j = ∏ k ∈ range d, F (k + 1) := by
  induction d with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

/-- For `p` odd and `ζ` a primitive `p`-th root of unity, `∏_{k<p} (w + ζ^k) = w^p + 1`. -/
private lemma prod_range_add_pow_eq {p : ℕ} (hp : 0 < p) (hodd : Odd p) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (w : K) :
    ∏ k ∈ range p, (w + ζ ^ k) = w ^ p + 1 := by
  have h := congrArg (eval (-w)) (X_pow_sub_C_eq_prod hζ hp (one_pow p))
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod, mul_one] at h
  rw [hodd.neg_pow] at h
  have e : ∏ k ∈ range p, (-w - ζ ^ k) = ∏ k ∈ range p, -(w + ζ ^ k) :=
    Finset.prod_congr rfl fun k _ => by ring
  rw [e, Finset.prod_neg, card_range, hodd.neg_one_pow] at h
  linear_combination h

/-- `w^d · g(w + w⁻¹) · (w + 1) = w^p + 1` for `w ≠ 0`, where `d = (p-1)/2`. -/
private lemma negTracePolynomial_eval_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (w : K) (hw : w ≠ 0) :
    w ^ ((p - 1) / 2) * (negTracePolynomial ζ p).eval (w + w⁻¹) * (w + 1) = w ^ p + 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  rw [← prod_range_add_pow_eq hp.pos hodd hζ w]
  obtain ⟨d, hd⟩ := hodd
  subst hd
  have hd' : (2 * d + 1 - 1) / 2 = d := by omega
  unfold negTracePolynomial
  rw [hd', eval_prod, prod_Icc_one_eq_prod_range, Finset.prod_range_succ',
    show 2 * d = d + d by ring, Finset.prod_range_add, pow_zero]
  have h2 : ∏ k ∈ range d, (w + ζ ^ (d + k + 1)) = ∏ k ∈ range d, (w + ζ⁻¹ ^ (k + 1)) := by
    rw [← Finset.prod_range_reflect (fun k => w + ζ ^ (d + k + 1)) d]
    refine prod_congr rfl fun k hk => ?_
    simp only [mem_range] at hk
    show w + ζ ^ (d + (d - 1 - k) + 1) = _
    have : ζ ^ (d + (d - 1 - k) + 1) * ζ ^ (k + 1) = 1 := by
      rw [← pow_add, show d + (d - 1 - k) + 1 + (k + 1) = 2 * d + 1 by omega, hζ.pow_eq_one]
    rw [inv_pow, eq_inv_of_mul_eq_one_left this]
  rw [h2]
  have hc : w ^ d = ∏ _k ∈ range d, w := by simp
  rw [hc, ← prod_mul_distrib, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun k _ => ?_
  have hww : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  have hzz : ζ ^ (k + 1) * ζ⁻¹ ^ (k + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
  simp only [eval_add, eval_X, eval_C]
  unfold rootTrace
  linear_combination hww - hzz

/-- Auxiliary form of `cyclotomicChebyshevPolynomial_eval_add_inv`, used in the proof of `cyclotomicChebyshevPolynomial_add_two`. -/
private lemma cyclotomicChebyshevPolynomial_eval_add_inv_aux {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (z : K) (hz : z ≠ 0) :
    (cyclotomicChebyshevPolynomial ζ p).eval (z + z⁻¹) = z ^ p + z⁻¹ ^ p := by
  unfold cyclotomicChebyshevPolynomial
  rw [eval_mul, eval_X, eval_comp]
  simp only [eval_sub, eval_pow, eval_X, eval_ofNat]
  set u := z⁻¹ with hu
  have hzu : z * u = 1 := mul_inv_cancel₀ hz
  have e : (z + u) ^ 2 - 2 = z ^ 2 + (z ^ 2)⁻¹ := by
    rw [← inv_pow, ← hu]
    linear_combination 2 * hzu
  rw [e]
  have h := negTracePolynomial_eval_mul hp hp2 hζ (z ^ 2) (pow_ne_zero 2 hz)
  set B := eval (z ^ 2 + (z ^ 2)⁻¹) (negTracePolynomial ζ p)
  have e3 : z ^ p * u ^ p = 1 := by rw [← mul_pow, hzu, one_pow]
  obtain ⟨d, hd⟩ := hp.odd_of_ne_two hp2
  subst hd
  rw [show (2 * d + 1 - 1) / 2 = d by omega] at h
  apply mul_left_cancel₀ (pow_ne_zero (2 * d + 1) hz)
  linear_combination h + z ^ (2 * d) * B * hzu - e3

/-- A polynomial over a characteristic-zero field is determined by its values
on reciprocal pairs. -/
private lemma eq_of_eval_add_inv_eq [CharZero K] (P Q : K[X])
    (key : ∀ z : K, z ≠ 0 → P.eval (z + z⁻¹) = Q.eval (z + z⁻¹)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : K) + 1) + ((n : K) + 1)⁻¹)
    ?_ ?_
  · intro a b hab
    simp only at hab
    have ha : (a : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero a
    have hb : (b : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero b
    have hx := mul_inv_cancel₀ ha
    have hy := mul_inv_cancel₀ hb
    have hprod : ((a : K) + 1 - ((b : K) + 1)) * (((a : K) + 1) * ((b : K) + 1) - 1) = 0 := by
      linear_combination ((a : K) + 1) * ((b : K) + 1) * hab - ((b : K) + 1) * hx +
        ((a : K) + 1) * hy
    rcases mul_eq_zero.mp hprod with h | h
    · have : (a : K) = b := by linear_combination h
      exact_mod_cast this
    · have h' : ((a : K) + 1) * ((b : K) + 1) = 1 := by linear_combination h
      have : (a + 1) * (b + 1) = 1 := by exact_mod_cast h'
      have h1 := Nat.eq_one_of_mul_eq_one_right this
      have h2 := Nat.eq_one_of_mul_eq_one_left this
      omega
  · intro n
    exact key _ (Nat.cast_add_one_ne_zero n)

/-- [TripathiGoswami], Proof of Proposition 4.7: `f(x) + 2 = (x + 2) g₀(x)²`. -/
theorem cyclotomicChebyshevPolynomial_add_two [CharZero K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    cyclotomicChebyshevPolynomial ζ p + 2 = (X + 2) * negTracePolynomial ζ p ^ 2 := by
  have key : ∀ z : K, z ≠ 0 →
      eval (z + z⁻¹) (cyclotomicChebyshevPolynomial ζ p + 2) = eval (z + z⁻¹) ((X + 2) * negTracePolynomial ζ p ^ 2) := by
    intro z hz
    rw [eval_add, cyclotomicChebyshevPolynomial_eval_add_inv_aux hp hp2 hζ z hz, eval_mul, eval_pow, eval_add, eval_X]
    simp only [eval_ofNat]
    have h := negTracePolynomial_eval_mul hp hp2 hζ z hz
    set G := eval (z + z⁻¹) (negTracePolynomial ζ p)
    set u := z⁻¹ with hu
    have hzu : z * u = 1 := mul_inv_cancel₀ hz
    have e3 : z ^ p * u ^ p = 1 := by rw [← mul_pow, hzu, one_pow]
    obtain ⟨d, hd⟩ := hp.odd_of_ne_two hp2
    subst hd
    rw [show (2 * d + 1 - 1) / 2 = d by omega] at h
    apply mul_left_cancel₀ (pow_ne_zero (2 * d + 1) hz)
    linear_combination e3 - (z ^ d * G * (z + 1) + z ^ (2 * d + 1) + 1) * h - z ^ (2 * d) * G ^ 2 * hzu
  exact eq_of_eval_add_inv_eq _ _ key

/-- The manuscript plus polynomial is the integral rescaled Chebyshev polynomial. -/
theorem cyclotomicChebyshevPolynomial_eq_chebyshev [CharZero K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : cyclotomicChebyshevPolynomial ζ p = Polynomial.Chebyshev.C K p := by
  apply eq_of_eval_add_inv_eq
  intro z hz
  rw [cyclotomicChebyshevPolynomial_eval_add_inv_aux hp hp2 hζ z hz, Polynomial.Chebyshev.C_eval_add_inv p z hz]

/-- `f` is the Dickson polynomial `D_p(x, 1)`: `f(z + z⁻¹) = z^p + z^{-p}`. -/
theorem cyclotomicChebyshevPolynomial_eval_add_inv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (z : K) (hz : z ≠ 0) :
    (cyclotomicChebyshevPolynomial ζ p).eval (z + z⁻¹) = z ^ p + z⁻¹ ^ p :=
  cyclotomicChebyshevPolynomial_eval_add_inv_aux hp hp2 hζ z hz

/-- For `p = 5`: `f(x) = x⁵ - 5x³ + 5x` (§6). -/
theorem cyclotomicChebyshevPolynomial_five {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    cyclotomicChebyshevPolynomial ζ 5 = X ^ 5 - 5 * X ^ 3 + 5 * X := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    have := hζ.geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ] using this
  have hinv : ζ⁻¹ = ζ ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h5)
  have hA : rootTrace ζ 1 + rootTrace ζ 2 = -1 := by
    unfold rootTrace; rw [hinv]; linear_combination hsum + ζ ^ 3 * h5
  have hB : rootTrace ζ 1 * rootTrace ζ 2 = -1 := by
    unfold rootTrace; rw [hinv]
    linear_combination hsum + (ζ ^ 4 + ζ + ζ ^ 2 * (ζ ^ 5 + 1)) * h5
  have hA' : C (rootTrace ζ 1) + C (rootTrace ζ 2) = (-1 : K[X]) := by rw [← C_add, hA, C_neg, C_1]
  have hB' : C (rootTrace ζ 1) * C (rootTrace ζ 2) = (-1 : K[X]) := by rw [← C_mul, hB, C_neg, C_1]
  unfold cyclotomicChebyshevPolynomial negTracePolynomial
  rw [show (5 - 1) / 2 = 2 by norm_num, show Icc 1 2 = {1, 2} by rfl, prod_pair (by norm_num)]
  simp only [mul_comp, add_comp, X_comp, C_comp]
  linear_combination (X * (X ^ 2 - 2)) * hA' + X * hB'

end HilbertModularity.Hyperelliptic
