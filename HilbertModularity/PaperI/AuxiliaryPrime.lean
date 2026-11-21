module
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public section
namespace HilbertModularity.PaperI

def cubicParameter (p : ℕ) : ℚ := (p : ℚ)^3 / (p^3+1)

theorem cubic_parameter_product (p : ℕ) :
    cubicParameter p * (cubicParameter p - 1) = -(p : ℚ)^3 / ((p^3+1)^2) := by
  unfold cubicParameter
  have hd : (p : ℚ)^3+1 ≠ 0 := by positivity
  field_simp
  ring

theorem cubic_parameter_depth (p : ℕ) [hp : Fact p.Prime] :
    padicValRat p (cubicParameter p) = 3 := by
  have hn : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hd : (p : ℚ)^3+1 ≠ 0 := by positivity
  have hnd : ¬p ∣ p^3+1 := by
    intro hh
    have hpow : p ∣ p^3 := dvd_pow_self p (by decide)
    exact hp.out.not_dvd_one ((Nat.dvd_add_iff_right hpow).mpr hh)
  have hv : padicValRat p ((p : ℚ)^3+1) = 0 := by
    norm_cast
    exact padicValNat.eq_zero_of_not_dvd hnd
  rw [cubicParameter, padicValRat.div (pow_ne_zero _ hn) hd, padicValRat.pow,
    padicValRat.self hp.out.one_lt, hv]
  decide

theorem cubic_parameter_auxiliary_valuations (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hne : q ≠ p) :
    padicValRat q (cubicParameter p * (cubicParameter p-1)) = -2*(padicValNat q (p^3+1) : ℤ) := by
  have hn : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hd : (p : ℚ)^3+1 ≠ 0 := by positivity
  have hq0 : padicValRat q (p : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).not.mpr hne)]
    rfl
  have hv : padicValRat q ((p : ℚ)^3+1) = (padicValNat q (p^3+1) : ℤ) := by
    exact_mod_cast (padicValRat.of_nat (p := q) (n := p^3+1))
  rw [cubic_parameter_product, padicValRat.div (neg_ne_zero.mpr (pow_ne_zero _ hn)) (pow_ne_zero _ hd),
    padicValRat.neg, padicValRat.pow, padicValRat.pow, hq0, hv]
  ring

theorem no_positive_auxiliary_valuation (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p) :
    padicValRat q (cubicParameter p * (cubicParameter p-1)) ≤ 0 := by
  rw [cubic_parameter_auxiliary_valuations p q hne]
  omega

theorem example_parameter_and_clearing :
    cubicParameter 5 = 125/126 ∧ cubicParameter 5*(cubicParameter 5-1) = -125/126^2 ∧
      (42 : ℚ)^5*(2-4*cubicParameter 5) = (-257233536 : ℤ) := by norm_num [cubicParameter]

end HilbertModularity.PaperI
