/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicBaseChange
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-! # Cyclotomic polynomials over the ramified `p`-adic field

The shift of the prime cyclotomic polynomial is Eisenstein at the maximal ideal
of `Z_p`. This proves irreducibility over `Q_p`, the algebraic prerequisite for
the ramified coefficient field in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace Polynomial

variable (p : ℕ) [Fact p.Prime]

/-- The prime-power cyclotomic polynomial shifted by one is Eisenstein over `Z_p`. -/
theorem cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt_padic (k : ℕ) :
    ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).IsEisensteinAt
      (IsLocalRing.maximalIdeal ℤ_[p]) := by
  have hm : ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).Monic := by
    simpa using (cyclotomic.monic (p ^ (k + 1)) ℤ_[p]).comp_X_add_C 1
  refine hm.isEisensteinAt_of_mem_of_notMem (Ideal.IsMaximal.ne_top (inferInstance : (IsLocalRing.maximalIdeal ℤ_[p]).IsMaximal)) ?_ ?_
  · have hw := (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k).isWeaklyEisensteinAt.map
      (Int.castRingHom ℤ_[p])
    simp only [map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one,
      Ideal.map_span, Set.image_singleton, map_natCast] at hw
    rw [← PadicInt.maximalIdeal_eq_span_p] at hw
    intro n hn
    exact hw.mem hn
  · rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one, zero_add,
      eval_one_cyclotomic_prime_pow, PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have hp0 : (p : ℤ_[p]) ≠ 0 := PadicInt.prime_p.ne_zero
    have : (p : ℤ_[p]) ∣ 1 := by
      apply (mul_dvd_mul_iff_left hp0).mp
      simpa only [pow_two, mul_one] using h
    exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one this)

/-- The prime cyclotomic polynomial shifted by one is Eisenstein over `Z_p`. -/
theorem cyclotomic_comp_X_add_one_isEisensteinAt_padic :
    ((cyclotomic p ℤ_[p]).comp (X + 1)).IsEisensteinAt
      (IsLocalRing.maximalIdeal ℤ_[p]) := by
  simpa only [Nat.zero_add, pow_one] using
    cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt_padic p 0

/-- The prime-power cyclotomic polynomial is irreducible over the `p`-adic numbers. -/
theorem cyclotomic_prime_pow_irreducible_padic (k : ℕ) :
    Irreducible (cyclotomic (p ^ (k + 1)) ℚ_[p]) := by
  have hm : ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).Monic := by
    simpa using (cyclotomic.monic (p ^ (k + 1)) ℤ_[p]).comp_X_add_C 1
  have hd : 0 < ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).natDegree := by
    rw [natDegree_comp, show (X + 1 : ℤ_[p][X]) = X + C 1 by simp,
      natDegree_X_add_C, mul_one, natDegree_cyclotomic]
    exact Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos _)
  have hi := (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt_padic p k).irreducible
    (inferInstance : (IsLocalRing.maximalIdeal ℤ_[p]).IsPrime) hm.isPrimitive hd
  have hq := (hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hi
  simp only [map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one] at hq
  apply (MulEquiv.irreducible_iff (f := (taylorEquiv (1 : ℚ_[p])).toMulEquiv)).mp
  change Irreducible (taylor (1 : ℚ_[p]) (cyclotomic (p ^ (k + 1)) ℚ_[p]))
  rw [taylor_apply, C_1]
  exact hq

/-- The prime cyclotomic polynomial is irreducible over the `p`-adic numbers. -/
theorem cyclotomic_irreducible_padic : Irreducible (cyclotomic p ℚ_[p]) := by
  simpa only [Nat.zero_add, pow_one] using cyclotomic_prime_pow_irreducible_padic p 0

end Polynomial

namespace HilbertModularity.Cyclotomic

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

/-- The scalar extension of the fixed global cyclotomic field is the cyclotomic
field over the `p`-adic numbers. -/
def padicTensorEquiv :
    ℚ_[p] ⊗[ℚ] cyclotomicField p ≃ₐ[ℚ_[p]] CyclotomicField p ℚ_[p] :=
  splittingFieldTensorEquiv p ℚ_[p] (Polynomial.cyclotomic_irreducible_padic p)

/-- At its conductor, the real cyclotomic coefficient tensor is a field. -/
theorem realPadicTensor_isField : IsField (ℚ_[p] ⊗[ℚ] realCyclotomicField p) :=
  realTensor_isField p ℚ_[p] (Polynomial.cyclotomic_irreducible_padic p)

/-- Scalar extension of a prime-power cyclotomic field is a single `p`-adic cyclotomic field. -/
def padicPrimePowerTensorEquiv (k : ℕ) :
    ℚ_[p] ⊗[ℚ] cyclotomicField (p ^ (k + 1)) ≃ₐ[ℚ_[p]] CyclotomicField (p ^ (k + 1)) ℚ_[p] :=
  splittingFieldTensorEquiv (p ^ (k + 1)) ℚ_[p]
    (Polynomial.cyclotomic_prime_pow_irreducible_padic p k)

/-- The real cyclotomic coefficient tensor at a prime-power conductor is a field. -/
theorem realPrimePowerPadicTensor_isField (k : ℕ) :
    IsField (ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1))) :=
  realTensor_isField (p ^ (k + 1)) ℚ_[p] (Polynomial.cyclotomic_prime_pow_irreducible_padic p k)

end HilbertModularity.Cyclotomic
