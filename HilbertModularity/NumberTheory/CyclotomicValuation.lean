/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.RealCyclotomicResidue
public import HilbertModularity.NumberTheory.CuspDepth
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FieldSimp

/-! # Valuations of cyclotomic scaling parameters

We use the canonical multiplicative adic valuation. Positive additive order
therefore means multiplicative valuation strictly less than `1`.
-/

@[expose] public section

namespace HilbertModularity.Cyclotomic

open WithZero
open scoped NumberField

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The generator of the ramified cyclotomic prime has additive order one. -/
theorem intValuation_rootInteger_sub_one :
    (primeAboveConductor p).intValuation (rootInteger p - 1) = exp (-1 : ℤ) :=
  (primeAboveConductor p).intValuation_singleton
    (root_isPrimitiveRoot p).zeta_sub_one_prime'.ne_zero rfl

/-- The cyclotomic root is a local unit at the ramified prime. -/
theorem valuation_root :
    (primeAboveConductor p).valuation (cyclotomicField p) (root p) = 1 := by
  change (primeAboveConductor p).valuation (cyclotomicField p)
    (algebraMap (𝓞 (cyclotomicField p)) (cyclotomicField p) (rootInteger p)) = 1
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  exact Ideal.notMem_of_isUnit _ ((rootInteger_isPrimitiveRoot p).isUnit (NeZero.ne p))

/-- The full cyclotomic field gives `ζ - 1` additive order one. -/
theorem valuation_root_sub_one :
    (primeAboveConductor p).valuation (cyclotomicField p) (root p - 1) = exp (-1 : ℤ) := by
  change (primeAboveConductor p).valuation (cyclotomicField p)
    (algebraMap (𝓞 (cyclotomicField p)) (cyclotomicField p) (rootInteger p - 1)) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_rootInteger_sub_one]

/-- The conductor has additive order `p - 1` in the full cyclotomic field. -/
theorem valuation_conductor :
    (primeAboveConductor p).valuation (cyclotomicField p) p = exp (-((p - 1 : ℕ) : ℤ)) := by
  obtain ⟨u, hu⟩ := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p
    (root_isPrimitiveRoot p)
  have huval : (primeAboveConductor p).intValuation (u : 𝓞 (cyclotomicField p)) = 1 :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
      (Ideal.notMem_of_isUnit _ u.isUnit)
  have h := congrArg (primeAboveConductor p).intValuation hu
  change (primeAboveConductor p).valuation (cyclotomicField p)
    (algebraMap (𝓞 (cyclotomicField p)) (cyclotomicField p) (p : 𝓞 (cyclotomicField p))) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  change (primeAboveConductor p).intValuation ((rootInteger p - 1) ^ (p - 1) * u) =
    (primeAboveConductor p).intValuation p at h
  rw [map_mul, map_pow, intValuation_rootInteger_sub_one, huval, mul_one] at h
  simpa using h.symm

/-- The real scaling parameter has additive order two in the full cyclotomic field. -/
theorem valuation_realCyclotomicParameter_root :
    (primeAboveConductor p).valuation (cyclotomicField p)
      (realCyclotomicParameter (root p)) = exp (-2 : ℤ) := by
  have hz := (root_isPrimitiveRoot p).ne_zero (NeZero.ne p)
  have h : realCyclotomicParameter (root p) = -(root p)⁻¹ * (root p - 1) ^ 2 := by
    unfold realCyclotomicParameter
    field_simp [hz]
    ring
  rw [h, map_mul, Valuation.map_neg, map_inv₀, map_pow, valuation_root, valuation_root_sub_one]
  norm_num

/-- The inclusion of the real scaling parameter in the full cyclotomic field. -/
theorem inclusion_realCyclotomicParameter :
    IntermediateField.inclusion (realCyclotomicField_le p) (2 - tau p 1) =
      realCyclotomicParameter (root p) := by
  apply Subtype.ext
  simp [realCyclotomicParameter_eq, (root_isPrimitiveRoot p).ne_zero (NeZero.ne p),
    rootTrace, tau]
  rfl

/-- The ramification formula applied to the real scaling parameter. -/
theorem valuation_real_parameter_extension :
    letI : Algebra (realCyclotomicField p) (cyclotomicField p) :=
      (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra
    (realPrimeAboveConductor p).valuation (realCyclotomicField p) (2 - tau p 1) ^
      (realPrimeAboveConductor p).asIdeal.ramificationIdx' (primeAboveConductor p).asIdeal =
        exp (-2 : ℤ) := by
  let : Algebra (realCyclotomicField p) (cyclotomicField p) :=
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra
  have : (primeAboveConductor p).asIdeal.LiesOver (realPrimeAboveConductor p).asIdeal := by
    rw [Ideal.liesOver_iff]
    exact realPrimeAboveConductor_eq_comap p
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_liesOver (cyclotomicField p)]
  change (primeAboveConductor p).valuation (cyclotomicField p)
    (IntermediateField.inclusion (realCyclotomicField_le p) (2 - tau p 1)) = _
  rw [inclusion_realCyclotomicParameter, valuation_realCyclotomicParameter_root]

/-- Normalizing the real parameter to order one gives relative ramification index two. -/
theorem ramificationIdx_real_prime
    (hnorm : (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      (2 - tau p 1) = exp (-1 : ℤ)) :
    letI : Algebra (realCyclotomicField p) (cyclotomicField p) :=
      (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra
    (realPrimeAboveConductor p).asIdeal.ramificationIdx' (primeAboveConductor p).asIdeal = 2 := by
  let : Algebra (realCyclotomicField p) (cyclotomicField p) :=
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra
  have h := valuation_real_parameter_extension p
  rw [hnorm] at h
  have hl := congrArg WithZero.log h
  simp only [WithZero.log_pow, WithZero.log_exp, Int.nsmul_eq_mul] at hl
  omega

/-- The real conductor has additive order `(p - 1) / 2`. -/
theorem log_valuation_real_conductor (hp : p ≠ 2)
    (hnorm : (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      (2 - tau p 1) = exp (-1 : ℤ)) :
    WithZero.log ((realPrimeAboveConductor p).valuation (realCyclotomicField p) p) =
      -(((p - 1) / 2 : ℕ) : ℤ) := by
  let : Algebra (realCyclotomicField p) (cyclotomicField p) :=
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra
  have : (primeAboveConductor p).asIdeal.LiesOver (realPrimeAboveConductor p).asIdeal := by
    rw [Ideal.liesOver_iff]
    exact realPrimeAboveConductor_eq_comap p
  have h := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver (cyclotomicField p)
    (realPrimeAboveConductor p) (primeAboveConductor p) (p : realCyclotomicField p)
  rw [ramificationIdx_real_prime p hnorm,
    map_natCast (algebraMap (realCyclotomicField p) (cyclotomicField p)), valuation_conductor] at h
  have hl := congrArg WithZero.log h
  simp only [WithZero.log_pow, WithZero.log_exp, Int.nsmul_eq_mul] at hl
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨k, hk⟩ := hodd
  omega

/-- Integers prime to the conductor are units for the real adic valuation. -/
theorem valuation_real_natCast_of_not_dvd {n : ℕ} (hn : ¬p ∣ n) :
    (realPrimeAboveConductor p).valuation (realCyclotomicField p) n = 1 := by
  change (realPrimeAboveConductor p).valuation (realCyclotomicField p)
    (algebraMap (𝓞 (realCyclotomicField p)) (realCyclotomicField p) n) = 1
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  change (n : 𝓞 (realCyclotomicField p)) ∉ RingHom.ker (realCyclotomicReduction p)
  simpa only [RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] using hn

/-- The real adic valuation of a nonzero natural number is determined by its `p`-part. -/
theorem valuation_real_natCast {n : ℕ} (hn : n ≠ 0) :
    (realPrimeAboveConductor p).valuation (realCyclotomicField p) n =
      (realPrimeAboveConductor p).valuation (realCyclotomicField p) p ^ padicValNat p n := by
  have hf := Nat.divMaxPow_mul_pow_padicValNat p n
  have he : (n : realCyclotomicField p) =
      (n.divMaxPow p : realCyclotomicField p) * (p : realCyclotomicField p) ^ padicValNat p n := by
    exact_mod_cast hf.symm
  rw [he, map_mul, map_pow,
    valuation_real_natCast_of_not_dvd p (Nat.not_dvd_divMaxPow (Fact.out : p.Prime).one_lt hn),
    one_mul]

/-- Logarithmic form of the real valuation of a natural number. -/
theorem log_valuation_real_natCast {n : ℕ} (hn : n ≠ 0) :
    WithZero.log ((realPrimeAboveConductor p).valuation (realCyclotomicField p) n) =
      (padicValNat p n : ℤ) *
        WithZero.log ((realPrimeAboveConductor p).valuation (realCyclotomicField p) p) := by
  rw [valuation_real_natCast p hn, WithZero.log_pow, Int.nsmul_eq_mul]

/-- Logarithmic form of the real valuation of a nonzero integer. -/
theorem log_valuation_real_intCast {n : ℤ} (hn : n ≠ 0) :
    WithZero.log ((realPrimeAboveConductor p).valuation (realCyclotomicField p) n) =
      (padicValInt p n : ℤ) *
        WithZero.log ((realPrimeAboveConductor p).valuation (realCyclotomicField p) p) := by
  cases n with
  | ofNat n =>
      simpa only [Int.ofNat_eq_natCast, Int.cast_natCast, padicValInt.of_nat] using
        log_valuation_real_natCast p (show n ≠ 0 by intro h; subst n; exact hn rfl)
  | negSucc n =>
      simpa only [Int.cast_negSucc, Valuation.map_neg, padicValInt, Int.natAbs_negSucc] using
        log_valuation_real_natCast p (Nat.succ_ne_zero n)

/-- The real adic valuation restricts to a multiple of the usual rational `p`-adic valuation. -/
theorem log_valuation_real_ratCast {t : ℚ} (ht : t ≠ 0) :
    WithZero.log ((realPrimeAboveConductor p).valuation (realCyclotomicField p) t) =
      padicValRat p t *
        WithZero.log ((realPrimeAboveConductor p).valuation (realCyclotomicField p) p) := by
  have hn : t.num ≠ 0 := Rat.num_ne_zero.mpr ht
  have hn' : (t.num : realCyclotomicField p) ≠ 0 := by exact_mod_cast hn
  have hd' : (t.den : realCyclotomicField p) ≠ 0 := by exact_mod_cast t.den_ne_zero
  rw [Rat.cast_def, map_div₀, WithZero.log_div
    ((Valuation.ne_zero_iff _).mpr hn') ((Valuation.ne_zero_iff _).mpr hd'),
    log_valuation_real_intCast p hn, log_valuation_real_natCast p t.den_ne_zero,
    padicValRat_def, sub_mul]

/-- The exact logarithmic valuation of the scaled rational cusp parameter. -/
theorem log_valuation_scaled_parameter (hp : p ≠ 2)
    (hnorm : (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      (2 - tau p 1) = exp (-1 : ℤ)) {t : ℚ} (ht : t ≠ 0) :
    WithZero.log ((realPrimeAboveConductor p).valuation (realCyclotomicField p)
      ((t : realCyclotomicField p) / (2 - tau p 1) ^ p)) =
      (p : ℤ) - (((p - 1) / 2 : ℕ) : ℤ) * padicValRat p t := by
  have ht' : (t : realCyclotomicField p) ≠ 0 := by exact_mod_cast ht
  rw [map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).mpr ht')
      (by rw [map_pow, hnorm]; exact pow_ne_zero _ (by simp)),
    log_valuation_real_ratCast p ht, log_valuation_real_conductor p hp hnorm,
    map_pow, WithZero.log_pow, hnorm, WithZero.log_exp, Int.nsmul_eq_mul]
  ring

/-- [TripathiGoswami], Appendix A: positive local order of `t / ϖ^p` is equivalent
    to rational `p`-adic depth at least three. The nonnegative-depth hypothesis is unnecessary. -/
theorem valuation_scaled_parameter_lt_one_iff (hp : 5 ≤ p)
    (hnorm : (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      (2 - tau p 1) = exp (-1 : ℤ)) {t : ℚ} (ht : t ≠ 0) :
    (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      ((t : realCyclotomicField p) / (2 - tau p 1) ^ p) < 1 ↔
        3 ≤ padicValRat p t := by
  have ht' : (t : realCyclotomicField p) ≠ 0 := by exact_mod_cast ht
  have hϖ : (2 - tau p 1 : realCyclotomicField p) ≠ 0 := by
    apply (Valuation.ne_zero_iff ((realPrimeAboveConductor p).valuation
      (realCyclotomicField p))).mp
    rw [hnorm]
    simp
  rw [← WithZero.log_lt_log ((Valuation.ne_zero_iff _).mpr
    (div_ne_zero ht' (pow_ne_zero p hϖ))) one_ne_zero,
    log_valuation_scaled_parameter p (by omega) hnorm ht, WithZero.log_one]
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h := HilbertModularity.Cusp.scaled_depth_pos_iff hp hodd (padicValRat p t)
  omega

end

end HilbertModularity.Cyclotomic
