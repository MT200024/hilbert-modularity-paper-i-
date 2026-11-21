/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Cyclotomic
public import HilbertModularity.NumberTheory.Inertia
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # Unramified primes of the cyclotomic coefficient fields

The prime-power cyclotomic discriminant is supported at its conductor prime.
Consequently the actual coefficient field is unramified at every other rational
prime. This supplies the arithmetic extension step in the good-unit descent
argument of [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped NumberField

namespace HilbertModularity.Cyclotomic

variable (p k q : ℕ) [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p)

include hq hqp

/-- No other rational prime divides the discriminant of the constructed prime-power field. -/
theorem not_dvd_discr_cyclotomic_primePower :
    ¬ (q : ℤ) ∣ NumberField.discr (cyclotomicField (p ^ (k + 1))) := by
  rw [IsCyclotomicExtension.Rat.discr_prime_pow_succ p k]
  have hq' : Prime (q : ℤ) := (Int.prime_iff_natAbs_prime (k := (q : ℤ))).mpr hq
  intro h
  rcases hq'.dvd_mul.mp h with h | h
  · have hunit : IsUnit ((-1 : ℤ) ^ (p ^ k * (p - 1) / 2)) := (isUnit_neg_one : IsUnit (-1 : ℤ)).pow _
    exact hq'.not_isUnit (isUnit_of_dvd_unit h hunit)
  · have hqp' : (q : ℤ) ∣ (p : ℤ) := hq'.dvd_of_dvd_pow h
    have hnat : q ∣ p := by exact_mod_cast hqp'
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp hnat)

/-- Every rational prime distinct from the conductor is unramified in the actual cyclotomic field. -/
theorem isUnramifiedIn_cyclotomic_primePower :
    Algebra.IsUnramifiedIn (𝓞 (cyclotomicField (p ^ (k + 1)))) (Ideal.span {(q : ℤ)}) :=
  (NumberField.not_dvd_discr_iff_isUnramifiedIn
    (cyclotomicField (p ^ (k + 1))) (𝓞 (cyclotomicField (p ^ (k + 1))))
    ((Int.prime_iff_natAbs_prime (k := (q : ℤ))).mpr hq)).mp (not_dvd_discr_cyclotomic_primePower p k q hq hqp)

/-- At every prime above a rational prime away from the conductor, the cyclotomic extension
is unramified over the real cyclotomic subfield as well. -/
theorem isUnramifiedAt_realCyclotomic_primePower
    (P : Ideal (𝓞 (cyclotomicField (p ^ (k + 1))))) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
      (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
    Algebra.IsUnramifiedAt (𝓞 (realCyclotomicField (p ^ (k + 1)))) P := by
  let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
    (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
  let : Algebra.IsUnramifiedAt ℤ P :=
    isUnramifiedIn_cyclotomic_primePower p k q hq hqp P inferInstance inferInstance
  exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ P

/-- The ramification index over the real subfield is one away from the conductor prime. -/
theorem ramificationIdx_realCyclotomic_primePower
    (P : Ideal (𝓞 (cyclotomicField (p ^ (k + 1))))) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
      (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
    Ideal.ramificationIdx P (𝓞 (realCyclotomicField (p ^ (k + 1)))) = 1 := by
  let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
    (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
  let : Algebra.IsUnramifiedAt (𝓞 (realCyclotomicField (p ^ (k + 1)))) P :=
    isUnramifiedAt_realCyclotomic_primePower p k q hq hqp P
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

/-- The actual finite cyclotomic Galois group has trivial inertia away from the conductor. -/
theorem inertia_cyclotomic_primePower_eq_bot
    (P : Ideal (𝓞 (cyclotomicField (p ^ (k + 1))))) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    Ideal.inertia
      (cyclotomicField (p ^ (k + 1)) ≃ₐ[ℚ] cyclotomicField (p ^ (k + 1))) P = ⊥ := by
  let : IsGalois ℚ (cyclotomicField (p ^ (k + 1))) :=
    IsCyclotomicExtension.isGalois {p ^ (k + 1)} ℚ _
  let : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime ((Nat.cast_ne_zero.mpr hq.ne_zero) : (q : ℤ) ≠ 0)).mpr
      ((Int.prime_iff_natAbs_prime (k := (q : ℤ))).mpr hq)
  let : Algebra.IsUnramifiedAt ℤ P :=
    isUnramifiedIn_cyclotomic_primePower p k q hq hqp P inferInstance inferInstance
  exact Ideal.inertia_eq_bot_of_isUnramifiedAt (Ideal.span {(q : ℤ)}) P

/-- The actual cyclotomic extension over its real subfield also has trivial finite inertia
at every prime away from the conductor. -/
theorem inertia_realCyclotomic_primePower_eq_bot
    (P : Ideal (𝓞 (cyclotomicField (p ^ (k + 1))))) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
      (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
    Ideal.inertia (cyclotomicField (p ^ (k + 1)) ≃ₐ[realCyclotomicField (p ^ (k + 1))]
      cyclotomicField (p ^ (k + 1))) P = ⊥ := by
  let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
    (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
  apply le_antisymm _ bot_le
  intro g hg
  have h : g.restrictScalars ℚ ∈ Ideal.inertia
      (cyclotomicField (p ^ (k + 1)) ≃ₐ[ℚ] cyclotomicField (p ^ (k + 1))) P := by
    rw [Ideal.mem_inertia] at hg ⊢
    exact hg
  rw [inertia_cyclotomic_primePower_eq_bot p k q hq hqp P, Subgroup.mem_bot] at h
  apply Subgroup.mem_bot.mpr
  apply AlgEquiv.restrictScalars_injective ℚ
  exact h

end HilbertModularity.Cyclotomic
