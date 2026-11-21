/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicResidue
public import HilbertModularity.NumberTheory.CyclotomicUnits
public import HilbertModularity.NumberTheory.LocalSpecialization

/-! # Cyclotomic units in the real subfield

The quotients of trace differences belong to the real cyclotomic field. Their
geometric-sum expressions show that they are algebraic integers; when the index
is prime to the conductor, they are units already in its ring of integers.

## References

The scaled roots used in [TripathiGoswami], Lemma 4.6.
-/

@[expose] public section

namespace HilbertModularity.Cyclotomic

open Finset
open scoped NumberField

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The scaling parameter of a prime cyclotomic field is nonzero. -/
theorem realCyclotomicParameter_zeta_ne_zero : realCyclotomicParameter (zeta p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  exact mul_ne_zero (sub_ne_zero.mpr ((zeta_isPrimitiveRoot p).ne_one hp.one_lt).symm)
    (sub_ne_zero.mpr ((zeta_isPrimitiveRoot p).inv.ne_one hp.one_lt).symm)

/-- The scaled root, regarded as an element of the real cyclotomic field. -/
def realScaledRoot (j : ℕ) : realCyclotomicField p :=
  (2 - tau p j) / (2 - tau p 1)

/-- The real quotient agrees with the product of the two geometric sums. -/
theorem coe_realScaledRoot (j : ℕ) :
    (realScaledRoot p j : Qbar) = cyclotomicUnitRatio (zeta p) j := by
  rw [cyclotomicUnitRatio_eq_div _ ((zeta_isPrimitiveRoot p).ne_zero (NeZero.ne p))
    (realCyclotomicParameter_zeta_ne_zero p)]
  simp [realScaledRoot, realCyclotomicParameter_eq _
    ((zeta_isPrimitiveRoot p).ne_zero (NeZero.ne p)), rootTrace, tau]
  rfl

/-- The scaled roots are algebraic integers in the real subfield. -/
theorem realScaledRoot_isIntegral (j : ℕ) : IsIntegral ℤ (realScaledRoot p j) := by
  apply (isIntegral_algHom_iff ((realCyclotomicField p).val.restrictScalars ℤ)
    (realCyclotomicField p).val.injective).mp
  change IsIntegral ℤ (realScaledRoot p j : Qbar)
  rw [coe_realScaledRoot]
  exact (IsIntegral.sum _ fun i _ =>
    ((zeta_isPrimitiveRoot p).isIntegral (NeZero.pos p)).pow i).mul
      (IsIntegral.sum _ fun i _ =>
        ((zeta_isPrimitiveRoot p).inv.isIntegral (NeZero.pos p)).pow i)

/-- The integral lift of a scaled root in the real cyclotomic field. -/
def realScaledRootInteger (j : ℕ) : 𝓞 (realCyclotomicField p) :=
  ⟨realScaledRoot p j, realScaledRoot_isIntegral p j⟩

@[simp] theorem coe_realScaledRootInteger (j : ℕ) :
    (realScaledRootInteger p j : realCyclotomicField p) = realScaledRoot p j := rfl

/-- The integer inclusion identifies a real scaled root with the two geometric sums. -/
theorem map_realScaledRootInteger (j : ℕ) :
    NumberField.RingOfIntegers.mapRingHom
        (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom
        (realScaledRootInteger p j) =
      (∑ i ∈ range j, rootInteger p ^ i) *
        (∑ i ∈ range j, (rootInteger p ^ (p - 1)) ^ i) := by
  have hp := (Fact.out : p.Prime)
  have hζ := zeta_isPrimitiveRoot p
  have hinv : (zeta p) ^ (p - 1) = (zeta p)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hζ.pow_eq_one]
  apply NumberField.RingOfIntegers.ext
  apply (cyclotomicField p).val.injective
  change (realScaledRoot p j : Qbar) = _
  rw [coe_realScaledRoot]
  simp [cyclotomicUnitRatio, rootInteger, root, map_pow]
  change (∑ i ∈ range j, zeta p ^ i) * (∑ i ∈ range j, (zeta p ^ i)⁻¹) =
    (∑ i ∈ range j, zeta p ^ i) * (∑ i ∈ range j, (zeta p ^ (p - 1)) ^ i)
  simp only [hinv, inv_pow]

/-- A scaled root with index prime to the conductor is a unit of the real
ring of integers, before any localization. -/
theorem realScaledRootInteger_isUnit {j : ℕ} (hj : j.Coprime p) :
    IsUnit (realScaledRootInteger p j) := by
  let : Algebra (realCyclotomicField p) (cyclotomicField p) :=
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra
  apply IsUnit.of_map (algebraMap (𝓞 (realCyclotomicField p)) (𝓞 (cyclotomicField p)))
  change IsUnit (NumberField.RingOfIntegers.mapRingHom
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom (realScaledRootInteger p j))
  rw [map_realScaledRootInteger]
  exact (cyclotomicUnitRatio_isUnit_and_mod (Fact.out : p.Prime)
    (rootInteger_isPrimitiveRoot p) hj).1

/-- The scaled root in the local ring at a finite prime of the real field. -/
def localScaledRoot
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p))) (j : ℕ) :
    P.valuationSubringAtPrime (realCyclotomicField p) :=
  algebraMap _ _ (realScaledRootInteger p j)

/-- Its image in the fraction field is the prescribed quotient of trace differences. -/
@[simp] theorem coe_localScaledRoot
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p))) (j : ℕ) :
    (localScaledRoot p P j : realCyclotomicField p) = (2 - tau p j) / (2 - tau p 1) := rfl

/-- Scaled cyclotomic units remain units at every finite prime of the real field. -/
theorem localScaledRoot_isUnit
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    {j : ℕ} (hj : j.Coprime p) : IsUnit (localScaledRoot p P j) :=
  (realScaledRootInteger_isUnit p hj).map (algebraMap _ _)

/-- All the scaled roots in the half interval are units of the local ring.
This applies in particular to the unique prime above `p`. -/
theorem localScaledRoot_isUnit_of_mem_Icc
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    {j : ℕ} (hj : j ∈ Icc 1 ((p - 1) / 2)) : IsUnit (localScaledRoot p P j) := by
  apply localScaledRoot_isUnit
  apply Nat.Coprime.symm
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro h
  have := Nat.le_of_dvd (by have := mem_Icc.mp hj; omega) h
  have := mem_Icc.mp hj
  omega

end

end HilbertModularity.Cyclotomic
