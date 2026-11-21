/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicPrime
public import HilbertModularity.NumberTheory.RealCyclotomicUnits

/-! # Residues of the real scaled cyclotomic roots

Reduction at the cyclotomic prime restricts to the real integer ring. Its kernel
defines the real prime above the conductor, and its residue field is `ZMod p`.
The scaled roots reduce to the squares of their indices, as in
[TripathiGoswami], Lemma 4.6.
-/

@[expose] public section

namespace HilbertModularity.Cyclotomic

open Finset
open scoped NumberField

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- Reduction on the real ring of integers, through its cyclotomic inclusion. -/
def realCyclotomicReduction : 𝓞 (realCyclotomicField p) →+* ZMod p :=
  (cyclotomicReduction p).comp (NumberField.RingOfIntegers.mapRingHom
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom)

/-- The real reduction is surjective because every residue is an integer. -/
theorem realCyclotomicReduction_surjective : Function.Surjective (realCyclotomicReduction p) := by
  intro x
  exact ⟨(x.val : 𝓞 (realCyclotomicField p)), by simp⟩

/-- The prime of the real cyclotomic field obtained by restricting the ramified prime. -/
def realPrimeAboveConductor :
    IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)) where
  asIdeal := RingHom.ker (realCyclotomicReduction p)
  isPrime := RingHom.ker_isPrime _
  ne_bot := by
    intro h
    have hm : (p : 𝓞 (realCyclotomicField p)) ∈ RingHom.ker (realCyclotomicReduction p) := by
      simp
    rw [h, Ideal.mem_bot] at hm
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hm

/-- The real prime is the contraction of the cyclotomic prime. -/
theorem realPrimeAboveConductor_eq_comap :
    (realPrimeAboveConductor p).asIdeal = (primeAboveConductor p).asIdeal.comap
      (NumberField.RingOfIntegers.mapRingHom
        (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom) := by
  ext x
  exact cyclotomicReduction_eq_zero_iff p _

/-- The chosen real prime lies above the rational prime conductor. -/
instance realPrimeAboveConductor_liesOver :
    (realPrimeAboveConductor p).asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  rw [Ideal.liesOver_iff]
  refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p)
    Ideal.IsPrime.ne_top' ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
  change (p : 𝓞 (realCyclotomicField p)) ∈ RingHom.ker (realCyclotomicReduction p)
  simp

/-- The real prime above the conductor is unique. -/
theorem eq_realPrimeAboveConductor_of_liesOver
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    [P.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] : P = realPrimeAboveConductor p := by
  let : Algebra (realCyclotomicField p) (cyclotomicField p) :=
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (cyclotomicField p)) P.asIdeal
  have : Q.IsMaximal := hQ
  have : Q.LiesOver P.asIdeal := hQP
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P.asIdeal _
  have he : Q = (primeAboveConductor p).asIdeal :=
    IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p
      (cyclotomicField p) (root_isPrimitiveRoot p) Q
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [Q.over_def P.asIdeal, he]
  exact (realPrimeAboveConductor_eq_comap p).symm

/-- The canonical residue-field identification at the real prime. -/
def realCyclotomicResidueEquiv :
    (𝓞 (realCyclotomicField p) ⧸ (realPrimeAboveConductor p).asIdeal) ≃+* ZMod p :=
  (realCyclotomicReduction p).quotientKerEquivOfSurjective
    (realCyclotomicReduction_surjective p)

/-- The integral scaled root reduces to the square of its index. -/
theorem realCyclotomicReduction_realScaledRootInteger (j : ℕ) :
    realCyclotomicReduction p (realScaledRootInteger p j) = (j : ZMod p) ^ 2 := by
  change cyclotomicReduction p (NumberField.RingOfIntegers.mapRingHom
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom
      (realScaledRootInteger p j)) = _
  rw [map_realScaledRootInteger]
  simp [pow_two]

/-- Reduction from the actual local ring, with residue field identified with `ZMod p`. -/
def realLocalReduction :
    (realPrimeAboveConductor p).valuationSubringAtPrime (realCyclotomicField p) →+* ZMod p :=
  (realCyclotomicResidueEquiv p).toRingHom.comp (realPrimeAboveConductor p).localResidue

/-- Reduction of a local integer agrees with reduction before localization. -/
@[simp] theorem realLocalReduction_algebraMap (x : 𝓞 (realCyclotomicField p)) :
    realLocalReduction p (algebraMap _ _ x) = realCyclotomicReduction p x := by
  change realCyclotomicResidueEquiv p
    ((realPrimeAboveConductor p).specialization (algebraMap _ (realCyclotomicField p) x)
      ((realPrimeAboveConductor p).valuation_le_one x)) = _
  rw [IsDedekindDomain.HeightOneSpectrum.specialization_algebraMap]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ _

/-- The local scaled root has residue `j²` in the prime field. -/
theorem realLocalReduction_localScaledRoot (j : ℕ) :
    realLocalReduction p (localScaledRoot p (realPrimeAboveConductor p) j) =
      (j : ZMod p) ^ 2 := by
  rw [localScaledRoot, realLocalReduction_algebraMap,
    realCyclotomicReduction_realScaledRootInteger]

/-- Including the index `0`, whose residue is `0`, the scaled-root residues
are pairwise distinct on the half interval. -/
theorem realLocalReduction_localScaledRoot_injOn :
    Set.InjOn (fun j : ℕ =>
      realLocalReduction p (localScaledRoot p (realPrimeAboveConductor p) j))
      (Set.Icc 0 ((p - 1) / 2)) := by
  intro i hi j hj h
  simp only [realLocalReduction_localScaledRoot] at h
  rcases eq_or_ne i 0 with rfl | hi0
  · rcases eq_or_ne j 0 with rfl | hj0
    · rfl
    · exact False.elim (sq_ne_zero (Nat.one_le_iff_ne_zero.mpr hj0) hj.2
        (by simpa using h.symm))
  · rcases eq_or_ne j 0 with rfl | hj0
    · exact False.elim (sq_ne_zero (Nat.one_le_iff_ne_zero.mpr hi0) hi.2
        (by simpa using h))
    · exact sq_injOn (Nat.one_le_iff_ne_zero.mpr hi0) hi.2
        (Nat.one_le_iff_ne_zero.mpr hj0) hj.2 h

end

end HilbertModularity.Cyclotomic
