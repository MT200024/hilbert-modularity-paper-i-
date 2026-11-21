/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalSpecialization
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-! # Finitely many nonunit coefficient primes

A nonzero algebraic value is a unit at all but finitely many coefficient
primes. Removing these primes preserves infinitely many residual
characteristics. This is the finite-exclusion step in
[TripathiGoswami, determinant rigidity]. The finiteness of denominator
support is the existing Dedekind-domain theorem in mathlib.
-/

@[expose] public noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero fraction is a local valuation unit outside finitely many primes. -/
theorem finite_nonunit_primes (y : K) (hy : y ≠ 0) :
    {P : HeightOneSpectrum R | P.valuation K y ≠ 1}.Finite := by
  apply ((Support.finite R y).union (Support.finite R y⁻¹)).subset
  intro P hP
  by_contra h
  have hyint : P.valuation K y ≤ 1 := not_lt.mp (fun ht => h (Or.inl ht))
  have hyinv : P.valuation K y⁻¹ ≤ 1 := not_lt.mp (fun ht => h (Or.inr ht))
  have hu : IsUnit (P.localElement y hyint) := by
    refine ⟨⟨P.localElement y hyint, P.localElement y⁻¹ hyinv, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mul_inv_cancel₀ hy)
    · exact Subtype.ext (inv_mul_cancel₀ hy)
  exact hP ((P.localIntegers.isUnit_iff_valuation_eq_one).mp hu)

/-- Infinitely many residue characteristics remain after requiring a nonzero
algebraic value to be a local unit. -/
theorem infinite_residue_characteristics_of_unit
    {J : Type*} (P : J → HeightOneSpectrum R) (S : Set J)
    (hS : ((fun j => ringChar (R ⧸ (P j).asIdeal)) '' S).Infinite)
    (y : K) (hy : y ≠ 0) :
    ((fun j => ringChar (R ⧸ (P j).asIdeal)) '' {j ∈ S | (P j).valuation K y = 1}).Infinite := by
  intro hf
  apply hS.not_finite
  apply (hf.union ((finite_nonunit_primes (R := R) y hy).image
    (fun Q => ringChar (R ⧸ Q.asIdeal)))).subset
  rintro ell ⟨j, hj, rfl⟩
  by_cases hu : (P j).valuation K y = 1
  · exact Or.inl ⟨j, ⟨hj, hu⟩, rfl⟩
  · exact Or.inr ⟨P j, hu, rfl⟩

end IsDedekindDomain.HeightOneSpectrum
