/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalSpecialization.FiniteSupport
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! # Finite exceptional sets for good unit specializations

For a parameter in a finite extension of number fields, the primes where the
parameter or its complement is not a unit are finite. We also remove the primes
containing a fixed nonzero integer. Contracting this finite set gives a single
finite set downstairs that works for every prime above a prime outside it.
-/

public noncomputable section

open scoped NumberField
open IsDedekindDomain

namespace HilbertModularity.LocalSpecialization

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
  [Algebra K F]

/-- The upstairs primes where a parameter does not specialize away from `0,1`,
or which contain the fixed integer `n`. -/
def badPrimesAbove (x : F) (n : ℕ) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  {P | ¬ P.GoodUnit x ∨ (n : 𝓞 F) ∈ P.asIdeal}

/-- The two reasons for excluding an upstairs prime. -/
theorem mem_badPrimesAbove_iff (x : F) (n : ℕ)
    (P : HeightOneSpectrum (𝓞 F)) :
    P ∈ badPrimesAbove x n ↔ ¬ P.GoodUnit x ∨ (n : 𝓞 F) ∈ P.asIdeal := Iff.rfl

theorem not_mem_badPrimesAbove_iff (x : F) (n : ℕ)
    (P : HeightOneSpectrum (𝓞 F)) :
    P ∉ badPrimesAbove x n ↔
      P.GoodUnit x ∧ (n : 𝓞 F) ∉ P.asIdeal := by
  simp only [badPrimesAbove, Set.mem_ofPred_eq, not_or, not_not]

/-- A nonzero parameter distinct from one has only finitely many bad upstairs primes. -/
theorem badPrimesAbove_finite (x : F) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (n : ℕ) (hn : n ≠ 0) : (badPrimesAbove x n).Finite := by
  have hcomp : (1 - x : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hfinite := (((HeightOneSpectrum.finite_nonunit_primes (R := 𝓞 F) x hx0).union
      (HeightOneSpectrum.finite_nonunit_primes (R := 𝓞 F) (1 - x) hcomp)).union
      (HeightOneSpectrum.finite_nonunit_primes (R := 𝓞 F) (n : F) hnF))
  apply hfinite.subset
  intro P hP
  rcases hP with hgood | hmem
  · by_cases hx : P.valuation F x = 1
    · exact Or.inl (Or.inr (by
        intro hc
        exact hgood ⟨hx, hc⟩))
    · exact Or.inl (Or.inl hx)
  · refine Or.inr ?_
    intro hnval
    have hnnot : (n : 𝓞 F) ∉ P.asIdeal :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) P).mp (by
        simpa only [map_natCast] using hnval)
    exact hnnot hmem

/-- The finite downstairs set obtained by contracting the bad upstairs primes. -/
def badPrimesBelow (x : F) (n : ℕ) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  (fun P : HeightOneSpectrum (𝓞 F) => P.under (𝓞 K)) '' badPrimesAbove x n

omit [NumberField K] in
/-- Membership in the contracted exceptional set has an upstairs witness. -/
theorem mem_badPrimesBelow_iff (x : F) (n : ℕ)
    (q : HeightOneSpectrum (𝓞 K)) :
    q ∈ badPrimesBelow (K := K) x n ↔
      ∃ P : HeightOneSpectrum (𝓞 F),
        (¬ P.GoodUnit x ∨ (n : 𝓞 F) ∈ P.asIdeal) ∧ P.under (𝓞 K) = q := Iff.rfl

omit [NumberField K] in
theorem badPrimesBelow_finite (x : F) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (n : ℕ) (hn : n ≠ 0) : (badPrimesBelow (K := K) x n).Finite :=
  (badPrimesAbove_finite x hx0 hx1 n hn).image _

omit [NumberField K] in
/-- Every prime above a prime outside the contracted exceptional set is good. -/
theorem goodUnit_and_integer_away_of_under_not_bad (x : F) (n : ℕ)
    (P : HeightOneSpectrum (𝓞 F))
    (hP : P.under (𝓞 K) ∉ badPrimesBelow (K := K) x n) :
    P.GoodUnit x ∧ (n : 𝓞 F) ∉ P.asIdeal := by
  have hnot : P ∉ badPrimesAbove x n := by
    intro hbad
    exact hP ⟨P, hbad, rfl⟩
  simpa only [badPrimesAbove, Set.mem_ofPred_eq, not_or, not_not] using hnot

/-- Regard a maximal ideal of the upper integer ring lying over a nonzero
base prime as a height-one prime. -/
def heightOnePrimeOfLiesOver (q : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    HeightOneSpectrum (𝓞 F) where
  asIdeal := Q
  isPrime := (inferInstance : Q.IsMaximal).isPrime
  ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot q.ne_bot Q

omit [NumberField K] [NumberField F] in
@[simp] theorem heightOnePrimeOfLiesOver_asIdeal (q : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    (heightOnePrimeOfLiesOver q Q).asIdeal = Q := (rfl)

omit [NumberField K] [NumberField F] in
/-- The prime constructed from a lying-over ideal contracts to its specified base prime. -/
theorem heightOnePrimeOfLiesOver_under (q : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    (heightOnePrimeOfLiesOver q Q).under (𝓞 K) = q := by
  apply HeightOneSpectrum.ext
  change Ideal.under (𝓞 K) Q = q.asIdeal
  exact (show Q.LiesOver q.asIdeal from inferInstance).over.symm

omit [NumberField K] in
/-- A maximal ideal above a base prime outside the bad set has a good
parameter specialization and avoids the chosen integer. -/
theorem goodUnit_and_integer_away_of_liesOver_not_bad (x : F) (n : ℕ)
    (q : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (hq : q ∉ badPrimesBelow (K := K) x n) :
    (heightOnePrimeOfLiesOver q Q).GoodUnit x ∧ (n : 𝓞 F) ∉ Q := by
  have hq' : (heightOnePrimeOfLiesOver q Q).under (𝓞 K) ∉
      badPrimesBelow (K := K) x n := by
    rw [heightOnePrimeOfLiesOver_under]
    exact hq
  simpa only [heightOnePrimeOfLiesOver_asIdeal] using
    goodUnit_and_integer_away_of_under_not_bad (K := K) x n
      (heightOnePrimeOfLiesOver q Q) hq'

omit [NumberField F] in
/-- A height-one prime of the base has a height-one prime above it in the
integer ring of a finite extension. -/
theorem exists_prime_above (q : HeightOneSpectrum (𝓞 K)) :
    ∃ P : HeightOneSpectrum (𝓞 F), P.under (𝓞 K) = q := by
  obtain ⟨Q, hQ, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 F) q.asIdeal
  let _ : Q.IsMaximal := hQ
  let _ : Q.LiesOver q.asIdeal := hOver
  exact ⟨heightOnePrimeOfLiesOver q Q, heightOnePrimeOfLiesOver_under q Q⟩

/-- The good-prime conclusion can be applied to a chosen prime above any
downstairs prime outside the finite exceptional set. -/
theorem exists_good_prime_above (x : F) (n : ℕ)
    (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∉ badPrimesBelow (K := K) x n) :
    ∃ P : HeightOneSpectrum (𝓞 F), P.under (𝓞 K) = q ∧
      P.GoodUnit x ∧ (n : 𝓞 F) ∉ P.asIdeal := by
  obtain ⟨P, hP⟩ := exists_prime_above (F := F) q
  exact ⟨P, hP, goodUnit_and_integer_away_of_under_not_bad x n P (hP ▸ hq)⟩

omit [NumberField F] in
/-- Avoiding a product of natural numbers avoids each factor. -/
theorem factors_away_of_product_away (P : HeightOneSpectrum (𝓞 F))
    (N ell : ℕ) (h : ((N * ell : ℕ) : 𝓞 F) ∉ P.asIdeal) :
    (N : 𝓞 F) ∉ P.asIdeal ∧ (ell : 𝓞 F) ∉ P.asIdeal := by
  constructor
  · intro hN
    exact h (by simpa only [Nat.cast_mul] using P.asIdeal.mul_mem_right (ell : 𝓞 F) hN)
  · intro hell
    exact h (by simpa only [Nat.cast_mul] using P.asIdeal.mul_mem_left (N : 𝓞 F) hell)

omit [NumberField K] in
/-- Outside the contracted exceptional set for `N * ell`, every upper prime
has good parameter reduction and residue characteristic dividing neither
factor. -/
theorem goodUnit_and_factors_away_of_under_not_bad (x : F) (N ell : ℕ)
    (P : HeightOneSpectrum (𝓞 F))
    (hP : P.under (𝓞 K) ∉ badPrimesBelow (K := K) x (N * ell)) :
    P.GoodUnit x ∧ (N : 𝓞 F) ∉ P.asIdeal ∧ (ell : 𝓞 F) ∉ P.asIdeal := by
  obtain ⟨hgood, hproduct⟩ :=
    goodUnit_and_integer_away_of_under_not_bad (K := K) x (N * ell) P hP
  exact ⟨hgood, factors_away_of_product_away P N ell hproduct⟩

omit [NumberField K] in
/-- The same product-prime conclusion for a specified maximal ideal lying
over the base prime. -/
theorem goodUnit_and_factors_away_of_liesOver_not_bad (x : F) (N ell : ℕ)
    (q : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (hq : q ∉ badPrimesBelow (K := K) x (N * ell)) :
    (heightOnePrimeOfLiesOver q Q).GoodUnit x ∧
      (N : 𝓞 F) ∉ Q ∧ (ell : 𝓞 F) ∉ Q := by
  have hq' : (heightOnePrimeOfLiesOver q Q).under (𝓞 K) ∉
      badPrimesBelow (K := K) x (N * ell) := by
    rw [heightOnePrimeOfLiesOver_under]
    exact hq
  simpa only [heightOnePrimeOfLiesOver_asIdeal] using
    goodUnit_and_factors_away_of_under_not_bad (K := K) x N ell
      (heightOnePrimeOfLiesOver q Q) hq'

end HilbertModularity.LocalSpecialization
