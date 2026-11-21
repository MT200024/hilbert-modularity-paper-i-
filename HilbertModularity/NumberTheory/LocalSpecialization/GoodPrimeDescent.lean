/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalSpecialization.GoodPrimes
public import Mathlib.NumberTheory.RamificationInertia.Valuation

/-! # Exact descent of good primes

For a parameter defined over the base number field, good unit reduction at one
prime above a base prime is equivalent to good unit reduction at every prime
above it. Thus the contracted exceptional set used in the finite-field trace
comparison excludes exactly the bad base primes, including in ramified extensions.
-/

public noncomputable section

open scoped NumberField
open IsDedekindDomain

namespace HilbertModularity.LocalSpecialization

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
  [Algebra K F]

/-- Valuation exponent zero is preserved and reflected by field extension at
primes lying over one another. No unramifiedness hypothesis is needed. -/
theorem valuation_algebraMap_eq_one_iff
    (q : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 F))
    [P.asIdeal.LiesOver q.asIdeal] (x : K) :
    P.valuation F (algebraMap K F x) = 1 ↔ q.valuation K x = 1 := by
  rw [← HeightOneSpectrum.valuation_liesOver F q P]
  exact pow_eq_one_iff_left
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P.asIdeal q.ne_bot)

/-- A base-field parameter has good unit reduction upstairs precisely when it
has good unit reduction downstairs. -/
theorem goodUnit_field_algebraMap_iff
    (q : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 F))
    [P.asIdeal.LiesOver q.asIdeal] (x : K) :
    P.GoodUnit (algebraMap K F x) ↔ q.GoodUnit x := by
  constructor
  · intro h
    exact ⟨(valuation_algebraMap_eq_one_iff q P x).mp h.valuation_eq_one,
      (valuation_algebraMap_eq_one_iff q P (1 - x)).mp (by
        simpa only [map_sub, map_one] using h.complement_valuation_eq_one)⟩
  · intro h
    exact ⟨(valuation_algebraMap_eq_one_iff q P x).mpr h.valuation_eq_one, by
      simpa only [map_sub, map_one] using
        (valuation_algebraMap_eq_one_iff q P (1 - x)).mpr h.complement_valuation_eq_one⟩

/-- Contracting the bad primes for a descended parameter introduces no extra
exceptional primes. -/
theorem badPrimesBelow_algebraMap (x : K) (n : ℕ) :
    badPrimesBelow (K := K) (algebraMap K F x) n = badPrimesAbove x n := by
  ext q
  rw [mem_badPrimesBelow_iff, mem_badPrimesAbove_iff]
  constructor
  · rintro ⟨P, hP, rfl⟩
    let : P.asIdeal.LiesOver (P.under (𝓞 K)).asIdeal :=
      ⟨by rfl⟩
    change ¬ (P.under (𝓞 K)).GoodUnit x ∨ (n : 𝓞 K) ∈ (P.under (𝓞 K)).asIdeal
    rcases hP with hP | hP
    · exact Or.inl (fun h => hP ((goodUnit_field_algebraMap_iff _ P x).mpr h))
    · exact Or.inr (by simpa only [HeightOneSpectrum.under, Ideal.mem_under, map_natCast] using hP)
  · intro hq
    obtain ⟨P, hP⟩ := exists_prime_above (F := F) q
    refine ⟨P, ?_, hP⟩
    subst q
    let : P.asIdeal.LiesOver (P.under (𝓞 K)).asIdeal :=
      ⟨by rfl⟩
    change ¬ P.GoodUnit (algebraMap K F x) ∨ (n : 𝓞 F) ∈ P.asIdeal
    rcases hq with hq | hq
    · exact Or.inl (fun h => hq ((goodUnit_field_algebraMap_iff _ P x).mp h))
    · exact Or.inr (by simpa only [HeightOneSpectrum.under, Ideal.mem_under, map_natCast] using hq)

/-- The manuscript's conditions at a specified upper prime are exactly
membership outside the canonical contracted exceptional set. -/
theorem under_not_mem_badPrimesBelow_iff (x : K) (n : ℕ)
    (P : HeightOneSpectrum (𝓞 F)) :
    P.under (𝓞 K) ∉ badPrimesBelow (K := K) (algebraMap K F x) n ↔
      P.GoodUnit (algebraMap K F x) ∧ (n : 𝓞 F) ∉ P.asIdeal := by
  let : P.asIdeal.LiesOver (P.under (𝓞 K)).asIdeal := ⟨by rfl⟩
  rw [badPrimesBelow_algebraMap, not_mem_badPrimesAbove_iff,
    ← goodUnit_field_algebraMap_iff (P.under (𝓞 K)) P x]
  simp only [HeightOneSpectrum.under, Ideal.mem_under, map_natCast]

/-- Exact good-prime coverage for any exceptional set contained in the
canonical one, at a specified prime above `q`. The containment must be proved
for the selected compatible system; it is not automatic for an arbitrary set. -/
theorem not_mem_of_goodUnit_of_subset_badPrimesBelow
    (x : K) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S ⊆ badPrimesBelow (K := K) (algebraMap K F x) n)
    (q : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 F))
    [P.asIdeal.LiesOver q.asIdeal]
    (hx : P.GoodUnit (algebraMap K F x)) (hn : (n : 𝓞 F) ∉ P.asIdeal) :
    q ∉ S := by
  have hq : P.under (𝓞 K) = q := by
    apply HeightOneSpectrum.ext
    exact (show P.asIdeal.LiesOver q.asIdeal from inferInstance).over.symm
  have hnot := (under_not_mem_badPrimesBelow_iff x n P).mpr ⟨hx, hn⟩
  rw [hq] at hnot
  exact fun h => hnot (hS h)

end HilbertModularity.LocalSpecialization
