/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalSpecialization.GoodPrimes

/-! # One geometric exceptional set for every Euler coefficient place -/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.LocalSpecialization

variable {K F : Type*} [Field K] [NumberField K]
  [Field F] [NumberField F] [Algebra K F]

omit [NumberField K] in
/-- Away from the coefficient characteristic, avoiding the contracted bad
set for `N` also avoids the set for `N * ℓ`. This set-theoretic step keeps
the geometric exceptional primes independent of the coefficient place. -/
theorem not_mem_badPrimesBelow_mul_of_away
    (x : F) (N ℓ : ℕ)
    (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∉ badPrimesBelow (K := K) x N)
    (hℓ : (ℓ : 𝓞 K) ∉ q.asIdeal) :
    q ∉ badPrimesBelow (K := K) x (N * ℓ) := by
  intro hbad
  obtain ⟨P, hbadP, hP⟩ := (mem_badPrimesBelow_iff (K := K)
    x (N * ℓ) q).mp hbad
  have hqP : P.under (𝓞 K) ∉ badPrimesBelow (K := K) x N := by
    simpa only [hP] using hq
  have hgood : P.GoodUnit x ∧ (N : 𝓞 F) ∉ P.asIdeal :=
    goodUnit_and_integer_away_of_under_not_bad (K := K) x N P hqP
  have hℓP : (ℓ : 𝓞 F) ∉ P.asIdeal := by
    intro hmem
    have hmemUnder : (ℓ : 𝓞 K) ∈ (P.under (𝓞 K)).asIdeal := by
      simpa only [HeightOneSpectrum.under_asIdeal, Ideal.mem_under, map_natCast] using hmem
    exact hℓ (hP ▸ hmemUnder)
  have hproduct : ((N * ℓ : ℕ) : 𝓞 F) ∉ P.asIdeal := by
    intro hmem
    have hmul : (N : 𝓞 F) * (ℓ : 𝓞 F) ∈ P.asIdeal := by
      simpa only [Nat.cast_mul] using hmem
    exact (P.isPrime.mem_or_mem hmul).elim hgood.2 hℓP
  rcases hbadP with hnotGood | hmem
  · exact hnotGood hgood.1
  · exact hproduct hmem

end HilbertModularity.LocalSpecialization
