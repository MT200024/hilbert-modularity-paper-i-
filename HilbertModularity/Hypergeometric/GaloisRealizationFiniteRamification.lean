/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GoodReductionInertia
public import HilbertModularity.Hypergeometric.DarmonHodgeComparison

/-! # Finite ramification of the selected proper Euler descent

The exceptional primes are obtained from the actual Euler parameter and the
integer `N * ℓ`. The cohomological inertia input is smooth proper base change
for the chosen model; the cyclotomic factor is unramified away from `ℓ`.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open HilbertModularity.LocalSpecialization
open scoped NumberField

namespace HilbertModularity.Hypergeometric

/-- The finite bad-prime set for the actual Euler fibre at any conductor.
It excludes precisely nonunit parameter, conductor and coefficient primes. -/
def properEulerBadPrimesOfConductor (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Finset (HeightOneSpectrum (𝓞 (realCyclotomicField N))) := by
  have hx0 : realEulerParameter N ξ ≠ 0 :=
    (realEulerParameter_isUnit N ξ).ne_zero
  have hx1 : realEulerParameter N ξ ≠ 1 := by
    intro hx
    exact (one_sub_realEulerParameter_isUnit N ξ).ne_zero (by rw [hx, sub_self])
  have hprod : N * ℓ ≠ 0 :=
    Nat.mul_ne_zero (NeZero.ne N) (Fact.out : ℓ.Prime).ne_zero
  exact (badPrimesBelow_finite (K := realCyclotomicField N)
    (realEulerParameter N ξ) hx0 hx1 (N * ℓ) hprod).toFinset

/-- Membership in the finite Euler exceptional set is exactly membership
in the underlying parameter/conductor/coefficient bad-prime set. -/
theorem not_mem_properEulerBadPrimesOfConductor_iff
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N))) :
    q ∉ properEulerBadPrimesOfConductor N ℓ ξ ↔
      q ∉ badPrimesBelow (K := realCyclotomicField N)
        (realEulerParameter N ξ) (N * ℓ) := by
  simp only [properEulerBadPrimesOfConductor, Set.Finite.mem_toFinset]

/-- The finite set of real-field primes below bad parameter, conductor, or
coefficient primes for the actual Euler fibre. -/
def properEulerBadPrimes (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hN : N.Prime)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Finset (HeightOneSpectrum (𝓞 (realCyclotomicField N))) := by
  have hx0 : realEulerParameter N ξ ≠ 0 :=
    (realEulerParameter_isUnit N ξ).ne_zero
  have hx1 : realEulerParameter N ξ ≠ 1 := by
    intro hx
    have h := (one_sub_realEulerParameter_isUnit N ξ).ne_zero
    exact h (by rw [hx, sub_self])
  have hprod : N * ℓ ≠ 0 :=
    Nat.mul_ne_zero hN.ne_zero (Fact.out : ℓ.Prime).ne_zero
  exact (badPrimesBelow_finite (K := realCyclotomicField N)
    (realEulerParameter N ξ) hx0 hx1 (N * ℓ) hprod).toFinset

/-- The prime bad-prime API is the same finite set as the conductor-wide
definition, with no changed exceptional primes. -/
theorem properEulerBadPrimes_eq_of_conductor (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hN : N.Prime)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    properEulerBadPrimes N ℓ hN ξ = properEulerBadPrimesOfConductor N ℓ ξ := by
  unfold properEulerBadPrimes properEulerBadPrimesOfConductor
  rfl

/-- The chosen descent's normalized arithmetic determinant is unramified
outside its actual finite bad-prime set. This is the finite-ramification input
used at the original fibre in the Darmon determinant argument. -/
theorem ProperEulerRealDescent.normalizedDeterminant_inertia_eq_one_of_coprime
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N))
    (hg : g ∈ Q.inertia _)
    (hq : q ∉ properEulerBadPrimesOfConductor N ℓ ξ) :
    puncturedFiberNormalizedDeterminant (realCyclotomicField N) ℓ L ξ
      D.localSystem g = 1 := by
  have hq' : q ∉ badPrimesBelow (K := realCyclotomicField N)
      (realEulerParameter N ξ) (N * ℓ) := by
    simpa only [properEulerBadPrimesOfConductor, Set.Finite.mem_toFinset] using hq
  have hD := D.inertia_eq_one_outside_badPrimes_realClosure_of_coprime N m ℓ L ι
    h3 hm hmN hcop 𝒞 ξ q hq' Q g hg
  obtain ⟨P, hP⟩ :=
    exists_prime_above (F := cyclotomicField N) q
  have haway := goodUnit_and_factors_away_of_under_not_bad
    (K := realCyclotomicField N) (realEulerParameter N ξ) N ℓ P (hP ▸ hq')
  have hℓq : (ℓ : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal := by
    intro hmem
    let : P.asIdeal.LiesOver q.asIdeal := by
      constructor
      simpa using congrArg HeightOneSpectrum.asIdeal hP.symm
    have hmemP : (ℓ : 𝓞 (cyclotomicField N)) ∈ P.asIdeal := by
      simpa only [map_natCast] using
        (Ideal.mem_of_liesOver P.asIdeal q.asIdeal
          (ℓ : 𝓞 (realCyclotomicField N))).mp hmem
    exact haway.2.2 hmemP
  have hℓQ : (ℓ : 𝓞 (AlgebraicClosure (realCyclotomicField N))) ∉ Q := by
    intro hmem
    have hmemq : (ℓ : 𝓞 (realCyclotomicField N)) ∈ q.asIdeal := by
      apply (Ideal.mem_of_liesOver Q q.asIdeal
        (ℓ : 𝓞 (realCyclotomicField N))).mpr
      simpa only [map_natCast] using hmem
    exact hℓq hmemq
  have hcycl := Field.cyclotomicCharacterWithCoefficients_eq_one_on_inertia
    (realCyclotomicField N) ℓ L Q hℓQ ⟨g, hg⟩
  have hdet :
      (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
        D.localSystem).determinantCharacter g = 1 := by
    apply Units.ext
    rw [Representation.determinantCharacter_coe]
    change LinearMap.det
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ) g) = 1
    rw [hD]
    exact LinearMap.det_id
  rw [puncturedFiberNormalizedDeterminant_apply, hdet, hcycl, one_mul]


/-- The prime normalized-determinant finite-ramification theorem is
the exact same-fibre specialization of the conductor-wide deduction. -/
theorem ProperEulerRealDescent.normalizedDeterminant_inertia_eq_one
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N))
    (hg : g ∈ Q.inertia _)
    (hq : q ∉ properEulerBadPrimes N ℓ hN ξ) :
    puncturedFiberNormalizedDeterminant (realCyclotomicField N) ℓ L ξ
      D.localSystem g = 1 := by
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  apply D.normalizedDeterminant_inertia_eq_one_of_coprime N m ℓ L ι
    (le_trans (by decide : 3 ≤ 5) h5) hm hmN hcop 𝒞 ξ q Q g hg
  simpa only [← properEulerBadPrimes_eq_of_conductor N ℓ hN ξ] using hq

end HilbertModularity.Hypergeometric
