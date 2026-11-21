/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ProperFrobeniusComparison
public import HilbertModularity.NumberTheory.CyclotomicInertia
public import HilbertModularity.NumberTheory.LocalGlobalInertia
public import HilbertModularity.NumberTheory.LocalSpecialization.GoodPrimes
public import HilbertModularity.NumberTheory.CyclotomicInertiaAway
public import HilbertModularity.RingTheory.IntegralClosure.Equiv
public import HilbertModularity.RingTheory.Ideal.InertiaEquiv
public import HilbertModularity.RingTheory.Ideal.UnderEquiv

/-! # Good-reduction inertia for the proper Euler realization

The proper Euler curve and its fixed primitive projector give an actual
cohomological Galois representation. Smooth proper base change at a good prime
supplies the raw inertia statement. The chosen generic real-field descent then
inherits it by its comparison with the proper cohomology.
-/

public noncomputable section

open AlgebraicGeometry
open HilbertModularity.Cyclotomic
open HilbertModularity.LocalSpecialization
open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

universe u

/-- [GPRV, Assumption 1 and Remark 7.1, p. 28] identify the smooth good
reduction of this completed Euler fibre. [src_milne_lec, Theorems 20.2 and 20.4,
pp. 127–128] give smooth proper base change for finite torsion cohomology;
the usual ℓ-adic passage and scalar extension give trivial inertia on the
actual proper `H¹` and its fixed `χ₀` projector. The correspondence with the
project's rationalized pro-étale cohomology API is an explicit admitted part
of this literature input. No extra exclusion is made at residue characteristic
two. -/
theorem properEuler_fixedPrimitive_inertia_eq_one_of_coprime
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    ∀ g : Qbar ≃ₐ[cyclotomicField N] Qbar,
      g ∈ Q.inertia (Qbar ≃ₐ[cyclotomicField N] Qbar) →
        properPrimitiveQbarGaloisRepresentation N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι g = 1 := by
  sorry

/-- The prime fixed-projector smooth-proper base-change interface is a
specialization of the coprime exponent version at the same family. -/
theorem properEuler_fixedPrimitive_inertia_eq_one
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    ∀ g : Qbar ≃ₐ[cyclotomicField N] Qbar,
      g ∈ Q.inertia (Qbar ≃ₐ[cyclotomicField N] Qbar) →
        properPrimitiveQbarGaloisRepresentation N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι g = 1 := by
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact properEuler_fixedPrimitive_inertia_eq_one_of_coprime
    N m ℓ L ι (le_trans (by decide : 3 ≤ 5) h5) hm hmN hcop
    𝒞 P hP hℓ Q ξ hξ

/-- The chosen real-field descent is unramified at every good prime lying
over a rational prime away from `N`. The rational-prime hypothesis only
identifies the prime for the cyclotomic inertia comparison; in particular it
allows the rational prime `2` when `N` is odd. -/
theorem ProperEulerRealDescent.inertia_eq_one_of_goodUnit_of_coprime
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver (Ideal.span {(q : ℤ)})]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    ∀ g ∈ Q.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar),
      D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        (realEulerClosureGaloisHom N g) = 1 := by
  let : Q.LiesOver (Ideal.span {(q : ℤ)}) :=
    Ideal.LiesOver.trans Q P.asIdeal _
  let ρ := (D.localSystem.arithmeticRepresentation
    (ProjectiveLine.puncturedPoint _ ξ)).comp (realEulerClosureGaloisHom N)
  have hraw := properEuler_fixedPrimitive_inertia_eq_one_of_coprime N m ℓ L ι
    h3 hm hmN hcop 𝒞 P hP hℓ Q ξ hξ
  have hrestricted :
      ∀ g ∈ Q.inertia (Qbar ≃ₐ[cyclotomicField N] Qbar),
        ρ (restrictCyclotomicGalois N g) = 1 := by
    intro g hg
    change D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N) g) = 1
    apply LinearMap.ext
    intro v
    apply (D.properComparison ξ).injective
    have h := D.properComparison_intertwines ξ g v
    rw [hraw g hg] at h
    simpa only [MonoidHom.comp_apply, Module.End.one_apply] using h
  let : Algebra (realCyclotomicField N) (cyclotomicField N) :=
    (IntermediateField.inclusion (realCyclotomicField_le N)).toRingHom.toAlgebra
  let : IsScalarTower (realCyclotomicField N) (cyclotomicField N) Qbar :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have he :
      (Q.inertia (Qbar ≃ₐ[cyclotomicField N] Qbar)).map
        (AlgEquiv.restrictScalarsHom (realCyclotomicField N)) =
        Q.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar) :=
    map_absoluteInertia_cyclotomic_to_real_of_not_dvd N q hq hqN Q
  intro g hg
  rw [← he] at hg
  obtain ⟨τ, hτ, rfl⟩ := hg
  exact hrestricted τ hτ


/-- The old prime-conductor good-unit statement is a specialization
of the coprime result, since `q ≠ N` is then equivalent to `q ∤ N`. -/
theorem ProperEulerRealDescent.inertia_eq_one_of_goodUnit
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (q : ℕ) (hq : q.Prime) (hqN : q ≠ N)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver (Ideal.span {(q : ℤ)})]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    ∀ g ∈ Q.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar),
      D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        (realEulerClosureGaloisHom N g) = 1 := by
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  have hqN' : ¬ q ∣ N := by
    intro hd
    exact hqN ((Nat.prime_dvd_prime_iff_eq hq hN).mp hd)
  exact D.inertia_eq_one_of_goodUnit_of_coprime N m ℓ L ι
    (le_trans (by decide : 3 ≤ 5) h5) hm hmN hcop 𝒞
    q hq hqN' P hP hℓ Q ξ hξ

instance realEulerCyclotomicAlgebra (N : ℕ) [NeZero N] :
    Algebra (realCyclotomicField N) (cyclotomicField N) :=
  (IntermediateField.inclusion (realCyclotomicField_le N)).toRingHom.toAlgebra

/-- Outside the contracted finite set of primes where the actual parameter or
its complement fails to be a unit, or where `N * ℓ` vanishes, the same chosen
descent is unramified at every prime of the cyclotomic field above a real
prime. In particular this includes residue characteristic two when eligible.
The only cohomological input is `properEuler_fixedPrimitive_inertia_eq_one`.
-/
theorem ProperEulerRealDescent.inertia_eq_one_outside_badPrimes_of_coprime
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ badPrimesBelow (K := realCyclotomicField N)
      (realEulerParameter N ξ) (N * ℓ))
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver q.asIdeal]
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    ∀ g ∈ Q.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar),
      D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        (realEulerClosureGaloisHom N g) = 1 := by
  have hunder : P.under (𝓞 (realCyclotomicField N)) = q := by
    apply HeightOneSpectrum.ext
    exact (show P.asIdeal.LiesOver q.asIdeal from inferInstance).over.symm
  have haway : P.GoodUnit (realEulerParameter N ξ) ∧
      (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal ∧
      (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal := by
    apply goodUnit_and_factors_away_of_under_not_bad
      (K := realCyclotomicField N) (realEulerParameter N ξ) N ℓ P
    rwa [hunder]
  let r := NumberField.primeBelow (cyclotomicField N) P
  let : Fact r.Prime := inferInstance
  have hrN : ¬ r ∣ N := by
    intro hd
    have hrmem : (r : 𝓞 (cyclotomicField N)) ∈ P.asIdeal := by
      apply (Ideal.mem_of_liesOver P.asIdeal (Ideal.span {(r : ℤ)}) (r : ℤ)).mp
      exact Ideal.mem_span_singleton_self _
    obtain ⟨k, hk⟩ := hd
    have hcast : (N : 𝓞 (cyclotomicField N)) =
        (r : 𝓞 (cyclotomicField N)) * (k : 𝓞 (cyclotomicField N)) := by
      exact_mod_cast hk
    exact haway.2.1 (hcast ▸ P.asIdeal.mul_mem_right (k : 𝓞 (cyclotomicField N)) hrmem)
  exact D.inertia_eq_one_of_goodUnit_of_coprime N m ℓ L ι h3 hm hmN hcop 𝒞
    r (Fact.out : r.Prime) hrN P haway.2.1 haway.2.2 Q ξ haway.1


/-- The prime-conductor finite-ramification deduction is the
specialization of the coprime result for the same descended local system. -/
theorem ProperEulerRealDescent.inertia_eq_one_outside_badPrimes
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ badPrimesBelow (K := realCyclotomicField N)
      (realEulerParameter N ξ) (N * ℓ))
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver q.asIdeal]
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    ∀ g ∈ Q.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar),
      D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        (realEulerClosureGaloisHom N g) = 1 := by
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact D.inertia_eq_one_outside_badPrimes_of_coprime N m ℓ L ι
    (le_trans (by decide : 3 ≤ 5) h5) hm hmN hcop 𝒞 ξ q hq P Q

/-- The fixed equivalence of algebraic closures identifies their actual
integer rings. -/
def realEulerClosureIntegerEquiv (N : ℕ) [NeZero N] :
    𝓞 (AlgebraicClosure (realCyclotomicField N)) ≃+* 𝓞 Qbar :=
  RingEquiv.mapIntegralClosure (RingEquiv.refl ℤ) (realEulerClosureEquiv N)
    (by intro x; simp)

/-- The isomorphism on integer rings uses the original closure equivalence
on the underlying algebraic integers. -/
theorem realEulerClosureIntegerEquiv_apply
    (N : ℕ) [NeZero N]
    (z : 𝓞 (AlgebraicClosure (realCyclotomicField N))) :
    ((realEulerClosureIntegerEquiv N z : 𝓞 Qbar) : Qbar) =
      realEulerClosureEquiv N z :=
  (rfl)

/-- Transport of algebraic integers is equivariant for the chosen Galois
conjugation. -/
theorem realEulerClosureIntegerEquiv_smul
    (N : ℕ) [NeZero N]
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar)
    (z : 𝓞 (AlgebraicClosure (realCyclotomicField N))) :
    realEulerClosureIntegerEquiv N ((realEulerClosureGaloisEquiv N g) • z) =
      g • realEulerClosureIntegerEquiv N z := by
  apply Subtype.ext
  change realEulerClosureEquiv N
      ((realEulerClosureGaloisEquiv N g) (z : AlgebraicClosure (realCyclotomicField N))) =
    g (realEulerClosureEquiv N z)
  rw [realEulerClosureGaloisEquiv_apply, realEulerClosureGaloisHom_apply,
    RingEquiv.apply_symm_apply]

/-- Transport of integer rings fixes the actual real-field integer ring. -/
theorem realEulerClosureIntegerEquiv_algebraMap
    (N : ℕ) [NeZero N] (x : 𝓞 (realCyclotomicField N)) :
    realEulerClosureIntegerEquiv N
        (algebraMap (𝓞 (realCyclotomicField N))
          (𝓞 (AlgebraicClosure (realCyclotomicField N))) x) =
      algebraMap (𝓞 (realCyclotomicField N)) (𝓞 Qbar) x := by
  apply Subtype.ext
  change realEulerClosureEquiv N
      (algebraMap (realCyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) x) =
      algebraMap (realCyclotomicField N) Qbar x
  exact realEulerClosureEquiv_algebraMap N x

/-- The same selected Euler descent is unramified at a specified prime of the
real field's own algebraic closure. The finite exceptional set is the actual
good-unit/conductor/coefficient-prime set, and no residue-characteristic-two
exclusion is added. -/
theorem ProperEulerRealDescent.inertia_eq_one_outside_badPrimes_realClosure_of_coprime
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ badPrimesBelow (K := realCyclotomicField N)
      (realEulerParameter N ξ) (N * ℓ))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    ∀ g ∈ Q.inertia
        (AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
          AlgebraicClosure (realCyclotomicField N)),
      D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ) g = 1 := by
  let e := realEulerClosureIntegerEquiv N
  let G := realEulerClosureGaloisEquiv N
  let QbarPrime : Ideal (𝓞 Qbar) := Q.map e
  let : QbarPrime.IsMaximal := inferInstance
  have hQbar : QbarPrime.LiesOver q.asIdeal := by
    constructor
    rw [Ideal.under_map_ringEquiv Q (RingEquiv.refl _) e
      (realEulerClosureIntegerEquiv_algebraMap N)]
    change q.asIdeal =
      (Q.under (𝓞 (realCyclotomicField N))).map
        (RingHom.id (𝓞 (realCyclotomicField N)))
    rw [Ideal.map_id]
    exact (show Q.LiesOver q.asIdeal from inferInstance).over
  let : QbarPrime.LiesOver q.asIdeal := hQbar
  let : IsScalarTower (realCyclotomicField N) (cyclotomicField N) Qbar :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (𝓞 (realCyclotomicField N))
      (𝓞 (cyclotomicField N)) (𝓞 Qbar) :=
    IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext (by rfl)
  let Pideal := QbarPrime.under (𝓞 (cyclotomicField N))
  let : Pideal.IsMaximal := inferInstance
  have hPover : Pideal.LiesOver q.asIdeal := by
    constructor
    calc
      q.asIdeal = QbarPrime.under (𝓞 (realCyclotomicField N)) := hQbar.over
      _ = Pideal.under (𝓞 (realCyclotomicField N)) :=
        (Ideal.under_under (A := 𝓞 (realCyclotomicField N))
          (B := 𝓞 (cyclotomicField N)) QbarPrime).symm
  let : Pideal.LiesOver q.asIdeal := hPover
  let P := heightOnePrimeOfLiesOver (F := cyclotomicField N) q Pideal
  let : P.asIdeal.LiesOver q.asIdeal := by
    simpa only [P, heightOnePrimeOfLiesOver_asIdeal] using hPover
  let : QbarPrime.LiesOver P.asIdeal := by
    simpa only [P, heightOnePrimeOfLiesOver_asIdeal] using
      (show QbarPrime.LiesOver Pideal from inferInstance)
  have hmap :
      QbarPrime.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar) =
        (Q.inertia
          (AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
            AlgebraicClosure (realCyclotomicField N))).map G.symm.toMonoidHom := by
    exact Ideal.inertia_map_ringEquiv Q e G.symm (by
      intro g z
      have h := realEulerClosureIntegerEquiv_smul N (G.symm g) z
      simpa only [show realEulerClosureGaloisEquiv N (G.symm g) = g from
        G.apply_symm_apply g] using h)
  intro g hg
  have hgbar : G.symm g ∈ QbarPrime.inertia
      (Qbar ≃ₐ[realCyclotomicField N] Qbar) := by
    rw [hmap]
    exact ⟨g, hg, rfl⟩
  have hraw := D.inertia_eq_one_outside_badPrimes_of_coprime N m ℓ L ι h3 hm hmN hcop
    𝒞 ξ q hq P (Q := QbarPrime) (G.symm g) hgbar
  have hident : realEulerClosureGaloisHom N (G.symm g) = g := by
    rw [← realEulerClosureGaloisEquiv_apply]
    exact G.apply_symm_apply g
  exact hident ▸ hraw


/-- The prime-conductor real-closure unramifiedness theorem is the
same-fibre specialization of the coprime deduction. -/
theorem ProperEulerRealDescent.inertia_eq_one_outside_badPrimes_realClosure
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ badPrimesBelow (K := realCyclotomicField N)
      (realEulerParameter N ξ) (N * ℓ))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    ∀ g ∈ Q.inertia
        (AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
          AlgebraicClosure (realCyclotomicField N)),
      D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ) g = 1 := by
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact D.inertia_eq_one_outside_badPrimes_realClosure_of_coprime
    N m ℓ L ι (le_trans (by decide : 3 ≤ 5) h5) hm hmN hcop
    𝒞 ξ q hq Q

end HilbertModularity.Hypergeometric
