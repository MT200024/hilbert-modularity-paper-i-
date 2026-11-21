/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.CoprimeEulerRealization
public import HilbertModularity.Hypergeometric.GprvKappaCharacter
public import HilbertModularity.RepresentationTheory.CharacterTwist
public import HilbertModularity.RepresentationTheory.FiniteCharacterContinuity
public import Mathlib.LinearAlgebra.Trace
public import HilbertModularity.Hypergeometric.ProperFrobeniusComparison
public import HilbertModularity.Hypergeometric.GaloisRealizationFiniteRamification

/-! # The effective Euler action with the GPRV κ-normalization

The proper Euler quotient is chosen once at each coprime conductor. The
single GPRV character over the real field is chosen separately and raised
to exponent m exactly once. The raw quotient action is then twisted at
every fibre. For odd N this is literally the checked raw action.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms
open HilbertModularity.LocalSpecialization

/-- Twisting scales the trace by the actual scalar character value. -/
private theorem trace_characterTwist
    {L G V : Type*} [Field L] [Group G] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V]
    (ρ : Representation L G V) (χ : G →* Lˣ) (g : G) :
    LinearMap.trace L V ((ρ.characterTwist χ) g) =
      (χ g : L) * LinearMap.trace L V (ρ g) := by
  let b := Module.Free.chooseBasis L V
  change LinearMap.trace L V ((χ g : L) • ρ g) = _
  rw [LinearMap.trace_eq_matrix_trace L b,
    LinearMap.trace_eq_matrix_trace L b, map_smul, Matrix.trace_smul]
  rfl

/-- The finite κ_N^m character in an actual coefficient field. Its source
is the one selected real-field extension of [GPRV, Definition 8.8,
Corollary 8.10 and Lemma 9.4]. -/
def gprvKappaLocal
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (m : ℕ)
    (L : Type) [Field L] [Algebra ℚ L] :
    AbsoluteGalois (realCyclotomicField N) →* Lˣ :=
  ((Units.map (algebraMap ℚ L).toMonoidHom).comp
    (chosenGprvKappaRealCharacter N h3).toMonoidHom) ^ m

/-- The coefficient value is the image of the one rational κ value,
raised to the fixed Euler exponent. -/
theorem gprvKappaLocal_coe
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (m : ℕ)
    (L : Type) [Field L] [Algebra ℚ L]
    (g : AbsoluteGalois (realCyclotomicField N)) :
    (gprvKappaLocal N h3 m L g : L) =
      (algebraMap ℚ L ((chosenGprvKappaRealCharacter N h3).toMonoidHom g : ℚ)) ^ m :=
  (rfl)

/-- The local κ_N^m character is continuous at any coefficient topology.
This follows from local constancy of the selected finite algebraic
character, independent of continuity of the embedding ℚ→L. -/
theorem continuous_gprvKappaLocal
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (m : ℕ)
    (L : Type) [Field L] [Algebra ℚ L] [TopologicalSpace Lˣ] :
    Continuous (gprvKappaLocal N h3 m L) := by
  have h := (chosenGprvKappaRealCharacter N h3).isLocallyConstant.comp
    (fun u : ℚˣ => ((Units.map (algebraMap ℚ L).toMonoidHom) u) ^ m)
  change Continuous (fun g => ((Units.map (algebraMap ℚ L).toMonoidHom)
    ((chosenGprvKappaRealCharacter N h3).toMonoidHom g)) ^ m)
  exact h.continuous

/-- The actual κ_N^m value has square one on every real-field Galois
element, including even conductors [GPRV, Lemma 9.4]. -/
theorem gprvKappaLocal_apply_sq
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (m : ℕ)
    (L : Type) [Field L] [Algebra ℚ L]
    (g : AbsoluteGalois (realCyclotomicField N)) :
    (gprvKappaLocal N h3 m L g) ^ 2 = 1 := by
  change (((Units.map (algebraMap ℚ L).toMonoidHom)
    ((chosenGprvKappaRealCharacter N h3).toMonoidHom g)) ^ m) ^ 2 = 1
  rw [← pow_mul, Nat.mul_comm m 2, pow_mul, ← map_pow,
    chosenGprvKappaRealCharacter_sq N h3 g, map_one, one_pow]

/-- A square-one character has finite image at every coefficient field. -/
theorem finite_gprvKappaLocal
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (m : ℕ)
    (L : Type) [Field L] [Algebra ℚ L] :
    (Set.range (gprvKappaLocal N h3 m L)).Finite := by
  let f : ℚˣ → Lˣ := fun u =>
    ((Units.map (algebraMap ℚ L).toMonoidHom) u) ^ m
  apply ((chosenGprvKappaRealCharacter N h3).finite_range.image f).subset
  rintro u ⟨g, rfl⟩
  exact ⟨(chosenGprvKappaRealCharacter N h3).toMonoidHom g,
    ⟨g, rfl⟩, rfl⟩

/-- The selected coefficient character has finite order as a character,
with a uniform square-one witness independent of the coefficient place. -/
theorem gprvKappaLocal_isOfFinOrder
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (m : ℕ)
    (L : Type) [Field L] [Algebra ℚ L] :
    IsOfFinOrder (gprvKappaLocal N h3 m L) := by
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨2, by decide, ?_⟩
  apply MonoidHom.ext
  intro g
  exact gprvKappaLocal_apply_sq N h3 m L g

/-- At a cyclotomic prime away from 2N, the selected local κ_N^m factor
is the normalized power-residue sign under the actual coefficient map.
This is the algebraic transport of [GPRV, Lemma 8.9, p. 33]. -/
theorem gprvKappaLocal_geometricFrobenius
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (m : ℕ)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hN : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (h2N : (2 * N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (L : Type) [Field L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L) :
    (gprvKappaLocal N h3 m L
      (cyclotomicToRealEulerGaloisHom N
        (absoluteGeometricFrobenius N P Q)) : L) =
      ι ((cyclotomicPowerResidueMulChar N P.asIdeal hN ^ m) (-1)) := by
  let g := cyclotomicToRealEulerGaloisHom N (absoluteGeometricFrobenius N P Q)
  have hs := chosenGprvKappaRealCharacter_geometricFrobenius N h3 P hN h2N Q
  have hbase : algebraMap ℚ L
      (((chosenGprvKappaRealCharacter N h3).toMonoidHom g : ℚ)) =
      ι (cyclotomicPowerResidueMulChar N P.asIdeal hN (-1)) := by
    let r : ℚ := ((chosenGprvKappaRealCharacter N h3).toMonoidHom g : ℚ)
    have hrat : ι (algebraMap ℚ (cyclotomicField N) r) =
        algebraMap ℚ L r := by
      simp
    exact hrat.symm.trans (congrArg ι hs)
  have hpow : (cyclotomicPowerResidueMulChar N P.asIdeal hN ^ m) (-1) =
      (cyclotomicPowerResidueMulChar N P.asIdeal hN (-1)) ^ m := by
    simpa only [Units.val_neg, Units.val_one] using
      (cyclotomicPowerResidueMulChar N P.asIdeal hN).pow_apply_coe m
        (-1 : (𝓞 (cyclotomicField N) ⧸ P.asIdeal)ˣ)
  rw [hpow, map_pow, ← hbase]
  rfl

/-- At even conductor, every prime away from N is automatically away
from 2N. Thus the κ Frobenius dictionary adds no exceptional prime. -/
theorem two_mul_conductor_away_of_even
    (N : ℕ) [NeZero N] (hEven : Even N)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hN : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) :
    (2 * N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal := by
  intro hmem
  have hmul : (2 : 𝓞 (cyclotomicField N)) *
      (N : 𝓞 (cyclotomicField N)) ∈ P.asIdeal := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmem
  rcases P.isPrime.mem_or_mem hmul with h2 | hNmem
  · obtain ⟨k, hk⟩ := hEven
    have hk2 : N = 2 * k := by omega
    have hcast : (N : 𝓞 (cyclotomicField N)) =
        (2 : 𝓞 (cyclotomicField N)) * (k : 𝓞 (cyclotomicField N)) := by
      exact_mod_cast hk2
    exact hN (hcast ▸ P.asIdeal.mul_mem_right (k : 𝓞 (cyclotomicField N)) h2)
  · exact hN hNmem

/-- A finite exceptional set for the effective fibre. The two visible
parts are the chosen Euler model's bad primes and the one selected
GPRV character's bad primes; neither depends on a new fibrewise
character choice. -/
def effectiveEulerBadPrimes
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Finset (HeightOneSpectrum (𝓞 (realCyclotomicField N))) := by
  classical
  exact properEulerBadPrimesOfConductor N ℓ ξ ∪
    (chosenGprvKappaRealCharacter N h3).bad_finite.toFinset

/-- The chosen κ_N^m is the trivial character when N is odd. -/
theorem gprvKappaLocal_eq_one_of_odd
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (hOdd : Odd N) (m : ℕ)
    (L : Type) [Field L] [Algebra ℚ L] :
    gprvKappaLocal N h3 m L = 1 := by
  apply MonoidHom.ext
  intro g
  simp [gprvKappaLocal,
    chosenGprvKappaRealCharacter_eq_one_of_odd N h3 hOdd]

/-- The actual arithmetic fibre of the chosen raw Euler quotient, twisted
by the one source κ_N^m character. All fibres share the same character and
quotient; for even N this is the effective GPRV normalization. -/
def chosenEffectiveEulerAction
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
    Representation L (AbsoluteGalois (realCyclotomicField N))
      ((R.placeDescent N m 𝒞 ℓ L ι).localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  ((R.placeDescent N m 𝒞 ℓ L ι).localSystem.arithmeticRepresentation
    (ProjectiveLine.puncturedPoint _ ξ)).characterTwist
      (gprvKappaLocal N h3 m L)

/-- The effective action is the same selected raw fibre scaled by the
single selected κ_N^m value. -/
theorem chosenEffectiveEulerAction_apply
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (g : AbsoluteGalois (realCyclotomicField N))
    (v : ((chosenCoprimeRawEulerRealization N m h3 hm hmN hcop).placeDescent
      N m (chosenCoprimeEulerFamily N m h3 hm hmN hcop) ℓ L ι).localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :
    chosenEffectiveEulerAction N m ℓ h3 hm hmN hcop L ι ξ g v =
      (gprvKappaLocal N h3 m L g : L) •
        ((chosenCoprimeRawEulerRealization N m h3 hm hmN hcop).placeDescent
          N m (chosenCoprimeEulerFamily N m h3 hm hmN hcop) ℓ L ι
          ).localSystem.arithmeticRepresentation
            (ProjectiveLine.puncturedPoint _ ξ) g v := by
  rfl

/-- The κ twist leaves the actual labelled fibre rank equal to two. -/
theorem chosenEffectiveEulerAction_rank_two
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Module.finrank L
      (((chosenCoprimeRawEulerRealization N m h3 hm hmN hcop).placeDescent
        N m (chosenCoprimeEulerFamily N m h3 hm hmN hcop) ℓ L ι).localSystem.toFunctor.obj
          (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) = 2 :=
  chosenCoprimeRawEulerRealization_rank_two N m h3 hm hmN hcop ℓ L ι ξ

/-- At odd conductor the selected effective arithmetic action is exactly
the raw chosen quotient action, with no additional Tate twist. -/
theorem chosenEffectiveEulerAction_eq_raw_of_odd
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N) (hOdd : Odd N)
    (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    chosenEffectiveEulerAction N m ℓ h3 hm hmN hcop L ι ξ =
      ((chosenCoprimeRawEulerRealization N m h3 hm hmN hcop).placeDescent
        N m (chosenCoprimeEulerFamily N m h3 hm hmN hcop) ℓ L ι
        ).localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ) := by
  unfold chosenEffectiveEulerAction
  rw [gprvKappaLocal_eq_one_of_odd N h3 hOdd m L]
  ext g v
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let ρ := (R.placeDescent N m 𝒞 ℓ L ι).localSystem.arithmeticRepresentation
    (ProjectiveLine.puncturedPoint _ ξ)
  change (1 : L) • ρ g v = ρ g v
  exact one_smul L (ρ g v)

/-- The actual effective Euler action has the normalized symmetric
GPRV/McCarthy scalar trace at every good prime away from the coefficient
characteristic. For even N the single κ_N^m twist supplies exactly
χ_P(-1)^m [GPRV, Lemma 8.9]; for odd N it is trivial, so eligible primes
above two remain included. No extra Tate twist is inserted. -/
theorem chosenEffectiveEulerAction_geometricFrobenius_trace
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hN : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
    let D := R.placeDescent N m 𝒞 ℓ L ι
    letI : Module.Finite L
        (D.localSystem.toFunctor.obj
          (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
      D.localSystem.finite _
    LinearMap.trace L _
      (chosenEffectiveEulerAction N m ℓ h3 hm hmN hcop L ι ξ
        ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
          (absoluteGeometricFrobenius N P Q))) =
      ι (normalizedCyclotomicEulerTrace N P.asIdeal hN m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 ℓ L ι
  let : Module.Finite L
      (D.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
    D.localSystem.finite _
  let x := ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ
  let gF := absoluteGeometricFrobenius N P Q
  let g := (realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N) gF
  let ρ := D.localSystem.arithmeticRepresentation x
  let χ := gprvKappaLocal N h3 m L
  have hraw := D.geometricFrobenius_trace_eq_eulerCurveSum_of_coprime
    N m ℓ L ι h3 hm hmN hcop 𝒞 P hN hℓ Q ξ hξ
  have ht := trace_characterTwist ρ χ g
  change LinearMap.trace L _ ((ρ.characterTwist χ) g) = _
  rw [ht, hraw]
  by_cases hOdd : Odd N
  · have hχ : (χ g : L) = 1 := by
      rw [show χ = 1 from gprvKappaLocal_eq_one_of_odd N h3 hOdd m L]
      rfl
    rw [hχ, one_mul, normalizedCyclotomicEulerTrace_eq_odd N P hN hOdd m,
      map_neg]
  · have hEven : Even N := Nat.not_odd_iff_even.mp hOdd
    have h2N := two_mul_conductor_away_of_even N hEven P hN
    have hχ : (χ g : L) =
        ι ((cyclotomicPowerResidueMulChar N P.asIdeal hN ^ m) (-1)) := by
      simpa only [χ, g, gF, MonoidHom.comp_apply,
        cyclotomicToRealEulerGaloisHom_apply] using
        gprvKappaLocal_geometricFrobenius N h3 m P hN h2N Q L ι
    rw [hχ, normalizedCyclotomicEulerTrace_eq_mul]
    rw [map_mul ι, map_neg ι]
    ring

/-- The actual effective arithmetic action is unramified outside its
explicit finite exceptional set. The raw smooth proper specialization
and the selected finite κ character are both trivial on the same
inertia element; scalar tensoring then preserves the identity. -/
theorem chosenEffectiveEulerAction_inertia_eq_one
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ effectiveEulerBadPrimes N ℓ h3 ξ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N))
    (hg : g ∈ Q.inertia _) :
    chosenEffectiveEulerAction N m ℓ h3 hm hmN hcop L ι ξ g = 1 := by
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 ℓ L ι
  classical
  have hqRaw : q ∉ properEulerBadPrimesOfConductor N ℓ ξ := by
    intro h
    exact hq (by
      simp only [effectiveEulerBadPrimes, Finset.mem_union]
      exact Or.inl h)
  have hqKappa : q ∉ (chosenGprvKappaRealCharacter N h3).bad := by
    intro h
    exact hq (by
      simp only [effectiveEulerBadPrimes, Finset.mem_union]
      exact Or.inr ((chosenGprvKappaRealCharacter N h3).bad_finite.mem_toFinset.mpr h))
  have hqRaw' : q ∉ badPrimesBelow (K := realCyclotomicField N)
      (realEulerParameter N ξ) (N * ℓ) := by
    exact (not_mem_properEulerBadPrimesOfConductor_iff N ℓ ξ q).mp hqRaw
  have hD := D.inertia_eq_one_outside_badPrimes_realClosure_of_coprime
    N m ℓ L ι h3 hm hmN hcop 𝒞 ξ q hqRaw' Q g hg
  have hκ := (chosenGprvKappaRealCharacter N h3).unramified q hqKappa
    q.asIdeal rfl Q g hg
  have hχ : (gprvKappaLocal N h3 m L g : L) = 1 := by
    change (((Units.map (algebraMap ℚ L).toMonoidHom)
      ((chosenGprvKappaRealCharacter N h3).toMonoidHom g)) ^ m : L) = 1
    simp [hκ]
  apply LinearMap.ext
  intro v
  change (gprvKappaLocal N h3 m L g : L) •
    D.localSystem.arithmeticRepresentation
      (ProjectiveLine.puncturedPoint _ ξ) g v = v
  rw [hχ, one_smul, hD]
  rfl

/-- The κ normalization introduces no new finite ramification
exception. For odd N it is trivial; for even N its conductor divides
2N and every prime away from N is automatically away from 2N.
Thus the actual effective action is unramified outside the raw
Euler parameter, conductor and coefficient exceptional set, with
no additional excluded primes. -/
theorem chosenEffectiveEulerAction_inertia_eq_one_outside_raw_bad
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ properEulerBadPrimesOfConductor N ℓ ξ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N))
    (hg : g ∈ Q.inertia _) :
    chosenEffectiveEulerAction N m ℓ h3 hm hmN hcop L ι ξ g = 1 := by
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 ℓ L ι
  have hqRaw : q ∉ badPrimesBelow (K := realCyclotomicField N)
      (realEulerParameter N ξ) (N * ℓ) :=
    (not_mem_properEulerBadPrimesOfConductor_iff N ℓ ξ q).mp hq
  by_cases hOdd : Odd N
  · rw [chosenEffectiveEulerAction_eq_raw_of_odd N m ℓ h3 hOdd
      hm hmN hcop L ι ξ]
    exact D.inertia_eq_one_outside_badPrimes_realClosure_of_coprime
      N m ℓ L ι h3 hm hmN hcop 𝒞 ξ q hqRaw Q g hg
  · have hEven : Even N := Nat.not_odd_iff_even.mp hOdd
    obtain ⟨P, hP⟩ := exists_prime_above (F := cyclotomicField N) q
    have haway := goodUnit_and_factors_away_of_under_not_bad
      (K := realCyclotomicField N) (realEulerParameter N ξ) N ℓ P
      (hP ▸ hqRaw)
    have hNq : (N : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal := by
      intro hmem
      let : P.asIdeal.LiesOver q.asIdeal := by
        constructor
        simpa using congrArg HeightOneSpectrum.asIdeal hP.symm
      have hmemP : (N : 𝓞 (cyclotomicField N)) ∈ P.asIdeal := by
        simpa only [map_natCast] using
          (Ideal.mem_of_liesOver P.asIdeal q.asIdeal
            (N : 𝓞 (realCyclotomicField N))).mp hmem
      exact haway.2.1 hmemP
    have h2N : (2 * N : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal := by
      intro hmem
      have hmul : (2 : 𝓞 (realCyclotomicField N)) *
          (N : 𝓞 (realCyclotomicField N)) ∈ q.asIdeal := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmem
      rcases q.isPrime.mem_or_mem hmul with h2 | hNmem
      · obtain ⟨k, hk⟩ := hEven
        have hk2 : N = 2 * k := by omega
        have hcast : (N : 𝓞 (realCyclotomicField N)) =
            (2 : 𝓞 (realCyclotomicField N)) *
              (k : 𝓞 (realCyclotomicField N)) := by
          exact_mod_cast hk2
        exact hNq (hcast ▸ q.asIdeal.mul_mem_right _ h2)
      · exact hNq hNmem
    have hκbad := chosenGprvKappaRealCharacter_not_bad_of_away N h3 q h2N
    have hqEff : q ∉ effectiveEulerBadPrimes N ℓ h3 ξ := by
      classical
      simp only [effectiveEulerBadPrimes, Finset.mem_union, not_or,
        Set.Finite.mem_toFinset]
      exact ⟨hq, hκbad⟩
    exact chosenEffectiveEulerAction_inertia_eq_one
      N m ℓ h3 hm hmN hcop L ι ξ q hqEff Q g hg


end HilbertModularity.Hypergeometric
