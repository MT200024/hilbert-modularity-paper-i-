/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFamily
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientDescent

/-! # One raw Euler quotient for every coprime conductor

The raw quotient of [GPRV, Theorem 9.2 and Proposition 9.5, pp. 40–41]
is chosen once, before all fibres and coefficient places. At even conductor
this is not yet the effective hypergeometric realization: the auxiliary
character of [GPRV, Definition 8.8] must be tensored to exponent m.
-/

public noncomputable section

open AlgebraicGeometry
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

/-- The actual exponent-m smooth proper Euler family at every coprime
conductor, selected from [EsnaultViehweg, §3]. -/
def chosenCoprimeEulerFamily
    (N m : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N) :
    SmoothProperEulerFamily N m :=
  Classical.choice (exists_smoothProperEulerFamily_of_coprime N m
    h3 hm hmN hcop.symm)

/-- One raw quotient with all labelled coefficient realizations, before
applying the possible auxiliary κ-twist. -/
def chosenCoprimeRawEulerRealization
    (N m : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N) :
    CommonRealEulerQuotientRealization N m
      (chosenCoprimeEulerFamily N m h3 hm hmN hcop) :=
  Classical.choice (exists_commonRealEulerQuotientRealization_of_coprime
    N m (chosenCoprimeEulerFamily N m h3 hm hmN hcop)
    h3 hm hmN hcop)

/-- The raw labelled component has rank two at every fibre and every
coefficient place, including composite conductors. -/
theorem chosenCoprimeRawEulerRealization_rank_two
    (N m : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
    Module.finrank L
      ((R.placeDescent N m 𝒞 ℓ L ι).localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) = 2 := by
  dsimp only
  rw [CommonRealEulerQuotientRealization.placeDescent_eq_atPlace]
  exact ((chosenCoprimeRawEulerRealization N m h3 hm hmN hcop).atPlace
    ℓ L ι).descent.rank_two ξ

end HilbertModularity.Hypergeometric
