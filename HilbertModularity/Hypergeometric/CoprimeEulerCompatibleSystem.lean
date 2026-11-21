/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationCompatibleSystem
public import HilbertModularity.Hypergeometric.CoprimeEulerRealization

/-! # Compatible systems of the chosen coprime Euler quotients

The semisimplicity and common-polynomial literature interfaces already
apply to the fixed quotient at arbitrary conductor. Here finite ramification
and the common exceptional set are assembled for every coprime exponent,
using [GPRV, Theorem 9.2] through those existing named inputs.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic LocalSpecialization

variable (N m : ℕ) [NeZero N]
  (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField N))

local instance coprimeEulerCompletionNorm (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField N)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField N))
    (WithZero (Multiplicative ℤ))

/-- The conductor and parameter exceptional set is finite without any
primality assumption on the conductor. -/
theorem commonEulerBadPrimes_finite_of_neZero :
    (commonEulerBadPrimes N ξ).Finite := by
  rw [commonEulerBadPrimes_eq]
  apply badPrimesBelow_finite
  · exact (realEulerParameter_isUnit N ξ).ne_zero
  · intro h
    exact (one_sub_realEulerParameter_isUnit N ξ).ne_zero (by rw [h, sub_self])
  · exact NeZero.ne N

include h3 hm hmN hcop in
/-- Completion actions of the same coprime Euler quotient are unramified
at every canonical good prime away from their own coefficient characteristic. -/
theorem commonEulerCompletionAction_unramified_of_coprime
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ commonEulerBadPrimes N ξ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (hp : (NumberField.primeBelow (cyclotomicField N) w :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N))
    (hg : g ∈ Q.inertia _) :
    commonEulerCompletionAction N m 𝒞 R ξ w g = 1 := by
  let : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let D := commonEulerCompletionDescent N m 𝒞 R w
  have hraw := D.inertia_eq_one_outside_badPrimes_realClosure_of_coprime N m
    (NumberField.primeBelow (cyclotomicField N) w)
    (w.adicCompletion (cyclotomicField N))
    (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N)))
    h3 hm hmN hcop 𝒞 ξ q
    (commonEulerBadPrimes_away_product N ξ
      (NumberField.primeBelow (cyclotomicField N) w) q hq hp) Q g hg
  exact (commonEulerCompletionActionEquiv N m 𝒞 R ξ w).apply_eq_one_of g hraw

/-- The actual raw Euler compatible system at every coprime conductor.
The family and quotient are selected once before all coefficient places.
Its coefficient field is the stated cyclotomic extension; no assertion of
minimal coefficient-field descent is hidden in this construction. -/
def chosenCoprimeRawEulerCompatibleSystem :
    NumberFieldCompatibleSystem (realCyclotomicField N) (cyclotomicField N) := by
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  exact {
    residueCharacteristic := NumberField.primeBelow (cyclotomicField N)
    residueCharacteristic_prime := fun w =>
      (NumberField.primeBelow_prime (cyclotomicField N) w).out
    coefficientPrime := fun w => NumberField.liesOver_primeBelow (cyclotomicField N) w
    action := commonEulerCompletionAction N m 𝒞 R ξ
    continuous := continuous_commonEulerCompletionAction_entry N m 𝒞 R ξ
    semisimple := commonEulerCompletionAction_isSemisimple N m 𝒞 R ξ
    bad := commonEulerBadPrimes N ξ
    bad_finite := commonEulerBadPrimes_finite_of_neZero N ξ
    polynomial := commonEulerFrobeniusPolynomial N m 𝒞 R ξ
    unramified := by
      intro w q hq P _ hP hp Q _ _ g hg
      subst P
      exact commonEulerCompletionAction_unramified_of_coprime
        N m h3 hm hmN hcop ξ 𝒞 R w q hq Q hp g hg
    frobenius_charpoly := by
      intro w q hq P _ hP hp Q _ _
      subst P
      exact commonEulerFrobeniusPolynomial_spec N m 𝒞 R ξ q hq w hp Q
  }

/-- The chosen all-conductor raw system has the canonical parameter and
conductor bad set, independent of the coefficient place. -/
theorem chosenCoprimeRawEulerCompatibleSystem_bad :
    (chosenCoprimeRawEulerCompatibleSystem N m h3 hm hmN hcop ξ).bad =
      commonEulerBadPrimes N ξ := (rfl)

/-- Its action uses exactly the chosen quotient and its original coefficient embedding. -/
theorem chosenCoprimeRawEulerCompatibleSystem_action
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    (chosenCoprimeRawEulerCompatibleSystem N m h3 hm hmN hcop ξ).action w =
      commonEulerCompletionAction N m (chosenCoprimeEulerFamily N m h3 hm hmN hcop)
        (chosenCoprimeRawEulerRealization N m h3 hm hmN hcop) ξ w := (rfl)

end HilbertModularity.Hypergeometric
