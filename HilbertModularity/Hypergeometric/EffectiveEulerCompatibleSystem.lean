/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.CoprimeEulerCompatibleSystem
public import HilbertModularity.Hypergeometric.EffectiveEulerRealization
public import HilbertModularity.RepresentationTheory.CompatibleSystemTwist
public import HilbertModularity.Hypergeometric.ChosenEulerIrreducibility

/-! # The effective Euler compatible system at every coprime conductor

One κ_N^m character is defined over the cyclotomic coefficient field before
all its completions. Twisting the actual raw quotient system by this character
constructs the effective system of [TripathiGoswamiRevised, Proposition 2.5].
The comparison with the original arithmetic fibres is proved explicitly.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

/-- Extend the single rational κ_N^m character to the system's cyclotomic
coefficient field. Its ramification set is retained; no local characters are
chosen independently and no new literature input is used. -/
def chosenGprvKappaCoefficientCharacter
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (m : ℕ) :
    FiniteAlgebraicGaloisCharacter (realCyclotomicField N) (cyclotomicField N) where
  toMonoidHom := gprvKappaLocal N h3 m (cyclotomicField N)
  finite_range := finite_gprvKappaLocal N h3 m (cyclotomicField N)
  local_continuous := by
    intro w
    have hc := ((chosenGprvKappaRealCharacter N h3).isLocallyConstant.comp
      (fun u : ℚˣ => (algebraMap ℚ (w.adicCompletion (cyclotomicField N)) (u : ℚ)) ^ m)
      ).continuous
    convert hc using 1
    funext g
    change algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))
      (gprvKappaLocal N h3 m (cyclotomicField N) g : cyclotomicField N) = _
    rw [gprvKappaLocal_coe, map_pow]
    congr 1
  bad := (chosenGprvKappaRealCharacter N h3).bad
  bad_finite := (chosenGprvKappaRealCharacter N h3).bad_finite
  unramified := by
    intro q hq P _ hP Q _ _ g hg
    have h := (chosenGprvKappaRealCharacter N h3).unramified q hq P hP Q g hg
    apply Units.ext
    rw [gprvKappaLocal_coe, h]
    simp only [Units.val_one, map_one, one_pow]

/-- Every local realization of the coefficient character is exactly the κ
factor already used in the selected effective Euler action. -/
theorem chosenGprvKappaCoefficientCharacter_local
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (m : ℕ)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    (chosenGprvKappaCoefficientCharacter N h3 m).local w =
      gprvKappaLocal N h3 m (w.adicCompletion (cyclotomicField N)) := by
  rw [FiniteAlgebraicGaloisCharacter.local_eq_composition]
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))
      (gprvKappaLocal N h3 m (cyclotomicField N) g : cyclotomicField N) =
    (gprvKappaLocal N h3 m (w.adicCompletion (cyclotomicField N)) g :
      w.adicCompletion (cyclotomicField N))
  rw [gprvKappaLocal_coe, gprvKappaLocal_coe, map_pow]
  congr 1

variable (N m : ℕ) [NeZero N]
  (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField N))

local instance effectiveEulerCompletionNorm (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField N)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField N))
    (WithZero (Multiplicative ℤ))

local instance effectiveEulerCoefficientPrime (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
  NumberField.primeBelow_prime (cyclotomicField N) w

/-- One semisimple compatible system whose local members are the actual
chosen effective Euler realizations, over the stated cyclotomic coefficient
field and with a coefficient-independent finite exceptional set. -/
def chosenEffectiveEulerCompatibleSystem :
    NumberFieldCompatibleSystem (realCyclotomicField N) (cyclotomicField N) :=
  (chosenCoprimeRawEulerCompatibleSystem N m h3 hm hmN hcop ξ).characterTwist
    (chosenGprvKappaCoefficientCharacter N h3 m)

/-- The completion action uses the original raw action and the fixed κ value. -/
theorem chosenEffectiveEulerCompatibleSystem_action
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    (chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).action w =
      (commonEulerCompletionAction N m (chosenCoprimeEulerFamily N m h3 hm hmN hcop)
        (chosenCoprimeRawEulerRealization N m h3 hm hmN hcop) ξ w).characterTwist
          (gprvKappaLocal N h3 m (w.adicCompletion (cyclotomicField N))) := by
  rw [chosenEffectiveEulerCompatibleSystem,
    NumberFieldCompatibleSystem.characterTwist_action,
    chosenCoprimeRawEulerCompatibleSystem_action,
    chosenGprvKappaCoefficientCharacter_local]

/-- The finite exceptional set is the union of the raw parameter/conductor
set and the selected global κ certificate; it is independent of the place. -/
theorem chosenEffectiveEulerCompatibleSystem_bad :
    (chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).bad =
      commonEulerBadPrimes N ξ ∪ (chosenGprvKappaRealCharacter N h3).bad := by
  rw [chosenEffectiveEulerCompatibleSystem,
    NumberFieldCompatibleSystem.characterTwist_bad,
    chosenCoprimeRawEulerCompatibleSystem_bad]
  rfl

/-- The system realizes the same selected quotient action at every coefficient
place, not an independently chosen isomorphic family or a relabelled factor. -/
def chosenEffectiveEulerCompatibleSystem_actionEquiv
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    ((chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).action w).Equiv
      (chosenEffectiveEulerAction N m (NumberField.primeBelow (cyclotomicField N) w)
        h3 hm hmN hcop (w.adicCompletion (cyclotomicField N))
        (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) ξ) := by
  rw [chosenEffectiveEulerCompatibleSystem_action]
  have e := commonEulerCompletionActionEquiv N m
    (chosenCoprimeEulerFamily N m h3 hm hmN hcop)
    (chosenCoprimeRawEulerRealization N m h3 hm hmN hcop) ξ w
  rw [commonEulerCompletionDescent_eq_placeDescent] at e
  refine .mk e.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  change e ((gprvKappaLocal N h3 m (w.adicCompletion (cyclotomicField N)) g :
      w.adicCompletion (cyclotomicField N)) • _) =
    chosenEffectiveEulerAction N m (NumberField.primeBelow (cyclotomicField N) w)
      h3 hm hmN hcop (w.adicCompletion (cyclotomicField N))
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) ξ g (e v)
  rw [map_smul, chosenEffectiveEulerAction_apply]
  congr 1
  exact congrArg (fun f => f v) (e.isIntertwining' g)

/-- The effective completion action is irreducible at every coefficient
place, by the all-coprime GPRV input and invariance under a scalar twist. -/
theorem chosenEffectiveEulerCompatibleSystem_isIrreducible
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    ((chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).action w
      ).IsIrreducible := by
  rw [chosenEffectiveEulerCompatibleSystem_action]
  apply (OrderIso.isSimpleOrder_iff
    (Representation.characterTwistSubrepresentationEquiv _ _)).mp
  exact commonEulerCompletionAction_isIrreducible_of_coprime N m h3 hm hmN hcop
    (chosenCoprimeEulerFamily N m h3 hm hmN hcop)
    (chosenCoprimeRawEulerRealization N m h3 hm hmN hcop) ξ w

/-- Irreducibility concerns the original effective arithmetic fibre itself,
not just the coordinate representation used by the compatible system. -/
theorem chosenEffectiveEulerAction_isIrreducible_at_completion
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    (chosenEffectiveEulerAction N m (NumberField.primeBelow (cyclotomicField N) w)
      h3 hm hmN hcop (w.adicCompletion (cyclotomicField N))
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) ξ
      ).IsIrreducible :=
  Representation.isIrreducible_equiv
    (chosenEffectiveEulerCompatibleSystem_actionEquiv N m h3 hm hmN hcop ξ w)
    (chosenEffectiveEulerCompatibleSystem_isIrreducible N m h3 hm hmN hcop ξ w)

end HilbertModularity.Hypergeometric
