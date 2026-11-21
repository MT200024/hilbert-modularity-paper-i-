/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteCharacterFrobenius

/-! # Twisting a compatible system by one finite algebraic character

The character's algebraic Frobenius value is fixed before any coefficient place
is chosen. The resulting system retains the exact local twist and has the union
of the two original bad sets. This is the system construction used in
[TripathiGoswamiRevised, Theorem `RMgeneral` and Lemma `promotion`].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.NumberFieldCompatibleSystem

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- The actual rank-two character twist over all completions of one number field. -/
def characterTwist (S : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E) : NumberFieldCompatibleSystem F E where
  residueCharacteristic := S.residueCharacteristic
  residueCharacteristic_prime := S.residueCharacteristic_prime
  coefficientPrime := S.coefficientPrime
  action := fun w => (S.action w).characterTwist (χ.local w)
  continuous := S.characterTwist_continuous χ
  semisimple := S.characterTwist_semisimple χ
  bad := S.bad ∪ χ.bad
  bad_finite := S.bad_finite.union χ.bad_finite
  polynomial := fun q => (S.polynomial q).scaleRoots (χ.frobeniusValue q : E)
  unramified := by
    intro w q hq P _ hP hp Q _ _ g hg
    have h : q ∉ S.bad ∧ q ∉ χ.bad := by simpa only [Set.mem_union, not_or] using hq
    exact S.characterTwist_unramified χ w q h.1 h.2 P hP hp Q g hg
  frobenius_charpoly := by
    intro w q hq P _ hP hp Q _ _
    subst P
    have h : q ∉ S.bad ∧ q ∉ χ.bad := by simpa only [Set.mem_union, not_or] using hq
    have htw := S.not_mem_twistBadAt_of_good χ w q h.1 h.2 hp
    rw [χ.frobeniusValue_eq q h.2 Q]
    exact S.characterTwist_frobenius_charpoly χ w q htw q.asIdeal rfl Q

/-- The system uses the scalar twist of the original action, in the same coordinates. -/
theorem characterTwist_action (S : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E) (w : HeightOneSpectrum (𝓞 E)) :
    (S.characterTwist χ).action w = (S.action w).characterTwist (χ.local w) := (rfl)

/-- No exceptional primes other than the two supplied bad sets are added. -/
theorem characterTwist_bad (S : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E) :
    (S.characterTwist χ).bad = S.bad ∪ χ.bad := (rfl)

/-- The common polynomial is obtained by multiplying its roots by the character value. -/
theorem characterTwist_polynomial (S : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E) (q : HeightOneSpectrum (𝓞 F)) :
    (S.characterTwist χ).polynomial q =
      (S.polynomial q).scaleRoots (χ.frobeniusValue q : E) := (rfl)

/-- The manuscript's precise good-prime condition is preserved when each input
bad set is contained in its canonical excluded set. -/
theorem characterTwist_bad_subset (S : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E) (T : Set (HeightOneSpectrum (𝓞 F)))
    (hS : S.bad ⊆ T) (hχ : χ.bad ⊆ T) :
    (S.characterTwist χ).bad ⊆ T := by
  rw [characterTwist_bad]
  exact Set.union_subset hS hχ

end HilbertModularity.NumberFieldCompatibleSystem
