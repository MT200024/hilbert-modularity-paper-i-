/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.NumberFieldCompatibleSystem
public import HilbertModularity.NumberTheory.ResidualRigidity

/-! # Finite exceptional sets for coefficient places

At a fixed coefficient place, the geometric primes above its residue
characteristic form a finite set. We combine this set with the common finite
ramification set of a compatible system. This makes the finite exclusions in
the Frobenius comparison of [TripathiGoswami, Lemma “Promotion from one
realization”] explicit.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- Geometric primes whose residue characteristic agrees with the selected
coefficient characteristic. -/
def NumberFieldCompatibleSystem.coefficientExceptional
    (ρ : NumberFieldCompatibleSystem F E) (w : HeightOneSpectrum (𝓞 E)) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  {q | (ρ.residueCharacteristic w : 𝓞 F) ∈ q.asIdeal}

/-- Only finitely many geometric primes lie above a fixed nonzero coefficient
characteristic. -/
theorem NumberFieldCompatibleSystem.coefficientExceptional_finite
    (ρ : NumberFieldCompatibleSystem F E) (w : HeightOneSpectrum (𝓞 E)) :
    (ρ.coefficientExceptional w).Finite := by
  apply HeightOneSpectrum.finite_primes_containing
  exact_mod_cast (ρ.residueCharacteristic_prime w).ne_zero

/-- The common bad set together with the coefficient-characteristic primes. -/
def NumberFieldCompatibleSystem.badAt
    (ρ : NumberFieldCompatibleSystem F E) (w : HeightOneSpectrum (𝓞 E)) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  ρ.bad ∪ ρ.coefficientExceptional w

theorem NumberFieldCompatibleSystem.badAt_finite
    (ρ : NumberFieldCompatibleSystem F E) (w : HeightOneSpectrum (𝓞 E)) :
    (ρ.badAt w).Finite :=
  ρ.bad_finite.union (ρ.coefficientExceptional_finite w)

/-- A prime outside the place-specific bad set is unramified for the system
and has residue characteristic different from the coefficient place. -/
theorem NumberFieldCompatibleSystem.good_of_not_mem_badAt
    (ρ : NumberFieldCompatibleSystem F E) (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ ρ.badAt w) :
    q ∉ ρ.bad ∧ (ρ.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal := by
  simpa only [NumberFieldCompatibleSystem.badAt,
    NumberFieldCompatibleSystem.coefficientExceptional,
    Set.mem_union, Set.mem_ofPred_eq, not_or] using hq

/-- The two good-prime hypotheses exclude the place-specific bad set. -/
theorem NumberFieldCompatibleSystem.not_mem_badAt_of_good
    (ρ : NumberFieldCompatibleSystem F E) (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ ρ.bad)
    (hp : (ρ.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal) :
    q ∉ ρ.badAt w := by
  simpa only [NumberFieldCompatibleSystem.badAt,
    NumberFieldCompatibleSystem.coefficientExceptional,
    Set.mem_union, Set.mem_ofPred_eq, not_or] using And.intro hq hp

/-- One finite geometric set suffices for both systems at both coefficient
places in a one-place promotion argument. -/
def NumberFieldCompatibleSystem.comparisonBad
    (ρ σ : NumberFieldCompatibleSystem F E)
    (w₀ w : HeightOneSpectrum (𝓞 E)) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  ρ.badAt w₀ ∪ σ.badAt w₀ ∪ ρ.badAt w ∪ σ.badAt w

theorem NumberFieldCompatibleSystem.comparisonBad_finite
    (ρ σ : NumberFieldCompatibleSystem F E)
    (w₀ w : HeightOneSpectrum (𝓞 E)) :
    (ρ.comparisonBad σ w₀ w).Finite :=
  (((ρ.badAt_finite w₀).union (σ.badAt_finite w₀)).union
    (ρ.badAt_finite w)).union (σ.badAt_finite w)

/-- The complement of the joint finite set supplies all four unramified and
all four residue-characteristic hypotheses. -/
theorem NumberFieldCompatibleSystem.good_of_not_mem_comparisonBad
    (ρ σ : NumberFieldCompatibleSystem F E)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.comparisonBad σ w₀ w) :
    q ∉ ρ.bad ∧ q ∉ σ.bad ∧
      (ρ.residueCharacteristic w₀ : 𝓞 F) ∉ q.asIdeal ∧
      (σ.residueCharacteristic w₀ : 𝓞 F) ∉ q.asIdeal ∧
      (ρ.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal ∧
      (σ.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal := by
  simp only [NumberFieldCompatibleSystem.comparisonBad,
    NumberFieldCompatibleSystem.badAt,
    NumberFieldCompatibleSystem.coefficientExceptional,
    Set.mem_union, not_or] at hq
  tauto

end HilbertModularity
