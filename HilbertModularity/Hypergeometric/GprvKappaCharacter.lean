/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisDescent
public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter
public import HilbertModularity.NumberTheory.Cyclotomic
public import HilbertModularity.Hypergeometric.FrobeniusComparison

/-! # The GPRV auxiliary cyclotomic character

The character κ_N is attached to F_N(ζ₂N)/F_N [GPRV, Definition 8.8],
then extended to the real field using Corollary 8.10 and Lemma 9.4. Its
restriction to F_N is specified by an actual fixing subgroup. Only the
real-field restriction is asserted to have square one; the global Dirichlet
extension need not itself be quadratic for high powers of two.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- Restrict an actual cyclotomic-field Galois automorphism to the real
field, then use the same closure identification as the chosen Euler descent. -/
def cyclotomicToRealEulerGaloisHom (N : ℕ) [NeZero N] :
    (Qbar ≃ₐ[cyclotomicField N] Qbar) →*
      AbsoluteGalois (realCyclotomicField N) :=
  (realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)

/-- This restriction is the same closure map used by the raw Euler trace
comparison. -/
theorem cyclotomicToRealEulerGaloisHom_apply
    (N : ℕ) [NeZero N]
    (g : Qbar ≃ₐ[cyclotomicField N] Qbar) :
    cyclotomicToRealEulerGaloisHom N g =
      realEulerClosureGaloisHom N (restrictCyclotomicGalois N g) := (rfl)

/-- One finite real-field extension of the character of
`F_N(ζ₂N)/F_N` [GPRV, Definition 8.8 and Corollary 8.10, p. 33;
Lemma 9.4, p. 40]. The displayed kernel is the exact action on the
cyclotomic extension, rather than an arbitrary quadratic character.
For odd N the extension is chosen trivial. For even N the source gives a
Dirichlet extension to `G_ℚ`, whose restriction to `G_{K_N}` has order at
most two; this interface records that restriction, not an assertion that
the global Dirichlet character is always quadratic or unique. Its finite
ramification is supported at primes dividing `2N`.

This is an existing-literature premise, with no Euler trace, RM comparison
or modularity assertion. -/
theorem exists_gprvKappaRealCharacter
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) :
    ∃ κ : FiniteAlgebraicGaloisCharacter (realCyclotomicField N) ℚ,
      (∀ g : AbsoluteGalois (realCyclotomicField N),
        κ.toMonoidHom g ^ 2 = 1) ∧
      (Odd N → κ.toMonoidHom = 1) ∧
      (∀ g : Qbar ≃ₐ[cyclotomicField N] Qbar,
        κ.toMonoidHom (cyclotomicToRealEulerGaloisHom N g) = 1 ↔
          (g.restrictScalars ℚ) ∈ (cyclotomicField (2 * N)).fixingSubgroup) ∧
      (∀ q : HeightOneSpectrum (𝓞 (realCyclotomicField N)),
        (2 * N : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal → q ∉ κ.bad) := by
  sorry

/-- Fix one source extension before choosing any Euler fibre or coefficient
place. -/
def chosenGprvKappaRealCharacter
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) :
    FiniteAlgebraicGaloisCharacter (realCyclotomicField N) ℚ :=
  Classical.choose (exists_gprvKappaRealCharacter N h3)

/-- The selected character has order dividing two on the actual real-field
Galois group, as in [GPRV, Lemma 9.4, p. 40]. -/
theorem chosenGprvKappaRealCharacter_sq
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (g : AbsoluteGalois (realCyclotomicField N)) :
    (chosenGprvKappaRealCharacter N h3).toMonoidHom g ^ 2 = 1 :=
  (Classical.choose_spec (exists_gprvKappaRealCharacter N h3)).1 g

/-- At odd conductor the selected κ is literally trivial, recovering the
previous checked odd realization. -/
theorem chosenGprvKappaRealCharacter_eq_one_of_odd
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N) (hOdd : Odd N) :
    (chosenGprvKappaRealCharacter N h3).toMonoidHom = 1 :=
  (Classical.choose_spec (exists_gprvKappaRealCharacter N h3)).2.1 hOdd

/-- The chosen character retains exactly the source cyclotomic-extension
restriction, including its chosen closure map. -/
theorem chosenGprvKappaRealCharacter_restriction
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (g : Qbar ≃ₐ[cyclotomicField N] Qbar) :
    (chosenGprvKappaRealCharacter N h3).toMonoidHom
        (cyclotomicToRealEulerGaloisHom N g) = 1 ↔
      (g.restrictScalars ℚ) ∈ (cyclotomicField (2 * N)).fixingSubgroup :=
  (Classical.choose_spec (exists_gprvKappaRealCharacter N h3)).2.2.1 g

/-- Away from the source conductor `2N`, the selected GPRV character
has no bad prime [GPRV, Definition 8.8 and Corollary 8.10, p. 33]. -/
theorem chosenGprvKappaRealCharacter_not_bad_of_away
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (h2N : (2 * N : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal) :
    q ∉ (chosenGprvKappaRealCharacter N h3).bad :=
  (Classical.choose_spec (exists_gprvKappaRealCharacter N h3)).2.2.2 q h2N

/-- [GPRV, Lemma 8.9, p. 33] identifies κ_N at a cyclotomic prime away
from 2N with the Nth power-residue character on -1. Geometric Frobenius
has the same value as arithmetic Frobenius because the real restriction
is quadratic [GPRV, Lemma 9.4, p. 40]. The character is the single one
selected from Corollary 8.10, and this statement concerns its restriction
to the actual cyclotomic Galois group. No Euler trace is assumed. -/
theorem chosenGprvKappaRealCharacter_geometricFrobenius
    (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hN : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (h2N : (2 * N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    algebraMap ℚ (cyclotomicField N)
        (((chosenGprvKappaRealCharacter N h3).toMonoidHom
          (cyclotomicToRealEulerGaloisHom N
            (absoluteGeometricFrobenius N P Q)) : ℚ)) =
      cyclotomicPowerResidueMulChar N P.asIdeal hN (-1) := by
  sorry

end HilbertModularity.Hypergeometric
