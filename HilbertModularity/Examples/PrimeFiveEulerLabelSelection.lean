/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveEulerTransport
public import HilbertModularity.Examples.PrimeFivePolynomialFactorization

/-! # Fixed-label selection from Euler traces and RM factorization

The actual oriented finite Euler scalar compares to one fixed RM factor.
The numeric genus-two polynomial determines both possible factor traces;
the finite real-root-of-unity argument then selects the same label and makes
the comparison character trivial at the worked prime.
-/

public noncomputable section

open IsDedekindDomain Polynomial
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

attribute [local instance] Ideal.Quotient.field
local instance labelSelectionFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance labelSelectionElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance labelSelectionFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The oriented Euler comparison at eleven fixes the first RM factor trace
and forces the finite comparison value to one. The factorization and actual
arithmetic comparison remain explicit mathematical prerequisites. -/
theorem primeFive_orientedEulerSelectsLabel_11
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1)
    {G : Type*} [Group G] (ν : G →* ℂˣ) (hν : (Set.range ν).Finite)
    (g : G) (a b : ℂ)
    (hpoly : (1 - C a * X + 11 * X ^ 2) *
      (1 - C b * X + 11 * X ^ 2) =
        (1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 : ℂ[X]))
    (hcomparison : primeFiveComplexEmbedding
      (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) = (ν g : ℂ) * a) :
    a = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧ ν g = 1 := by
  have hpair := unorderedTracePair_of_localPolynomial_11 a b hpoly
  have ht : a = ((Real.sqrt 5 : ℂ) - 1) / 2 ∨
      a = (-1 - (Real.sqrt 5 : ℂ)) / 2 :=
    hpair.imp And.left And.left
  have hsum : rankTwoMcCarthySum θ
      (primeFiveComplexCharacter11 P hP e primeFiveComplexEmbedding) 125 =
        (ν g : ℂ) * a :=
    (primeFive_orientedMcCarthy_eq_normalizedEuler_11 P hP e he θ hθ).trans hcomparison
  exact finite_comparison_character_11 ν hν g _
    (primeFiveComplexCharacter11_generator P hP e he _ primeFiveComplexEmbedding_root)
    θ hθ a ht hsum

/-- At forty-one, the same actual Euler normalization selects the negative
square-root RM trace and trivial finite comparison value. -/
theorem primeFive_orientedEulerSelectsLabel_41
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1)
    {G : Type*} [Group G] (ν : G →* ℂˣ) (hν : (Set.range ν).Finite)
    (g : G) (a b : ℂ)
    (hpoly : (1 - C a * X + 41 * X ^ 2) *
      (1 - C b * X + 41 * X ^ 2) =
        (1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 : ℂ[X]))
    (hcomparison : primeFiveComplexEmbedding
      (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) = (ν g : ℂ) * a) :
    a = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧ ν g = 1 := by
  have hpair := unorderedTracePair_of_localPolynomial_41 a b hpoly
  have ht : a = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∨
      a = (-1 + 5 * (Real.sqrt 5 : ℂ)) / 2 :=
    hpair.imp And.left And.left
  have hsum : rankTwoMcCarthySum θ
      (primeFiveComplexCharacter41 P hP e primeFiveComplexEmbedding) 125 =
        (ν g : ℂ) * a :=
    (primeFive_orientedMcCarthy_eq_normalizedEuler_41 P hP e he θ hθ).trans hcomparison
  exact finite_comparison_character_41 ν hν g _
    (primeFiveComplexCharacter41_generator P hP e he _ primeFiveComplexEmbedding_root)
    θ hθ a ht hsum

end HilbertModularity.Examples
