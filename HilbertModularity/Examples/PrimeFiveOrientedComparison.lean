/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveComplexCharacters
public import HilbertModularity.Examples.PrimeFiveComparison

/-! # Fixed labels in the actual oriented level-five example

The direct finite sums use the positive power-residue character at the chosen
cyclotomic prime. Given the same labelled arithmetic comparison and the
unordered RM trace pair, the real-root-of-unity argument identifies the
label and the value of its finite comparison character.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

attribute [local instance] Ideal.Quotient.field
local instance orientedComparisonFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance orientedComparisonElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance orientedComparisonFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- For the actual oriented character at eleven, the comparison selects the
fixed positive-square-root RM label and gives finite factor one. -/
theorem primeFive_orientedComparison_11
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1)
    {G : Type*} [Group G] (ν : G →* ℂˣ) (hν : (Set.range ν).Finite)
    (g : G) (t : ℂ)
    (ht : t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∨
      t = (-1 - (Real.sqrt 5 : ℂ)) / 2)
    (hcomparison : Hypergeometric.rankTwoMcCarthySum θ
      (primeFiveComplexCharacter11 P hP e primeFiveComplexEmbedding) 125 =
        (ν g : ℂ) * t) :
    t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧ ν g = 1 :=
  finite_comparison_character_11 ν hν g _
    (primeFiveComplexCharacter11_generator P hP e he _ primeFiveComplexEmbedding_root)
    θ hθ t ht hcomparison

/-- The same fixed-label comparison at forty-one selects the negative-root
trace and forces the finite character to one. -/
theorem primeFive_orientedComparison_41
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1)
    {G : Type*} [Group G] (ν : G →* ℂˣ) (hν : (Set.range ν).Finite)
    (g : G) (t : ℂ)
    (ht : t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∨
      t = (-1 + 5 * (Real.sqrt 5 : ℂ)) / 2)
    (hcomparison : Hypergeometric.rankTwoMcCarthySum θ
      (primeFiveComplexCharacter41 P hP e primeFiveComplexEmbedding) 125 =
        (ν g : ℂ) * t) :
    t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧ ν g = 1 :=
  finite_comparison_character_41 ν hν g _
    (primeFiveComplexCharacter41_generator P hP e he _ primeFiveComplexEmbedding_root)
    θ hθ t ht hcomparison

end HilbertModularity.Examples
