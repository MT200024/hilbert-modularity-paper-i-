/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveComplexCharacters
public import HilbertModularity.Hypergeometric.FrobeniusComparison

/-! # Transport of the level-five Euler scalar to the direct complex sum

The positive power-residue character is transported across the actual
residue-field equivalence and fixed complex embedding. Euler's finite sum
therefore has exactly the same normalization as the direct McCarthy sum.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

attribute [local instance] Ideal.Quotient.field
local instance eulerTransportFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance eulerTransportElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance eulerTransportFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- A field equivalence and a pointwise character transport identify the
rank-two McCarthy sum with the positive-power Euler curve sum at exponent one.
The character value at minus one remains explicit. -/
theorem rankTwoMcCarthySum_eq_transportedEulerFive
    (q : ℕ) [Fact q.Prime]
    (k : Type*) [Field k] [Fintype k]
    (e : k ≃+* ZMod q)
    (χ : MulChar k (cyclotomicField 5))
    (ι : cyclotomicField 5 →+* ℂ)
    (A : MulChar (ZMod q) ℂ)
    (hA : ∀ x, A x = ι (χ (e.symm x)))
    (horder : orderOf A = 5)
    (θ : AddChar (ZMod q) ℂ) (hθ : θ ≠ 1)
    (x : ZMod q) (hx : x ≠ 0) :
    rankTwoMcCarthySum θ A x =
      -ι (χ (-1)) *
        ∑ y : k, ι (χ (y * (1 - y) ^ 4 * (1 - e.symm x * y))) := by
  classical
  have hnontrivial : A ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    omega
  have hpow : A ^ 5 = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one A
  have heuler : eulerCharacterSum A x =
      ∑ y : k, ι (χ (y * (1 - y) ^ 4 * (1 - e.symm x * y))) := by
    have h := eulerCharacterSum_pow_eq A 5 1 (by decide) (by decide) hpow x
    simp only [pow_one, Nat.reduceSub] at h
    rw [h]
    rw [← Equiv.sum_comp e.symm.toEquiv
      (fun y : k => ι (χ (y * (1 - y) ^ 4 * (1 - e.symm x * y))))]
    apply Finset.sum_congr rfl
    intro y _
    rw [hA]
    congr 1
    simp
  rw [rankTwoMcCarthySum_eq_eulerCharacterSum A hnontrivial θ hθ x hx,
    heuler, hA]
  congr 1
  simp

/-- At the actual oriented prime above eleven, the direct complex McCarthy
sum equals the image of the normalized cyclotomic Euler scalar. -/
theorem primeFive_orientedMcCarthy_eq_normalizedEuler_11
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) :
    rankTwoMcCarthySum θ
      (primeFiveComplexCharacter11 P hP e primeFiveComplexEmbedding) 125 =
        primeFiveComplexEmbedding
          (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) := by
  let k := 𝓞 (cyclotomicField 5) ⧸ P
  let : Fintype k := Fintype.ofFinite k
  let A := primeFiveComplexCharacter11 P hP e primeFiveComplexEmbedding
  have h := rankTwoMcCarthySum_eq_transportedEulerFive 11 k e
    (cyclotomicPowerResidueMulChar 5 P hP) primeFiveComplexEmbedding A
    (primeFiveComplexCharacter11_apply P hP e primeFiveComplexEmbedding)
    (primeFiveComplexCharacter11_orderOf P hP e he) θ hθ 125 (by decide)
  calc
    rankTwoMcCarthySum θ A 125 =
        -primeFiveComplexEmbedding (cyclotomicPowerResidueMulChar 5 P hP (-1)) *
          ∑ y : k, primeFiveComplexEmbedding
            (cyclotomicPowerResidueMulChar 5 P hP
              (y * (1 - y) ^ 4 * (1 - e.symm 125 * y))) := h
    _ = primeFiveComplexEmbedding
          (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) := by
      rw [normalizedCyclotomicEulerTrace_map]
      simp only [pow_one, Nat.reduceSub]
      congr 1

/-- The same exact Euler/McCarthy scalar identity at the oriented prime
above forty-one. -/
theorem primeFive_orientedMcCarthy_eq_normalizedEuler_41
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) :
    rankTwoMcCarthySum θ
      (primeFiveComplexCharacter41 P hP e primeFiveComplexEmbedding) 125 =
        primeFiveComplexEmbedding
          (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) := by
  let k := 𝓞 (cyclotomicField 5) ⧸ P
  let : Fintype k := Fintype.ofFinite k
  let A := primeFiveComplexCharacter41 P hP e primeFiveComplexEmbedding
  have h := rankTwoMcCarthySum_eq_transportedEulerFive 41 k e
    (cyclotomicPowerResidueMulChar 5 P hP) primeFiveComplexEmbedding A
    (primeFiveComplexCharacter41_apply P hP e primeFiveComplexEmbedding)
    (primeFiveComplexCharacter41_orderOf P hP e he) θ hθ 125 (by decide)
  calc
    rankTwoMcCarthySum θ A 125 =
        -primeFiveComplexEmbedding (cyclotomicPowerResidueMulChar 5 P hP (-1)) *
          ∑ y : k, primeFiveComplexEmbedding
            (cyclotomicPowerResidueMulChar 5 P hP
              (y * (1 - y) ^ 4 * (1 - e.symm 125 * y))) := h
    _ = primeFiveComplexEmbedding
          (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) := by
      rw [normalizedCyclotomicEulerTrace_map]
      simp only [pow_one, Nat.reduceSub]
      congr 1

/-- The actual chosen cyclotomic Euler scalar at eleven has the direct
McCarthy value under the fixed complex embedding. -/
theorem primeFive_orientedEulerValue_11
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) :
    primeFiveComplexEmbedding
      (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) =
        ((Real.sqrt 5 : ℂ) - 1) / 2 :=
  (primeFive_orientedMcCarthy_eq_normalizedEuler_11 P hP e he θ hθ).symm.trans
    (primeFiveComplexCharacter11_mccarthyValue P hP e he θ hθ)

/-- The corresponding actual Euler scalar at forty-one has the second
computed value under the same complex embedding. -/
theorem primeFive_orientedEulerValue_41
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) :
    primeFiveComplexEmbedding
      (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) =
        (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 :=
  (primeFive_orientedMcCarthy_eq_normalizedEuler_41 P hP e he θ hθ).symm.trans
    (primeFiveComplexCharacter41_mccarthyValue P hP e he θ hθ)

end HilbertModularity.Examples
