/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveCoefficientEmbedding
public import HilbertModularity.Examples.PrimeFiveFrobenius
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! # Algebraic RM trace candidates from the worked polynomials

The fifth-cyclotomic trace parameter has quadratic relation `s²+s=1`.
Consequently the determinant-q RM factors of the actual genus-two polynomial
have traces in the image of that fixed coefficient field, before any
complex or p-adic embedding is chosen.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

local instance algebraicRootsFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Over any characteristic-zero coefficient field, the eleven-prime
factorization has the two traces `s` and `-1-s`, where `s²+s=1`. -/
theorem unorderedTracePair11_of_quadraticParameter
    {L : Type*} [Field L] [CharZero L]
    (s a b : L) (hs : s ^ 2 + s = 1)
    (hpoly : (1 - C a * X + 11 * X ^ 2) *
      (1 - C b * X + 11 * X ^ 2) =
        (1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 : L[X])) :
    (a = s ∧ b = -1 - s) ∨ (a = -1 - s ∧ b = s) := by
  have hpoly' : (1 - C (a + b) * X + C (a * b + 22) * X ^ 2 -
      C (11 * (a + b)) * X ^ 3 + 121 * X ^ 4 : L[X]) =
        1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 := by
    calc
      _ = (1 - C a * X + 11 * X ^ 2) *
          (1 - C b * X + 11 * X ^ 2) := by
        simp only [map_add, map_mul, map_ofNat]
        ring
      _ = _ := hpoly
  have h1 := congrArg (fun p : L[X] => p.coeff 1) hpoly'
  have h2 := congrArg (fun p : L[X] => p.coeff 2) hpoly'
  simp only [coeff_add,
    coeff_sub,
    coeff_C_mul_X_pow,
    coeff_C_mul_X,
    coeff_X,
    coeff_one] at h1 h2
  norm_num at h1 h2
  have hsum : a + b = -1 := by linear_combination -h1
  have hprod : a * b = -1 := by linear_combination h2
  apply unordered_pair_of_sum_product
  · linear_combination hsum
  · linear_combination hprod + hs

/-- At forty-one the two traces are `-3-5s` and `2+5s` in every
characteristic-zero realization of the same real coefficient field. -/
theorem unorderedTracePair41_of_quadraticParameter
    {L : Type*} [Field L] [CharZero L]
    (s a b : L) (hs : s ^ 2 + s = 1)
    (hpoly : (1 - C a * X + 41 * X ^ 2) *
      (1 - C b * X + 41 * X ^ 2) =
        (1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 : L[X])) :
    (a = -3 - 5 * s ∧ b = 2 + 5 * s) ∨
      (a = 2 + 5 * s ∧ b = -3 - 5 * s) := by
  have hpoly' : (1 - C (a + b) * X + C (a * b + 82) * X ^ 2 -
      C (41 * (a + b)) * X ^ 3 + 1681 * X ^ 4 : L[X]) =
        1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 := by
    calc
      _ = (1 - C a * X + 41 * X ^ 2) *
          (1 - C b * X + 41 * X ^ 2) := by
        simp only [map_add, map_mul, map_ofNat]
        ring
      _ = _ := hpoly
  have h1 := congrArg (fun p : L[X] => p.coeff 1) hpoly'
  have h2 := congrArg (fun p : L[X] => p.coeff 2) hpoly'
  simp only [coeff_add,
    coeff_sub,
    coeff_C_mul_X_pow,
    coeff_C_mul_X,
    coeff_X,
    coeff_one] at h1 h2
  norm_num at h1 h2
  have hsum : a + b = -1 := by linear_combination -h1
  have hprod : a * b = -31 := by linear_combination h2
  apply unordered_pair_of_sum_product
  · linear_combination hsum
  · linear_combination hprod + 25 * hs

/-- An actual rank-two factor of the eleven-prime polynomial has a trace
represented in the common algebraic coefficient field. The fixed complex
embedding sends it to one of the two manuscript roots; no label is selected
by this result. -/
theorem exists_primeFive_algebraicTrace_11_of_factorization
    (L : Type*) [Field L] [CharZero L] [Algebra (cyclotomicField 5) L]
    (E' : IntermediateField (cyclotomicField 5) L)
    (ι : cyclotomicField 5 →+* L)
    (hι : E'.subtype.comp (algebraMap (cyclotomicField 5) E') = ι)
    (c : E' →+* ℂ)
    (hc : c.comp (algebraMap (cyclotomicField 5) E') = primeFiveComplexEmbedding)
    (a b : L)
    (hpoly : (1 - C a * X + 11 * X ^ 2) *
      (1 - C b * X + 11 * X ^ 2) =
        (1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 : L[X])) :
    ∃ t : E', E'.subtype t = a ∧
      (c t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∨
        c t = (-1 - (Real.sqrt 5 : ℂ)) / 2) := by
  let τF := realEulerCoefficientInclusion 5 (tau 5 1)
  let sE : E' := algebraMap (cyclotomicField 5) E' τF
  let sL : L := ι τF
  have hsL : sL ^ 2 + sL = 1 := by
    have h := congrArg ι primeFive_fullTau_quadratic
    simpa only [map_add, map_pow, map_one, sL, τF] using h
  have hsE : E'.subtype sE = sL := by
    have h := congrArg (fun f : cyclotomicField 5 →+* L => f τF) hι
    exact h
  have hcE : c sE = ((Real.sqrt 5 : ℂ) - 1) / 2 := by
    have h := congrArg (fun f : cyclotomicField 5 →+* ℂ => f τF) hc
    exact h.trans primeFiveComplexEmbedding_tau
  rcases unorderedTracePair11_of_quadraticParameter sL a b hsL hpoly with
    ⟨ha, _⟩ | ⟨ha, _⟩
  · exact ⟨sE, hsE.trans ha.symm, Or.inl hcE⟩
  · refine ⟨-1 - sE, ?_, Or.inr ?_⟩
    · change (-1 - (sE : L)) = a
      have hsE' : (sE : L) = sL := hsE
      rw [hsE']
      exact ha.symm
    · rw [map_sub, map_neg, map_one, hcE]
      ring

/-- The forty-one-prime factorization likewise places the fixed factor's
trace in the same algebraic coefficient field, with exactly the two
complex conjugate values from the manuscript. -/
theorem exists_primeFive_algebraicTrace_41_of_factorization
    (L : Type*) [Field L] [CharZero L] [Algebra (cyclotomicField 5) L]
    (E' : IntermediateField (cyclotomicField 5) L)
    (ι : cyclotomicField 5 →+* L)
    (hι : E'.subtype.comp (algebraMap (cyclotomicField 5) E') = ι)
    (c : E' →+* ℂ)
    (hc : c.comp (algebraMap (cyclotomicField 5) E') = primeFiveComplexEmbedding)
    (a b : L)
    (hpoly : (1 - C a * X + 41 * X ^ 2) *
      (1 - C b * X + 41 * X ^ 2) =
        (1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 : L[X])) :
    ∃ t : E', E'.subtype t = a ∧
      (c t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∨
        c t = (-1 + 5 * (Real.sqrt 5 : ℂ)) / 2) := by
  let τF := realEulerCoefficientInclusion 5 (tau 5 1)
  let sE : E' := algebraMap (cyclotomicField 5) E' τF
  let sL : L := ι τF
  have hsL : sL ^ 2 + sL = 1 := by
    have h := congrArg ι primeFive_fullTau_quadratic
    simpa only [map_add, map_pow, map_one, sL, τF] using h
  have hsE : (sE : L) = sL := by
    have h := congrArg (fun f : cyclotomicField 5 →+* L => f τF) hι
    exact h
  have hcE : c sE = ((Real.sqrt 5 : ℂ) - 1) / 2 := by
    have h := congrArg (fun f : cyclotomicField 5 →+* ℂ => f τF) hc
    exact h.trans primeFiveComplexEmbedding_tau
  have hc5 : c (5 : E') = (5 : ℂ) := map_ofNat c 5
  have hc2 : c (2 : E') = (2 : ℂ) := map_ofNat c 2
  have hcneg3 : c (-3 : E') = (-3 : ℂ) := by
    simp only [map_neg, map_ofNat]
  rcases unorderedTracePair41_of_quadraticParameter sL a b hsL hpoly with
    ⟨ha, _⟩ | ⟨ha, _⟩
  · refine ⟨-3 - 5 * sE, ?_, Or.inl ?_⟩
    · change (-3 - 5 * (sE : L)) = a
      rw [hsE]
      exact ha.symm
    · rw [map_sub, map_mul, hcneg3, hc5, hcE]
      ring
  · refine ⟨2 + 5 * sE, ?_, Or.inr ?_⟩
    · change (2 + 5 * (sE : L)) = a
      rw [hsE]
      exact ha.symm
    · rw [map_add, map_mul, hc2, hc5, hcE]
      ring

end HilbertModularity.Examples
