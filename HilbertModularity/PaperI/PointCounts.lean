module
public import HilbertModularity.PaperI.PrimeNineteen
public import HilbertModularity.Examples.PrimeFiveCohomologicalPolynomial
public import HilbertModularity.Examples.PrimeFiveFrobenius
import Mathlib.Tactic.LinearCombination
public noncomputable section
namespace HilbertModularity.PaperI.Nineteen
open AlgebraicGeometry HilbertModularity.Hyperelliptic HilbertModularity.Examples Polynomial
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The two completed curves, with both rational points at infinity. -/
theorem projective_counts :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : ZMod 19))) = 25 ∧
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : K))) = 423 := by
  constructor
  · rw [primeFive_projective_card_euler (by rw [ringChar.eq (ZMod 19) 19]; decide), affine_counts.1]
  · rw [primeFive_projective_card_euler (by rw [ringChar.eq K 19]; decide), affine_counts.2]

/-- The reciprocal Frobenius polynomial on the actual geometric first cohomology. -/
theorem geometricFrobeniusPolynomial_19 :
    ∃ b : Module.Basis (Fin 4) ℚ_[7] (primeFiveGeometricH1 (ZMod 19)),
      (LinearMap.toMatrix b b (AlgebraicGeometry.Hyperelliptic.genusTwoGeometricFrobeniusAction
        (ZMod 19) (primeFivePolynomial (ZMod 19)) (primeFivePolynomial_degree (ZMod 19)) 7)).charpolyRev =
        1 + 5 * X + 43 * X ^ 2 + 95 * X ^ 3 + 361 * X ^ 4 := by
  let f := primeFivePolynomial (ZMod 19)
  have hd : f.natDegree = 2 * 3 := primeFivePolynomial_degree (ZMod 19)
  have hd₂ : (f.map (algebraMap (ZMod 19) K)).natDegree = 2 * 3 := by
    simpa only [f, primeFivePolynomial_map] using primeFivePolynomial_degree K
  have h₁ : Nat.card (Scheme.RationalPoint (AlgebraicGeometry.Hyperelliptic.toSpec f 3 hd)) =
      25 := by
    have heq : f = plusPolynomial 5 (125 : ZMod 19) :=
      (plusPolynomial_five (ZMod 19)).symm
    exact (rationalPointCount_congr heq (by decide) hd
      (plusPolynomial_evenDegree 5 (by decide) (125 : ZMod 19))).trans
      projective_counts.1
  have h₂ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec
        (f.map (algebraMap (ZMod 19) K)) 3 hd₂)) = 423 := by
    have heq : f.map (algebraMap (ZMod 19) K) =
        plusPolynomial 5 (125 : K) := by
      simpa only [f, primeFivePolynomial_map] using
        (plusPolynomial_five K).symm
    exact (rationalPointCount_congr heq (by decide) hd₂
      (plusPolynomial_evenDegree 5 (by decide) (125 : K))).trans
      projective_counts.2
  obtain ⟨b, hb⟩ := AlgebraicGeometry.Hyperelliptic.genusTwoGeometricFrobeniusPolynomial
    (ZMod 19) f hd 7 (primeFivePolynomial_monic (ZMod 19))
    (primeFivePolynomial_separable (ZMod 19) (by decide) (by decide)
      (by decide) (by decide)) (by decide) (by decide) hd₂
    (by simpa [ZMod.card] using card_field)
  refine ⟨b, ?_⟩
  dsimp only at hb
  rw [h₁, h₂] at hb
  norm_num [primeFiveGeometricH1, f, ZMod.card] at hb ⊢
  exact hb

/-- The projective counts and the two quadratic determinants give the
unordered pair of RM traces. -/
theorem frobenius_trace_pair_19 (M N : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 19) (hN : N.det = 19)
    (h₁ : (Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : ZMod 19))) : ℂ)
      = 19 + 1 - (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : K))) : ℂ)
      = 19 ^ 2 + 1 - ((M ^ 2).trace + (N ^ 2).trace)) :
    (M.trace = ((-5 : ℂ) + Real.sqrt 5) / 2 ∧ N.trace = ((-5 : ℂ) - Real.sqrt 5) / 2) ∨
    (M.trace = ((-5 : ℂ) - Real.sqrt 5) / 2 ∧ N.trace = ((-5 : ℂ) + Real.sqrt 5) / 2) := by
  rw [projective_counts.1] at h₁
  rw [projective_counts.2] at h₂
  have hs : M.trace + N.trace = -5 := by linear_combination h₁
  have hm := two_mul_det_eq_sq_trace_sub_trace_sq M
  have hn := two_mul_det_eq_sq_trace_sub_trace_sq N
  rw [hM] at hm
  rw [hN] at hn
  have hsq : M.trace ^ 2 + N.trace ^ 2 = 15 := by linear_combination -hm - hn + h₂
  have hp : M.trace * N.trace = 5 := by
    linear_combination (1 / 2 : ℂ) * (M.trace + N.trace - 5) * hs - (1 / 2 : ℂ) * hsq
  have hr : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  apply unordered_complex_pair_of_sum_product
  · linear_combination hs
  · linear_combination hp + (1 / 4 : ℂ) * hr

end HilbertModularity.PaperI.Nineteen
