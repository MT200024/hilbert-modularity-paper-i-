/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveComplexCharacters
public import HilbertModularity.Hypergeometric.GaloisDescent
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! # The fixed real coefficient label in the complex worked example

The same cyclotomic embedding that orients the positive power-residue
character sends the first real trace parameter to the manuscript's positive
square-root embedding of the real coefficient field.
-/

public noncomputable section

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

local instance coefficientEmbeddingFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The actual positive-square-root complex embedding of the real
fifth-cyclotomic coefficient field, induced by the oriented full embedding. -/
def primeFiveRealComplexEmbedding : realCyclotomicField 5 →+* ℂ :=
  primeFiveComplexEmbedding.comp (realEulerCoefficientInclusion 5)

/-- The fixed label τ₅,₁=ζ₅+ζ₅⁻¹ maps to (√5−1)/2 under the *same*
complex embedding used for the oriented finite characters. -/
theorem primeFiveComplexEmbedding_tau :
    primeFiveComplexEmbedding (realEulerCoefficientInclusion 5 (tau 5 1)) =
      ((Real.sqrt 5 : ℂ) - 1) / 2 := by
  rw [realEulerCoefficientInclusion_tau]
  simp only [pow_one, map_add, map_inv₀, primeFiveComplexEmbedding_root]
  have hi : fifthRoot ^ 4 = fifthRoot⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact fifthRoot_isPrimitiveRoot.pow_eq_one
  rw [← hi]
  exact fifthRoot_add_fourth_pow

@[simp] theorem primeFiveRealComplexEmbedding_tau :
    primeFiveRealComplexEmbedding (tau 5 1) = ((Real.sqrt 5 : ℂ) - 1) / 2 :=
  primeFiveComplexEmbedding_tau

/-- The fixed real trace parameter satisfies the actual fifth-cyclotomic
quadratic relation, with the sign pinned by the oriented complex embedding. -/
theorem primeFive_tau_quadratic :
    (tau 5 1) ^ 2 + tau 5 1 = (1 : realCyclotomicField 5) := by
  apply primeFiveRealComplexEmbedding.injective
  simp only [map_add, map_pow, map_one, primeFiveRealComplexEmbedding_tau]
  have hs : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  linear_combination (1 / 4 : ℂ) * hs

/-- The same quadratic relation after inclusion in the full cyclotomic
coefficient field. -/
theorem primeFive_fullTau_quadratic :
    (realEulerCoefficientInclusion 5 (tau 5 1)) ^ 2 +
      realEulerCoefficientInclusion 5 (tau 5 1) = (1 : cyclotomicField 5) := by
  exact (by simpa only [map_add, map_pow, map_one] using
    congrArg (realEulerCoefficientInclusion 5) primeFive_tau_quadratic)

/-- Every number field containing the fixed full cyclotomic coefficient field
has a complex embedding extending the exact positive-root embedding used by
the worked characters and Euler sums. -/
theorem exists_primeFiveComplexEmbedding_extension
    (E : Type*) [Field E] [NumberField E]
    (i : cyclotomicField 5 →+* E) :
    ∃ c : E →+* ℂ, c.comp i = primeFiveComplexEmbedding := by
  let : Algebra (cyclotomicField 5) E := i.toAlgebra
  let : Algebra.IsAlgebraic (cyclotomicField 5) E :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (L := cyclotomicField 5) (A := E)
  exact ⟨NumberField.ComplexEmbedding.lift E primeFiveComplexEmbedding,
    NumberField.ComplexEmbedding.lift_comp_algebraMap E primeFiveComplexEmbedding⟩

end HilbertModularity.Examples
