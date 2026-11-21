module

public import HilbertModularity.Hypergeometric.PrimeEulerMain
public import HilbertModularity.Hypergeometric.EulerSum
public import HilbertModularity.Hypergeometric.FiniteField
public import HilbertModularity.NumberTheory.CuspDepth
import Mathlib.Tactic.Ring

/-!
# Paper I (traditional introduction): checked alignment layer

This file aligns explicit conclusions of the revised manuscript with the
pre-existing formalization. It introduces no `sorry`, custom axioms, or
unproved comparison theorem.

It does **not** establish `cor:prime-exact-twist` (the identification of the
Euler/RM comparison character with the character of F_p/K_p). The earlier
formalization only gives a finite-order comparison character; see
MANUSCRIPT_ALIGNMENT.md for this outstanding obligation and the effect on
`thm:intro-RM-automorphy`.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

variable (p : ℕ) [Fact p.Prime]

/-- Revised `thm:intro-main`: deep-cusp modularity, in the existing formal
notion of `FiniteFieldHilbertModularAt`. This is a restatement of the
previously formalized valuation formulation; no exact-twist claim is used. -/
theorem revisedPaperI_deepCusp_modular
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ₀ : ProjectiveLine.Parameter ℚ)
    (hdeep : 3 ≤ padicValRat p ξ₀.val ∨ 3 ≤ padicValRat p (1 - ξ₀.val)) :
    FiniteFieldHilbertModularAt p m (darmonRationalParameter p ξ₀).val := by
  exact finiteFieldHilbertModularAt_of_deep_cusp p hp m hmPos hmLt ξ₀ hdeep

/-- The revised abstract and `thm:intro-main` use the cubic divisibility
criterion. The equivalence with valuation depth is formally supplied by
`Cusp.padicValRat_ge_three_iff` and
`Cusp.padicValRat_one_sub_ge_three_iff`. -/
theorem revisedPaperI_cubicDivisibility_modular
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A)) :
    FiniteFieldHilbertModularAt p m (darmonRationalParameter p ξ₀).val := by
  apply revisedPaperI_deepCusp_modular p hp m hmPos hmLt ξ₀
  rcases hdeep with hnum | hdiff
  · left
    rw [hξ]
    exact (Cusp.padicValRat_ge_three_iff hA hB hAB).2 hnum
  · right
    have hnotone : (A : ℚ) / B ≠ 1 := by
      intro heq
      apply ξ₀.property.2
      exact hξ.trans heq
    rw [hξ]
    exact (Cusp.padicValRat_one_sub_ge_three_iff hB hAB hnotone).2 hdiff

end HilbertModularity.Hypergeometric

namespace HilbertModularity.RevisedPaperI

/-- Distinguishes the trace of squared Frobenius from the trace of the
symmetric square. In the revised introduction, `a = α + β` and
`d = α * β` (for the specified Hecke polynomial, `d = N𝔮`). -/
theorem frobenius_square_trace {R : Type*} [CommRing R] (α β : R) :
    α ^ 2 + β ^ 2 = (α + β) ^ 2 - 2 * (α * β) := by
  ring

/-- The trace of the symmetric-square representation has the middle
root `α * β`, unlike the trace of Frobenius squared. -/
theorem symmetric_square_trace {R : Type*} [CommRing R] (α β : R) :
    α ^ 2 + α * β + β ^ 2 = (α + β) ^ 2 - α * β := by
  ring

/-- The extra summand in the symmetric square is exactly the determinant. -/
theorem symmetric_square_vs_frobenius_square {R : Type*} [CommRing R]
    (α β : R) :
    (α ^ 2 + α * β + β ^ 2) - (α ^ 2 + β ^ 2) = α * β := by
  ring

end HilbertModularity.RevisedPaperI
