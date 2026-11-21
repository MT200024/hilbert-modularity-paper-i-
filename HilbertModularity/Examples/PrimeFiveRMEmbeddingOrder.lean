/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveRMBlockFactorization
public import HilbertModularity.NumberTheory.RealCyclotomicPrime

/-! # The two real-multiplication labels at conductor five

The fixed coefficient embedding is placed first. The other embedding is
obtained from the degree-two embedding count, so no unordered trace is silently
identified with the manuscript's first label.
-/

public noncomputable section

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic

local instance rmEmbeddingOrderFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A splitting coefficient field has exactly two embeddings of the real
level-five RM field. Any already fixed label can be the first coordinate of
the complete pair. -/
theorem exists_primeFiveRMEmbeddingOrder
    (L : Type*) [Field L] [Algebra ℚ L]
    (hL : ∀ x : realCyclotomicField 5,
      ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField 5 →ₐ[ℚ] L) :
    ∃ labels : Fin 2 ≃ (realCyclotomicField 5 →ₐ[ℚ] L),
      labels 0 = σ := by
  have hcard : Fintype.card (realCyclotomicField 5 →ₐ[ℚ] L) = 2 := by
    rw [AlgHom.card_of_splits ℚ (realCyclotomicField 5) L hL,
      finrank_realCyclotomicField 5 (by decide)]
  exact exists_finTwo_equiv_with_first hcard σ

end HilbertModularity.Examples
