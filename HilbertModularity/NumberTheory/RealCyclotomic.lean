/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Cyclotomic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Total reality of the trace-generated cyclotomic field -/

public noncomputable section

namespace HilbertModularity.Cyclotomic

/-- Every complex embedding of the trace-generated field is fixed by conjugation. -/
theorem realCyclotomicField_embedding_isReal (N : ℕ) [NeZero N]
    (φ : realCyclotomicField N →+* ℂ) : NumberField.ComplexEmbedding.IsReal φ := by
  let i := IntermediateField.inclusion (realCyclotomicField_le N)
  let : Algebra (realCyclotomicField N) (cyclotomicField N) := i.toRingHom.toAlgebra
  let : Algebra (realCyclotomicField N) ℂ := φ.toAlgebra
  let : Algebra.IsAlgebraic (realCyclotomicField N) (cyclotomicField N) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (L := realCyclotomicField N)
      (A := cyclotomicField N)
  let e : cyclotomicField N →ₐ[realCyclotomicField N] ℂ := IsAlgClosed.lift
  have he (x : realCyclotomicField N) : e (i x) = φ x := e.commutes x
  apply NumberField.ComplexEmbedding.isReal_iff.mpr
  ext x
  change star (φ x) = φ x
  have hc := embedding_conjugation N e.toRingHom.toRatAlgHom (i x)
  change e (conjugation N (i x)) = star (e (i x)) at hc
  rw [conjugation_inclusion] at hc
  exact (congrArg star (he x)).symm.trans (hc.symm.trans (he x))

/-- The project's actual real cyclotomic coefficient field is totally real. -/
instance realCyclotomicField_isTotallyReal (N : ℕ) [NeZero N] :
    NumberField.IsTotallyReal (realCyclotomicField N) where
  isReal v := NumberField.InfinitePlace.isReal_iff.mpr
    (realCyclotomicField_embedding_isReal N v.embedding)

end HilbertModularity.Cyclotomic
