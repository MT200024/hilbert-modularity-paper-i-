/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Cyclotomic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Scalar extension of cyclotomic fields

When the cyclotomic polynomial remains irreducible over a characteristic-zero
field, extending scalars in the fixed rational cyclotomic field gives its
cyclotomic splitting field over the new coefficients.
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

namespace HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [CharZero K]

/-- The embedding sending the fixed global root to the standard primitive root
in the cyclotomic splitting field over `K`. -/
def splittingFieldEmbedding : cyclotomicField N →ₐ[ℚ] CyclotomicField N K :=
  ((root_isPrimitiveRoot N).powerBasis ℚ).lift
    (IsCyclotomicExtension.zeta N K (CyclotomicField N K)) (by
      rw [IsPrimitiveRoot.powerBasis_gen,
        ← (root_isPrimitiveRoot N).minpoly_eq_cyclotomic_of_irreducible
          (cyclotomic.irreducible_rat (NeZero.pos N))]
      rw [← eval_map_algebraMap, map_cyclotomic, ← IsRoot.def]
      exact (IsCyclotomicExtension.zeta_spec N K (CyclotomicField N K)).isRoot_cyclotomic
        (NeZero.pos N))

@[simp] theorem splittingFieldEmbedding_root :
    splittingFieldEmbedding N K (root N) =
      IsCyclotomicExtension.zeta N K (CyclotomicField N K) :=
  PowerBasis.lift_gen _ _ _

/-- The canonical scalar-extension map induced by the chosen primitive roots. -/
def splittingFieldTensorMap : K ⊗[ℚ] cyclotomicField N →ₐ[K] CyclotomicField N K :=
  AlgHom.liftEquiv ℚ K _ _ (splittingFieldEmbedding N K)

@[simp] theorem splittingFieldTensorMap_tmul (a : K) (x : cyclotomicField N) :
    splittingFieldTensorMap N K (a ⊗ₜ[ℚ] x) = a • splittingFieldEmbedding N K x := rfl

/-- The scalar-extension map contains the generating primitive root in its image. -/
theorem splittingFieldTensorMap_surjective : Function.Surjective (splittingFieldTensorMap N K) := by
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← IsCyclotomicExtension.adjoin_primitive_root_eq_top
    (IsCyclotomicExtension.zeta_spec N K (CyclotomicField N K))]
  apply Algebra.adjoin_le
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact ⟨1 ⊗ₜ[ℚ] root N, by simp⟩

/-- Irreducibility over the new coefficients makes scalar extension an isomorphism. -/
def splittingFieldTensorEquiv (hirr : Irreducible (cyclotomic N K)) :
    K ⊗[ℚ] cyclotomicField N ≃ₐ[K] CyclotomicField N K :=
by
  letI : FiniteDimensional K (CyclotomicField N K) :=
    ((IsCyclotomicExtension.zeta_spec N K (CyclotomicField N K)).powerBasis K).finite
  exact AlgEquiv.ofBijective (splittingFieldTensorMap N K) ⟨by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (splittingFieldTensorMap N K).toLinearMap) ?_).mpr
      (splittingFieldTensorMap_surjective N K)
    rw [Module.finrank_baseChange,
      IsCyclotomicExtension.finrank (cyclotomicField N)
        (cyclotomic.irreducible_rat (NeZero.pos N)),
      IsCyclotomicExtension.finrank (CyclotomicField N K) hirr],
    splittingFieldTensorMap_surjective N K⟩

/-- Scalar extension of the inclusion of the real cyclotomic field. -/
def realTensorInclusion :
    K ⊗[ℚ] realCyclotomicField N →ₐ[K] K ⊗[ℚ] cyclotomicField N :=
  Algebra.TensorProduct.map (AlgHom.id K K)
    (IntermediateField.inclusion (realCyclotomicField_le N))

/-- Extending scalars preserves the injectivity of the real-field inclusion. -/
theorem realTensorInclusion_injective : Function.Injective (realTensorInclusion N K) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (IntermediateField.inclusion (realCyclotomicField_le N)).toLinearMap
    (IntermediateField.inclusion (realCyclotomicField_le N)).injective

/-- If the full cyclotomic polynomial remains irreducible, the real cyclotomic
coefficient tensor is a field as well. -/
theorem realTensor_isField (hirr : Irreducible (cyclotomic N K)) :
    IsField (K ⊗[ℚ] realCyclotomicField N) := by
  let f := (splittingFieldTensorEquiv N K hirr).toAlgHom.comp (realTensorInclusion N K)
  have hf : Function.Injective f :=
    (splittingFieldTensorEquiv N K hirr).injective.comp (realTensorInclusion_injective N K)
  let : IsDomain (K ⊗[ℚ] realCyclotomicField N) := hf.isDomain f.toRingHom
  exact isField_of_isIntegral_of_isField' (R := K) (S := K ⊗[ℚ] realCyclotomicField N) (Field.toIsField K)

end HilbertModularity.Cyclotomic
