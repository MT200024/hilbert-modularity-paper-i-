/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.CoefficientTensorFactor
public import HilbertModularity.RepresentationTheory.CoefficientDecomposition
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import HilbertModularity.RepresentationTheory.ScalarRestriction

/-! # Equivariant coefficient-tensor realization of labelled factors

The actual embedding-idempotent subrepresentation is equivalent to scalar
extension over the original coefficient algebra along that embedding. This
retains the original acting group and its action on the original tensorand,
as required by [TripathiGoswami, ramified scalar label].
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation
open Algebra.TensorProduct
variable (k R F L : Type*) [Field k] [Field R] [Field F] [Field L]
  [Algebra k R] [Algebra k F] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
  {G V : Type*} [Monoid G] [AddCommGroup V]
  [Module R V] [Module (R ⊗[k] F) V] [IsScalarTower R (R ⊗[k] F) V]
  [Module k V] [IsScalarTower k R V]
  [FiniteDimensional k F] [Algebra.IsSeparable k F]
  (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits)
  (ρ : Representation (R ⊗[k] F) G V)

/-- The actual labelled subrepresentation of the scalar-extended original coefficient module. -/
def coefficientTensorSubrepresentation (σ : F →ₐ[k] L) :
    Subrepresentation ((ρ.restrictScalars R).baseChange L) := by
  letI : Module (L ⊗[k] F) (L ⊗[R] V) :=
    Module.compHom _ (coefficientScalarExtensionAction k R F L V).toRingHom
  letI : IsScalarTower L (L ⊗[k] F) (L ⊗[R] V) :=
    IsScalarTower.of_algebraMap_smul fun l w => by
      change coefficientScalarExtensionAction k R F L V (algebraMap L (L ⊗[k] F) l) w = l • w
      rw [(coefficientScalarExtensionAction k R F L V).commutes]
      rfl
  exact coefficientSubrepresentation k F L hL ((ρ.restrictScalars R).baseChange L)
    (fun g a v => coefficientScalarExtensionAction_naturality k R F L V V (ρ g) a v) σ

/-- Scalar extension along an embedding is equivariantly the actual idempotent-labelled factor. -/
def coefficientTensorFactorEquiv {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V) (σ : F →ₐ[k] L) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    (ρ.baseChange L).Equiv
      (coefficientTensorSubrepresentation k R F L hL ρ σ).toRepresentation := by
  letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  refine .mk (coefficientProjectionTensorEquiv k R F L V b hL σ) ?_
  intro g
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  induction w using TensorProduct.inductionOn with
  | add w z hw hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hw hz
  | tmul l v =>
    change (coefficientProjectionTensorEquiv k R F L V b hL σ
        ((ρ.baseChange L) g (l ⊗ₜ[R ⊗[k] F] v)) : L ⊗[R] V) =
      ((ρ.restrictScalars R).baseChange L) g
        (coefficientProjectionTensorEquiv k R F L V b hL σ
          (l ⊗ₜ[R ⊗[k] F] v) : L ⊗[R] V)
    rw [baseChange_tmul, coefficientProjectionTensorEquiv_tmul,
      coefficientProjectionTensorEquiv_tmul]
    exact (coefficientScalarExtensionAction_naturality k R F L V V (ρ g)
      (embeddingIdempotent k F L hL σ) (l ⊗ₜ[R] v)).symm

/-- The actual labelled factor is equivariantly the coefficient tensor without a basis hypothesis. -/
def coefficientTensorSummandEquiv (σ : F →ₐ[k] L) :
    letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
    (ρ.baseChange L).Equiv
      (coefficientTensorSubrepresentation k R F L hL ρ σ).toRepresentation := by
  letI : Algebra (R ⊗[k] F) L := (coefficientTensorEmbedding k R F L σ).toAlgebra
  refine .mk (Algebra.TensorProduct.coefficientTensorSummandEquiv k R F L V hL σ) ?_
  intro g
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  induction w using TensorProduct.inductionOn with
  | add w z hw hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hw hz
  | tmul l v =>
    change (Algebra.TensorProduct.coefficientTensorSummandEquiv k R F L V hL σ
        ((ρ.baseChange L) g (l ⊗ₜ[R ⊗[k] F] v)) : L ⊗[R] V) =
      ((ρ.restrictScalars R).baseChange L) g
        (Algebra.TensorProduct.coefficientTensorSummandEquiv k R F L V hL σ
          (l ⊗ₜ[R ⊗[k] F] v) : L ⊗[R] V)
    rw [baseChange_tmul, Algebra.TensorProduct.coefficientTensorSummandEquiv_tmul,
      Algebra.TensorProduct.coefficientTensorSummandEquiv_tmul]
    exact (coefficientScalarExtensionAction_naturality k R F L V V (ρ g)
      (embeddingIdempotent k F L hL σ) (l ⊗ₜ[R] v)).symm

end Representation
