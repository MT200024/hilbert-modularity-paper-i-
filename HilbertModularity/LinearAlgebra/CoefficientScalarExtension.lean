/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.CoefficientDecomposition
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Scalar extension of coefficient-algebra bases

A basis over an unsplit coefficient algebra gives coordinates over its scalar
extension. The coordinates respect the original coefficient action, so they
can be used to compute dimensions of the actual embedding-idempotent images.
This is the scalar-extension step in [TripathiGoswami, coefficient-label lemma].
-/

@[expose] public noncomputable section
open scoped TensorProduct

namespace Algebra.TensorProduct

variable (k R F L V : Type*) [Field k] [Field R] [Field F] [Field L]
  [Algebra k R] [Algebra k F] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
  [AddCommGroup V] [Module R V] [Module (R ⊗[k] F) V]
  [IsScalarTower R (R ⊗[k] F) V]

/-- Extending a coefficient basis gives coordinates over the extended coefficient algebra. -/
def coefficientScalarExtensionEquiv {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V) :
    (L ⊗[R] V) ≃ₗ[L] (ι → L ⊗[k] F) := by
  classical
  exact ((b.equivFun.restrictScalars R).baseChange R L _ _).trans
    ((TensorProduct.piRight R L L (fun _ : ι => R ⊗[k] F)).trans
      (LinearEquiv.piCongrRight fun _ => (cancelBaseChange k R L L F).toLinearEquiv))

/-- The extended coordinates are obtained by applying the coefficient base-change map. -/
@[simp]
theorem coefficientScalarExtensionEquiv_tmul {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V) (l : L) (v : V) (i : ι) :
    coefficientScalarExtensionEquiv k R F L V b (l ⊗ₜ[R] v) i =
      cancelBaseChange k R L L F (l ⊗ₜ[R] b.equivFun v i) := rfl

variable [Module k V] [IsScalarTower k R V]

/-- The coefficient action extended from the original module, before choosing a basis. -/
def coefficientScalarExtensionAction :
    L ⊗[k] F →ₐ[L] Module.End L (L ⊗[R] V) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (((Module.End.baseChangeHom R L V).restrictScalars k).comp
      (((Algebra.lsmul R R V).restrictScalars k).comp
        (includeRight : F →ₐ[k] R ⊗[k] F)))
    (fun a _ => Algebra.commutes a _)

/-- A pure coefficient tensor acts by scalar multiplication and base change of the old action. -/
theorem coefficientScalarExtensionAction_tmul_eq (a : L) (f : F) :
    coefficientScalarExtensionAction k R F L V (a ⊗ₜ[k] f) =
      a • (Algebra.lsmul R R V ((1 : R) ⊗ₜ[k] f)).baseChange L := rfl

omit [Module (R ⊗[k] F) V] [IsScalarTower R (R ⊗[k] F) V] in
/-- Scalar extension of an action presented by an algebra homomorphism preserves its operators. -/
theorem coefficientScalarExtensionAction_compHom_tmul
    (α : R ⊗[k] F →ₐ[R] Module.End R V) (f : F) :
    letI : Module (R ⊗[k] F) V := Module.compHom V α.toRingHom
    ∀ [IsScalarTower R (R ⊗[k] F) V],
      coefficientScalarExtensionAction k R F L V ((1 : L) ⊗ₜ[k] f) =
        (α ((1 : R) ⊗ₜ[k] f)).baseChange L := by
  let : Module (R ⊗[k] F) V := Module.compHom V α.toRingHom
  intro h
  rw [coefficientScalarExtensionAction_tmul_eq, one_smul]
  rfl

/-- On pure tensors the extended coefficient action is the original action on the second factor. -/
@[simp]
theorem coefficientScalarExtensionAction_tmul (a l : L) (f : F) (v : V) :
    coefficientScalarExtensionAction k R F L V (a ⊗ₜ[k] f) (l ⊗ₜ[R] v) =
      (a * l) ⊗ₜ[R] (((1 : R) ⊗ₜ[k] f) • v) := by
  change a • (l ⊗ₜ[R] (((1 : R) ⊗ₜ[k] f) • v)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul]

/-- Extended coordinates intertwine the actual coefficient action with coordinate multiplication. -/
theorem coefficientScalarExtensionEquiv_action {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V) (c : L ⊗[k] F) (w : L ⊗[R] V) (i : ι) :
    coefficientScalarExtensionEquiv k R F L V b
        (coefficientScalarExtensionAction k R F L V c w) i =
      c * coefficientScalarExtensionEquiv k R F L V b w i := by
  induction c using TensorProduct.inductionOn with
  | add c d hc hd => simp only [map_add, LinearMap.add_apply, Pi.add_apply, hc, hd, add_mul]
  | tmul a f =>
    induction w using TensorProduct.inductionOn with
    | add v w hv hw => simp only [map_add, Pi.add_apply, hv, hw, mul_add]
    | tmul l v =>
      rw [coefficientScalarExtensionAction_tmul, coefficientScalarExtensionEquiv_tmul,
        coefficientScalarExtensionEquiv_tmul, map_smul]
      change cancelBaseChange k R L L F
          ((a * l) ⊗ₜ[R] (((1 : R) ⊗ₜ[k] f) * b.equivFun v i)) = _
      rw [← Algebra.TensorProduct.tmul_mul_tmul, map_mul]
      simp only [cancelBaseChange_tmul, one_smul]

/-- The scalar-extended coordinate equivalence is linear over the full coefficient algebra. -/
def coefficientScalarExtensionLinearEquiv {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V) :
    letI : Module (L ⊗[k] F) (L ⊗[R] V) :=
      Module.compHom _ (coefficientScalarExtensionAction k R F L V).toRingHom
    (L ⊗[R] V) ≃ₗ[L ⊗[k] F] (ι → L ⊗[k] F) := by
  letI : Module (L ⊗[k] F) (L ⊗[R] V) :=
    Module.compHom _ (coefficientScalarExtensionAction k R F L V).toRingHom
  refine { (coefficientScalarExtensionEquiv k R F L V b).toAddEquiv with map_smul' := ?_ }
  intro c w
  funext i
  exact coefficientScalarExtensionEquiv_action k R F L V b c w i

/-- A coefficient basis extends to a basis for the canonical scalar-extended action. -/
def coefficientScalarExtensionBasis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V) :
    letI : Module (L ⊗[k] F) (L ⊗[R] V) :=
      Module.compHom _ (coefficientScalarExtensionAction k R F L V).toRingHom
    Module.Basis ι (L ⊗[k] F) (L ⊗[R] V) := by
  letI : Module (L ⊗[k] F) (L ⊗[R] V) :=
    Module.compHom _ (coefficientScalarExtensionAction k R F L V).toRingHom
  exact (Pi.basisFun (L ⊗[k] F) ι).map
    (coefficientScalarExtensionLinearEquiv k R F L V b).symm

/-- The extended basis vectors are the pure tensors of the original coefficient basis. -/
@[simp]
theorem coefficientScalarExtensionBasis_apply {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V) (i : ι) :
    coefficientScalarExtensionBasis k R F L V b i = (1 : L) ⊗ₜ[R] b i := by
  classical
  let : Module (L ⊗[k] F) (L ⊗[R] V) :=
    Module.compHom _ (coefficientScalarExtensionAction k R F L V).toRingHom
  apply (coefficientScalarExtensionLinearEquiv k R F L V b).injective
  change (coefficientScalarExtensionLinearEquiv k R F L V b)
      ((coefficientScalarExtensionLinearEquiv k R F L V b).symm
        (Pi.basisFun (L ⊗[k] F) ι i)) = _
  rw [LinearEquiv.apply_symm_apply]
  ext j
  change Pi.basisFun (L ⊗[k] F) ι i j =
    coefficientScalarExtensionEquiv k R F L V b ((1 : L) ⊗ₜ[R] b i) j
  by_cases h : j = i
  · subst j
    simp [coefficientScalarExtensionEquiv_tmul, Module.Basis.equivFun_self,
      Pi.basisFun_apply, ← Algebra.TensorProduct.one_def]
  · simp [coefficientScalarExtensionEquiv_tmul, Module.Basis.equivFun_self,
      Pi.basisFun_apply, h, Ne.symm h]

variable [FiniteDimensional k F] [Algebra.IsSeparable k F]

/-- The original coefficient basis supplies coordinates on each actual idempotent image
of the scalar-extended module. -/
def coefficientScalarExtensionProjectionEquiv {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V)
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits) (σ : F →ₐ[k] L) :
    LinearMap.range (coefficientScalarExtensionAction k R F L V
      (embeddingIdempotent k F L hL σ)) ≃ₗ[L] (ι → L) := by
  letI : Module (L ⊗[k] F) (L ⊗[R] V) :=
    Module.compHom _ (coefficientScalarExtensionAction k R F L V).toRingHom
  letI : IsScalarTower L (L ⊗[k] F) (L ⊗[R] V) :=
    IsScalarTower.of_algebraMap_smul fun l w => by
      change coefficientScalarExtensionAction k R F L V (algebraMap L (L ⊗[k] F) l) w = l • w
      rw [(coefficientScalarExtensionAction k R F L V).commutes]
      rfl
  exact coefficientSummandEquiv k F L (L ⊗[R] V) hL
    (coefficientScalarExtensionBasis k R F L V b) σ

/-- The labelled basis induced by an original coefficient basis. -/
def coefficientScalarExtensionProjectionBasis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V)
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits) (σ : F →ₐ[k] L) :
    Module.Basis ι L (LinearMap.range (coefficientScalarExtensionAction k R F L V
      (embeddingIdempotent k F L hL σ))) :=
  (Pi.basisFun L ι).map (coefficientScalarExtensionProjectionEquiv k R F L V b hL σ).symm

/-- Each labelled basis vector is the actual projector applied to the scalar extension
of the corresponding original coefficient-basis vector. -/
@[simp]
theorem coefficientScalarExtensionProjectionBasis_coe {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V)
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits) (σ : F →ₐ[k] L) (i : ι) :
    (coefficientScalarExtensionProjectionBasis k R F L V b hL σ i : L ⊗[R] V) =
      coefficientScalarExtensionAction k R F L V (embeddingIdempotent k F L hL σ)
        ((1 : L) ⊗ₜ[R] b i) := by
  classical
  let : Module (L ⊗[k] F) (L ⊗[R] V) :=
    Module.compHom _ (coefficientScalarExtensionAction k R F L V).toRingHom
  let : IsScalarTower L (L ⊗[k] F) (L ⊗[R] V) :=
    IsScalarTower.of_algebraMap_smul fun l w => by
      change coefficientScalarExtensionAction k R F L V (algebraMap L (L ⊗[k] F) l) w = l • w
      rw [(coefficientScalarExtensionAction k R F L V).commutes]
      rfl
  let b' := coefficientScalarExtensionBasis k R F L V b
  change b'.equivFun.symm (fun j => Pi.basisFun L ι i j • embeddingIdempotent k F L hL σ) =
    embeddingIdempotent k F L hL σ • ((1 : L) ⊗ₜ[R] b i)
  rw [← coefficientScalarExtensionBasis_apply k R F L V b i]
  apply b'.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, map_smul]
  funext j
  change Pi.basisFun L ι i j • embeddingIdempotent k F L hL σ =
    embeddingIdempotent k F L hL σ * b'.equivFun (b' i) j
  rw [Module.Basis.equivFun_self]
  by_cases h : j = i
  · subst j
    simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, h, Ne.symm h]

/-- Each actual embedding-idempotent image after scalar extension has the original coefficient rank. -/
theorem finrank_coefficientScalarExtensionProjection {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⊗[k] F) V)
    (hL : ∀ f : F, ((minpoly k f).map (algebraMap k L)).Splits) (σ : F →ₐ[k] L) :
    Module.finrank L (LinearMap.range (coefficientScalarExtensionAction k R F L V
      (embeddingIdempotent k F L hL σ))) = Fintype.card ι := by
  rw [(coefficientScalarExtensionProjectionEquiv k R F L V b hL σ).finrank_eq,
    Module.finrank_pi]

end Algebra.TensorProduct
