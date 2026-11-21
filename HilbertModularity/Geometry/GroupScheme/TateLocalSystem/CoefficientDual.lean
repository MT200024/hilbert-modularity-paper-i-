/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiberDuality
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LabelledFiber
public import HilbertModularity.Geometry.TateModule.CoefficientDual
public import HilbertModularity.RepresentationTheory.Duality

/-! # Cohomological duals of the labelled Tate family

The cohomological factor is the dual of the actual labelled family. Its
arithmetic fibres are the native dual Tate factors, with the same coefficient
embedding, as prescribed in [TripathiGoswami, cohomological RM factor].
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra ChangeOfRings
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [Field L] [Algebra ℚ_[p] L]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ L]
  (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

/-- The cohomological labelled family is the contragredient of the actual covariant family. -/
def labelledCohomologicalTateLocalSystem (σ : F →ₐ[ℚ] L) :
    Scheme.EtaleFiberGroupoid K S ⥤ ModuleCat L :=
  ModuleCat.cohDual L (labelledTateLocalSystem K A p L F φ hL σ)

/-- Restriction of functionals gives the natural quotient onto a labelled dual family. -/
def labelledCohomologicalTateLocalSystemQuotient (σ : F →ₐ[ℚ] L) :
    ModuleCat.cohDual L (extendedTateLocalSystem K A p L) ⟶
      labelledCohomologicalTateLocalSystem K A p L F φ hL σ :=
  ModuleCat.cohDualMap L (labelledTateLocalSystemInclusion K A p L F φ hL σ)

/-- Transposed coefficient endomorphisms retain the same embedding on the dual quotient. -/
theorem tensorAction_labelledCohomologicalTateLocalSystem
    (σ : F →ₐ[ℚ] L) (z : L ⊗[ℚ] F) :
    ModuleCat.cohDualEndomorphism L (extendedTensorTateLocalSystemAction K A p L F φ) z ≫
        labelledCohomologicalTateLocalSystemQuotient K A p L F φ hL σ =
      Algebra.TensorProduct.embeddingEquiv ℚ F L hL z σ •
        labelledCohomologicalTateLocalSystemQuotient K A p L F φ hL σ := by
  exact ModuleCat.cohDualEndomorphism_quotient L
    (extendedTensorTateLocalSystemAction K A p L F φ)
    (labelledTateLocalSystemInclusion K A p L F φ hL σ) z _
    (tensorAction_labelledTateLocalSystem K A p L F φ hL σ z)

/-- Dualizing coefficients preserves their number-field embedding, without inversion. -/
theorem numberFieldAction_labelledCohomologicalTateLocalSystem
    (σ : F →ₐ[ℚ] L) (a : F) :
    ModuleCat.cohDualEndomorphism L (extendedTensorTateLocalSystemAction K A p L F φ)
        ((1 : L) ⊗ₜ[ℚ] a) ≫
        labelledCohomologicalTateLocalSystemQuotient K A p L F φ hL σ =
      σ a • labelledCohomologicalTateLocalSystemQuotient K A p L F φ hL σ := by
  simpa only [Algebra.TensorProduct.embeddingEquiv_tmul, one_mul] using
    tensorAction_labelledCohomologicalTateLocalSystem K A p L F φ hL σ ((1 : L) ⊗ₜ[ℚ] a)

/-- The dual quotient has a canonical section obtained by transposing the original retraction. -/
def labelledCohomologicalTateLocalSystemSection (σ : F →ₐ[ℚ] L) :
    labelledCohomologicalTateLocalSystem K A p L F φ hL σ ⟶
      ModuleCat.cohDual L (extendedTateLocalSystem K A p L) :=
  ModuleCat.cohDualMap L (CategoryTheory.Limits.factorThruImage
    (labelledTateLocalSystemProjection K A p L F φ hL σ))

/-- The cohomological factor is a natural retract of the dual ambient family. -/
@[simp] theorem labelledCohomologicalTateLocalSystem_section_quotient
    (σ : F →ₐ[ℚ] L) :
    labelledCohomologicalTateLocalSystemSection K A p L F φ hL σ ≫
      labelledCohomologicalTateLocalSystemQuotient K A p L F φ hL σ =
        𝟙 (labelledCohomologicalTateLocalSystem K A p L F φ hL σ) := by
  have h := congrArg (ModuleCat.cohDualMap L)
    (labelledTateLocalSystem_retraction K A p L F φ hL σ)
  simpa only [ModuleCat.cohDualMap_comp, ModuleCat.cohDualMap_id,
    labelledCohomologicalTateLocalSystemSection, labelledCohomologicalTateLocalSystemQuotient,
    labelledTateLocalSystemInclusion, labelledCohomologicalTateLocalSystem,
    labelledTateLocalSystem] using h

/-- Every actual arithmetic fibre of the dual family is its native labelled dual Tate factor. -/
def labelledCohomologicalTateLocalSystemArithmeticEquiv
    (x : Spec (CommRingCat.of K) ⟶ S) (σ : F →ₐ[ℚ] L) :
    Representation.Equiv
      (Scheme.arithmeticFiberRepresentation K S
        (labelledCohomologicalTateLocalSystem K A p L F φ hL σ) x)
      (labelledDualTateFactor K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
        (fiberPointsAction_realized K (AlgebraicClosure K) A x (𝓞 F) φ) σ) := by
  unfold labelledCohomologicalTateLocalSystem
  rw [Scheme.arithmeticFiberRepresentation_cohDual]
  unfold labelledDualTateFactor
  exact HilbertModularity.representationDualEquiv (K := L)
    (V := (labelledTateLocalSystem K A p L F φ hL σ).obj (Scheme.etaleFiberPoint K S x))
    (W := labelledTateSummand K (fiber K A x).X p F L hL
      (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ) σ)
    (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (labelledTateLocalSystem_arithmeticEquiv K A p L x F φ hL σ)

end AlgebraicGeometry.GroupScheme
