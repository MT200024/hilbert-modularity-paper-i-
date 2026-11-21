/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedRMProduct
public import HilbertModularity.Geometry.TateModule.RealMultiplicationPairing

/-! # The selected product in the native RM factor presentation

The native endomorphism-labelled factors are the same integral RM
projectors on the selected plus Jacobian. This presentation lets the
existing exact pairing determinant apply to each factor.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

local instance selectedNativeProductFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Decompose the dual Tate polynomial using an endomorphism action while
all coefficient and group-scheme parents are still abstract. -/
theorem endomorphismLabelledDualTate_charpolyRev_two
    (K : Type*) [Field K] [CharZero K]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type*) [Field F] [NumberField F]
    (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (φ : 𝓞 F →+* End A)
    [FiniteDimensional L (L ⊗[ℚ_[ℓ]] rationalTate K A.X ℓ)]
    (labels : Fin 2 ≃ (F →ₐ[ℚ] L))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (b : Module.Basis (Fin 4) L
      (Module.Dual L (L ⊗[ℚ_[ℓ]] rationalTate K A.X ℓ)))
    (b₀ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate K A ℓ F L hL φ
        (labels 0)).toSubmodule))
    (b₁ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate K A ℓ F L hL φ
        (labels 1)).toSubmodule)) :
    (LinearMap.toMatrix b b (((tateRepresentation K A.X ℓ).baseChange L).dual g)).charpolyRev =
      (LinearMap.toMatrix b₀ b₀
        ((endomorphismLabelledTate K A ℓ F L hL φ
          (labels 0)).toRepresentation.dual g)).charpolyRev *
      (LinearMap.toMatrix b₁ b₁
        ((endomorphismLabelledTate K A ℓ F L hL φ
          (labels 1)).toRepresentation.dual g)).charpolyRev := by
  unfold endomorphismLabelledTate at b₀ b₁ ⊢
  change Module.Basis (Fin 2) L
    (Module.Dual L (labelledTateSummand K A.X ℓ F L hL
      ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)
      (labels 0))) at b₀
  change Module.Basis (Fin 2) L
    (Module.Dual L (labelledTateSummand K A.X ℓ F L hL
      ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)
      (labels 1))) at b₁
  have hprod := labelledDualTate_charpolyRev_two K A.X ℓ F L hL
    ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)
    (pointsEndomorphismAction_realized K A F φ)
    labels g b b₀ b₁
  unfold labelledDualTateFactor at hprod
  refine hprod.trans ?_
  congr 1

/-- Full dual Tate Frobenius is the product of the two native
endomorphism-labelled cohomological factors. -/
theorem primeFiveSelectedNativeRM_charpolyRev_product
    (L : Type*) [Field L] [Algebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : realCyclotomicField 5,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (realCyclotomicField 5 →ₐ[ℚ] L))
    (g : AlgebraicClosure (realCyclotomicField 5) ≃ₐ[realCyclotomicField 5]
      AlgebraicClosure (realCyclotomicField 5))
    (b : Module.Basis (Fin 4) L
      (Module.Dual L (L ⊗[ℚ_[5]] rationalTate (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5)))
    (b₀ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
        5 (realCyclotomicField 5) L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 0)).toSubmodule))
    (b₁ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
        5 (realCyclotomicField 5) L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 1)).toSubmodule)) :
    (LinearMap.toMatrix b b
      (((tateRepresentation (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5).baseChange L).dual g)).charpolyRev =
    (LinearMap.toMatrix b₀ b₀
      ((endomorphismLabelledTate (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
        5 (realCyclotomicField 5) L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 0)).toRepresentation.dual g)).charpolyRev *
    (LinearMap.toMatrix b₁ b₁
      ((endomorphismLabelledTate (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
        5 (realCyclotomicField 5) L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 1)).toRepresentation.dual g)).charpolyRev := by
  let : FiniteDimensional L (L ⊗[ℚ_[5]] rationalTate (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5) := by
    infer_instance
  with_reducible
    exact endomorphismLabelledDualTate_charpolyRev_two
      (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
      5 (realCyclotomicField 5) L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter)
      labels g b b₀ b₁

end HilbertModularity.Examples
