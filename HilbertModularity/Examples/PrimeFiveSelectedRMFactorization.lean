/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedNativeRMProduct
public import HilbertModularity.Examples.PrimeFiveRMQuadraticProduct
public import HilbertModularity.LinearAlgebra.ReverseCharacteristicPolynomial

/-! # Factor a selected plus-Jacobian full polynomial by its native RM action

The full intrinsic polynomial and the covariant pairing determinant are
supplied as independently established properties of the same selected
Jacobian. The algebraic deduction produces its two quadratic trace factors.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

local instance selectedFactorFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local notation "K₅" => realCyclotomicField 5
local notation "J₅" => primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter

/-- The checked full polynomial, native projector product and common
determinant q yield the displayed two-factor trace polynomial. -/
theorem primeFiveSelectedRM_factorization_of_intrinsic
    (L : Type) [Field L] [Algebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L))
    (g : AlgebraicClosure K₅ ≃ₐ[K₅] AlgebraicClosure K₅)
    (q : L) (R : Polynomial L)
    (hfull : (((tateRepresentation K₅ (J₅).X 5).baseChange L).dual g).charpolyRev = R)
    (hdet : ∀ σ : K₅ →ₐ[ℚ] L,
      LinearMap.det ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) σ).toRepresentation.dual g) = q)
    (b : Module.Basis (Fin 4) L
      (Module.Dual L (L ⊗[ℚ_[5]] rationalTate K₅ (J₅).X 5)))
    (b₀ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 0)).toSubmodule))
    (b₁ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 1)).toSubmodule)) :
    let f₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 0)).toRepresentation.dual g
    let f₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 1)).toRepresentation.dual g
    quadraticTraceFactor (LinearMap.toMatrix b₀ b₀ f₀) q *
      quadraticTraceFactor (LinearMap.toMatrix b₁ b₁ f₁) q = R := by
  let f₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 0)).toRepresentation.dual g
  let f₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 1)).toRepresentation.dual g
  have hprodFactory := primeFiveSelectedNativeRM_charpolyRev_product
    L hL labels g
  have hprod := by
    with_reducible exact hprodFactory b b₀ b₁
  have hfullM : (LinearMap.toMatrix b b
      (((tateRepresentation K₅ (J₅).X 5).baseChange L).dual g)).charpolyRev = R :=
    (LinearMap.charpolyRev_toMatrix b _).trans hfull
  have hdet₀ : (LinearMap.toMatrix b₀ b₀ f₀).det = q := by
    simpa only [f₀, LinearMap.det_toMatrix] using hdet (labels 0)
  have hdet₁ : (LinearMap.toMatrix b₁ b₁ f₁).det = q := by
    simpa only [f₁, LinearMap.det_toMatrix] using hdet (labels 1)
  have hquad₀ := quadraticTraceFactor_eq_charpolyRev
    (LinearMap.toMatrix b₀ b₀ f₀) q hdet₀
  have hquad₁ := quadraticTraceFactor_eq_charpolyRev
    (LinearMap.toMatrix b₁ b₁ f₁) q hdet₁
  change quadraticTraceFactor (LinearMap.toMatrix b₀ b₀ f₀) q *
    quadraticTraceFactor (LinearMap.toMatrix b₁ b₁ f₁) q = R
  calc
    quadraticTraceFactor (LinearMap.toMatrix b₀ b₀ f₀) q *
        quadraticTraceFactor (LinearMap.toMatrix b₁ b₁ f₁) q =
      (LinearMap.toMatrix b₀ b₀ f₀).charpolyRev *
        (LinearMap.toMatrix b₁ b₁ f₁).charpolyRev :=
          congrArg₂ (· * ·) hquad₀ hquad₁
    _ = (LinearMap.toMatrix b b
      (((tateRepresentation K₅ (J₅).X 5).baseChange L).dual g)).charpolyRev := by
        with_reducible exact hprod.symm
    _ = R := hfullM

end HilbertModularity.Examples
