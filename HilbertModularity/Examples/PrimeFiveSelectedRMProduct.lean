/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveRMFactorProduct
public import HilbertModularity.Examples.PrimeFiveSelectedJacobian
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricResidual

/-! # The actual selected level-five RM projector product

The full dual Tate polynomial of the single plus Jacobian is the product of
its two idempotent RM factors, ordered by a specified coefficient embedding.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

local instance selectedRMProductFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
theorem selectedRMProductFiveLowerBound : 5 ≤ 5 := by decide
local notation "K₅" => realCyclotomicField 5
local notation "J₅" => primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter

/-- The points action of the actual integral RM on the selected plus
Jacobian at `ξ=125`. -/
def primeFiveSelectedPointsRM :
    𝓞 (realCyclotomicField 5) →+* AddMonoid.End
      (Points (realCyclotomicField 5) (AlgebraicClosure (realCyclotomicField 5))
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X) :=
  (pointsEndomorphismMap (realCyclotomicField 5)
    (AlgebraicClosure (realCyclotomicField 5))
    (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)).comp
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound primeFiveParameter)

/-- Every selected RM point action comes from the same group-scheme
endomorphism, as required by the coefficient-idempotent decomposition. -/
theorem primeFiveSelectedPointsRM_realized
    (a : 𝓞 (realCyclotomicField 5)) :
    ∃ (f : (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X ⟶
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X)
      (_ : IsMonHom f),
      primeFiveSelectedPointsRM a =
        pointsMap (realCyclotomicField 5)
          (AlgebraicClosure (realCyclotomicField 5)) f := by
  exact ⟨(primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound primeFiveParameter a).hom.hom.hom,
    inferInstance, rfl⟩

/-- The actual selected plus Jacobian's full scalar-extended dual Tate
polynomial is the product of its two ordered RM-idempotent factors. This
asserts no numeric polynomial or choice of trace label. -/
theorem primeFiveSelectedRM_charpolyRev_product
    (L : Type*) [Field L] [Algebra ℚ_[5] L] [Algebra ℚ L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L))
    (g : AlgebraicClosure K₅ ≃ₐ[K₅] AlgebraicClosure K₅)
    (b : Module.Basis (Fin 4) L
      (Module.Dual L (L ⊗[ℚ_[5]] rationalTate K₅ (J₅).X 5)))
    (b₀ : Module.Basis (Fin 2) L
      (Module.Dual L (labelledTateSummand K₅ (J₅).X 5 K₅ L hL
        primeFiveSelectedPointsRM (labels 0))))
    (b₁ : Module.Basis (Fin 2) L
      (Module.Dual L (labelledTateSummand K₅ (J₅).X 5 K₅ L hL
        primeFiveSelectedPointsRM (labels 1)))) :
    (LinearMap.toMatrix b b
      (((tateRepresentation K₅ (J₅).X 5).baseChange L).dual g)).charpolyRev =
      (LinearMap.toMatrix b₀ b₀
        (labelledDualTateFactor K₅ (J₅).X 5 K₅ L hL primeFiveSelectedPointsRM
          primeFiveSelectedPointsRM_realized (labels 0) g)).charpolyRev *
      (LinearMap.toMatrix b₁ b₁
        (labelledDualTateFactor K₅ (J₅).X 5 K₅ L hL primeFiveSelectedPointsRM
          primeFiveSelectedPointsRM_realized (labels 1) g)).charpolyRev := by
  let : FiniteDimensional L (L ⊗[ℚ_[5]] rationalTate K₅ (J₅).X 5) := by
    infer_instance
  exact labelledDualTate_charpolyRev_two K₅ (J₅).X 5 K₅ L hL
    primeFiveSelectedPointsRM primeFiveSelectedPointsRM_realized
    labels g b b₀ b₁

end HilbertModularity.Examples
