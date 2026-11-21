/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientPaths
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientMonodromy
public import HilbertModularity.Geometry.GroupScheme.TateGeometricPathMonodromy

/-! # Coefficient-linear geometric transport of Tate monodromy

The same geometric path intertwines monodromy over the full coefficient tensor
algebra. This keeps the real-multiplication label fixed when changing basepoint.
-/

public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)

/-- Geometric Tate transport intertwines the actual action over its coefficient algebra. -/
def coefficientTateGeometricPathRepresentationEquiv :
    let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    let W := TateModule.rational p (Additive (Scheme.geometricPointOver L y ⟶ A.X))
    letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
      Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
    letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
      Module.compHom W (geometricTensorTateAction L A p F φ y).toRingHom
    (coefficientTateMonodromy K A p F φ x).Equiv
      ((coefficientTateMonodromy L A p F φ y).comp
        (Scheme.geometricFiberPathGroupEquiv K L e).toMonoidHom) := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let W := TateModule.rational p (Additive (Scheme.geometricPointOver L y ⟶ A.X))
  letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (geometricTensorTateAction L A p F φ y).toRingHom
  exact .mk (coefficientTateGeometricPathEquiv K L e A p F φ) (by
    intro g
    apply LinearMap.ext
    intro v
    exact congrArg (fun f => f v)
      ((rationalTateGeometricPathRepresentationEquiv K L e A p).isIntertwining' g))

end AlgebraicGeometry.GroupScheme
