/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateGeometricPathNaturality
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.ArithmeticCoefficients

/-! # Real-multiplication coefficients along geometric Tate paths -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)

set_option maxHeartbeats 1000000 in
/-- The actual path intertwines the whole tensor coefficient action arising from
one integral real-multiplication action on the original group scheme. -/
theorem rationalTateGeometricPathEquiv_tensorCoefficients (a : ℚ_[p] ⊗[ℚ] F)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    rationalTateGeometricPathEquiv K L e A p
        (((tensorTateLocalSystemAction K A p F φ a).app (Scheme.etaleFiberPoint K S x)).hom v) =
      ((tensorTateLocalSystemAction L A p F φ a).app (Scheme.etaleFiberPoint L S y)).hom
        (rationalTateGeometricPathEquiv K L e A p v) := by
  let aK := (TateModule.rationalEndomorphismMap p
    (Additive (Scheme.geometricPointOver K x ⟶ A.X))).comp
      ((CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver K x) A).comp φ)
  let aL := (TateModule.rationalEndomorphismMap p
    (Additive (Scheme.geometricPointOver L y ⟶ A.X))).comp
      ((CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver L y) A).comp φ)
  let E := rationalTateGeometricPathEquiv K L e A p
  have h := NumberField.RingOfIntegers.tensorExtension_intertwines F aK aL E.toLinearMap
    (fun c w => LinearMap.congr_fun
      (rationalTateGeometricPathEquiv_natural K L e p (φ c)) w) a v
  exact (congrArg E (LinearMap.congr_fun (tensorTateLocalSystemAction_app K A p F φ x a) v)).trans
    (h.trans (LinearMap.congr_fun (tensorTateLocalSystemAction_app L A p F φ y a) (E v)).symm)

end AlgebraicGeometry.GroupScheme
