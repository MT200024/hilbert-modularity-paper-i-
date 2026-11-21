/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateGeometricPathCoefficients
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.GeometricCoefficients

/-! # Coefficient-linear transport between actual geometric Tate fibres -/

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
/-- An actual geometric path is linear over the tensor coefficient algebra of the same family.
In particular, a coefficient basis at the generic point transports to any connected fibre. -/
def coefficientTateGeometricPathEquiv :
    let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    let W := TateModule.rational p (Additive (Scheme.geometricPointOver L y ⟶ A.X))
    letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
      Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
    letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
      Module.compHom W (geometricTensorTateAction L A p F φ y).toRingHom
    V ≃ₗ[ℚ_[p] ⊗[ℚ] F] W := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let W := TateModule.rational p (Additive (Scheme.geometricPointOver L y ⟶ A.X))
  letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (geometricTensorTateAction L A p F φ y).toRingHom
  refine { (rationalTateGeometricPathEquiv K L e A p).toAddEquiv with map_smul' := ?_ }
  intro a v
  change rationalTateGeometricPathEquiv K L e A p (geometricTensorTateAction K A p F φ x a v) =
    geometricTensorTateAction L A p F φ y a (rationalTateGeometricPathEquiv K L e A p v)
  exact rationalTateGeometricPathEquiv_tensorCoefficients K L e A p F φ a v

/-- Coefficient-linear transport has exactly the original geometric action on vectors. -/
@[simp] theorem coefficientTateGeometricPathEquiv_apply
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    coefficientTateGeometricPathEquiv K L e A p F φ v = rationalTateGeometricPathEquiv K L e A p v := rfl

end AlgebraicGeometry.GroupScheme
