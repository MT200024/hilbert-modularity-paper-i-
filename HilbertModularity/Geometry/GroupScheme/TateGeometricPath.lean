/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TorsionGeometricPath
public import HilbertModularity.Topology.TateModule.Maps

/-! # Actual Tate-module transport along geometric paths

A single path transports all torsion levels compatibly. Passing to the
inverse limit and then extending scalars gives the integral and rational Tate
comparisons for the same group scheme over different geometric fields.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
open scoped TensorProduct
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The integral map induced by transport on every actual finite torsion fibre. -/
def integralTateGeometricPathMap :
    TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) →ₗ[ℤ_[p]]
      TateModule.integral p (Additive (Scheme.geometricPointOver L y ⟶ A.X)) :=
  TateModule.mapOfTorsion p (torsionGeometricPathLinearMap K L e A p)
    (torsionGeometricPathLinearMap_transition K L e A p)

/-- Every Tate coordinate is transported by the original torsion path. -/
@[simp] theorem integralTateGeometricPathMap_projection
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) (n : ℕ) :
    (integralTateGeometricPathMap K L e A p v).val n =
      torsionGeometricPathEquiv K L e A (p ^ n) (v.val n) := rfl

/-- A geometric path identifies the actual integral Tate modules of the two fibres. -/
def integralTateGeometricPathEquiv :
    TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) ≃ₗ[ℤ_[p]]
      TateModule.integral p (Additive (Scheme.geometricPointOver L y ⟶ A.X)) where
  __ := integralTateGeometricPathMap K L e A p
  invFun := integralTateGeometricPathMap L K e.symm A p
  left_inv v := by
    apply Subtype.ext
    funext n
    change (torsionGeometricPathEquiv K L e A (p ^ n)).symm
      (torsionGeometricPathEquiv K L e A (p ^ n) (v.val n)) = v.val n
    exact (torsionGeometricPathEquiv K L e A (p ^ n)).symm_apply_apply _
  right_inv v := by
    apply Subtype.ext
    funext n
    change torsionGeometricPathEquiv K L e A (p ^ n)
      ((torsionGeometricPathEquiv K L e A (p ^ n)).symm (v.val n)) = v.val n
    exact (torsionGeometricPathEquiv K L e A (p ^ n)).apply_symm_apply _

/-- Scalar extension transports the actual rational Tate modules along the same path. -/
def rationalTateGeometricPathEquiv :
    TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) ≃ₗ[ℚ_[p]]
      TateModule.rational p (Additive (Scheme.geometricPointOver L y ⟶ A.X)) :=
  LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ (integralTateGeometricPathEquiv K L e A p)

/-- Rational path transport fixes coefficients and transports integral Tate vectors. -/
@[simp] theorem rationalTateGeometricPathEquiv_tmul (c : ℚ_[p])
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    rationalTateGeometricPathEquiv K L e A p (c ⊗ₜ v) =
      c ⊗ₜ integralTateGeometricPathEquiv K L e A p v := rfl

end AlgebraicGeometry.GroupScheme
