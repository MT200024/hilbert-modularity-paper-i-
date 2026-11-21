/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateGeometricPath

/-! # Continuity of Tate transport along actual geometric paths -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  [TopologicalSpace (Additive (Scheme.geometricPointOver K x ⟶ A.X))]
  [TopologicalSpace (Additive (Scheme.geometricPointOver L y ⟶ A.X))]
  [DiscreteTopology (Additive (Scheme.geometricPointOver K x ⟶ A.X))]

/-- Integral geometric path transport is continuous for the ordinary inverse-limit topology. -/
theorem continuous_integralTateGeometricPathEquiv :
    Continuous (integralTateGeometricPathEquiv K L e A p) :=
  TateModule.continuous_mapOfTorsion p (torsionGeometricPathLinearMap K L e A p)
    (torsionGeometricPathLinearMap_transition K L e A p) (fun _ => continuous_of_discreteTopology)

/-- Rational geometric path transport is continuous for the ordinary rational Tate topology. -/
theorem continuous_rationalTateGeometricPathEquiv :
    Continuous (rationalTateGeometricPathEquiv K L e A p) :=
  TateModule.continuous_baseChange_map p (integralTateGeometricPathEquiv K L e A p).toLinearMap
    (continuous_integralTateGeometricPathEquiv K L e A p)

variable [DiscreteTopology (Additive (Scheme.geometricPointOver L y ⟶ A.X))]

/-- An actual geometric path identifies the topological integral Tate modules. -/
def integralTateGeometricPathContinuousEquiv :
    TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) ≃L[ℤ_[p]]
      TateModule.integral p (Additive (Scheme.geometricPointOver L y ⟶ A.X)) where
  __ := integralTateGeometricPathEquiv K L e A p
  continuous_toFun := continuous_integralTateGeometricPathEquiv K L e A p
  continuous_invFun := continuous_integralTateGeometricPathEquiv L K e.symm A p

/-- An actual geometric path identifies the topological rational Tate modules. -/
def rationalTateGeometricPathContinuousEquiv :
    TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) ≃L[ℚ_[p]]
      TateModule.rational p (Additive (Scheme.geometricPointOver L y ⟶ A.X)) where
  __ := rationalTateGeometricPathEquiv K L e A p
  continuous_toFun := continuous_rationalTateGeometricPathEquiv K L e A p
  continuous_invFun := continuous_rationalTateGeometricPathEquiv L K e.symm A p

end AlgebraicGeometry.GroupScheme
