/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GeometricFiberPath
public import HilbertModularity.Geometry.Etale.ArithmeticFieldTopology

/-! # Fundamental groups along geometric paths over different fields -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
variable {S : Scheme.{u}} (K L : Type u) [Field K] [Field L]
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor L y)

/-- An actual path identifies profinite fundamental groups even when its
geometric points are constructed from different residue fields. -/
def geometricFiberPathGroupEquiv :
    etaleFundamentalGroup K x ≃ₜ* etaleFundamentalGroup L y :=
  { e.conjAut with
    continuous_toFun := PreGaloisCategory.continuous_conjAut e
    continuous_invFun := PreGaloisCategory.continuous_conjAut e.symm }

/-- The arithmetic loops at the second point transported to the first geometric fibre. -/
def galoisAlongGeometricFiberPath :
    (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) →ₜ* etaleFundamentalGroup K x :=
  ((geometricFiberPathGroupEquiv K L e).symm :
    etaleFundamentalGroup L y →ₜ* etaleFundamentalGroup K x).comp
      (continuousGaloisToEtaleFundamentalGroup L y)

/-- Transporting arithmetic loops back along the path recovers the actual arithmetic action. -/
@[simp] theorem geometricFiberPathGroupEquiv_galoisAlong
    (g : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    geometricFiberPathGroupEquiv K L e (galoisAlongGeometricFiberPath K L e g) =
      galoisToEtaleFundamentalGroup L y g :=
  (geometricFiberPathGroupEquiv K L e).apply_symm_apply _

end AlgebraicGeometry.Scheme
