/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GroupFiber
public import HilbertModularity.Geometry.Etale.GeometricPathGroup

/-! # Transporting finite étale group fibres between different geometric fields -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory finiteEtaleBraidedCategory
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor L y)

/-- A geometric path over possibly different fields transports actual finite group fibres. -/
def finiteGroupFiberGeometricPathIso :
    finiteGroupFiberFunctor K x ≅ finiteGroupFiberFunctor L y :=
  Functor.isoWhiskerRight
    (Functor.mapCommGrpNatIso (show finiteGeometricFiberFunctor K x ≅
      finiteGeometricFiberFunctor L y from
        Functor.isoWhiskerRight e (CategoryTheory.forget FintypeCat)))
    commGrpTypeEquivalenceCommGrp.functor

/-- Group transport is the given path on the underlying finite cover. -/
@[simp] theorem finiteGroupFiberGeometricPathIso_apply
    (A : CommGrp S.FiniteEtale) (v : (finiteGroupFiberFunctor K x).obj A) :
    (finiteGroupFiberGeometricPathIso K L e).hom.app A v = e.hom.app A.X v := rfl

/-- The group path intertwines monodromy after the actual fundamental-group conjugation. -/
theorem finiteGroupFiberGeometricPathIso_smul
    (A : CommGrp S.FiniteEtale) (σ : etaleFundamentalGroup K x)
    (v : (finiteGroupFiberFunctor K x).obj A) :
    (finiteGroupFiberGeometricPathIso K L e).hom.app A (σ.hom.app A.X v) =
      (geometricFiberPathGroupEquiv K L e σ).hom.app A.X
        ((finiteGroupFiberGeometricPathIso K L e).hom.app A v) := by
  change e.hom.app A.X (σ.hom.app A.X v) =
    e.hom.app A.X (σ.hom.app A.X (e.inv.app A.X (e.hom.app A.X v)))
  have h := ConcreteCategory.congr_hom (e.hom_inv_id_app A.X) v
  change e.inv.app A.X (e.hom.app A.X v) = v at h
  rw [h]

end AlgebraicGeometry.Scheme
