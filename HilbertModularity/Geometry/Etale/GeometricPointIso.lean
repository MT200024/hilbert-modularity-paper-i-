/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GeometricFiber

/-! # Isomorphic geometric points give isomorphic finite étale fibres -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
variable (Ω Ω' : Type u) [Field Ω] [Field Ω'] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of Ω) ⟶ S) (y : Spec (CommRingCat.of Ω') ⟶ S)
  (e : Over.mk x ≅ Over.mk y)

/-- An isomorphism of geometric points acts by precomposition on every finite étale fibre. -/
def finiteEtaleFiberPointIso : finiteEtaleFiberFunctor Ω x ≅ finiteEtaleFiberFunctor Ω' y := by
  let a (Y : S.FiniteEtale) :
      (Over.mk x ⟶ (Etale.forget S).obj Y.obj) ≃
        (Over.mk y ⟶ (Etale.forget S).obj Y.obj) :=
    { toFun := fun v => e.inv ≫ v
      invFun := fun v => e.hom ≫ v
      left_inv := fun v => e.hom_inv_id_assoc v
      right_inv := fun v => e.inv_hom_id_assoc v }
  refine NatIso.ofComponents (fun Y => FintypeCat.equivEquivIso (a Y)) ?_
  intro Y Z f
  apply FintypeCat.hom_ext
  intro v
  exact (Category.assoc e.inv v ((Etale.forget S).map f.hom)).symm

/-- The fibre comparison uses the original point isomorphism on each actual cover. -/
@[simp]
theorem finiteEtaleFiberPointIso_hom_app (Y : S.FiniteEtale)
    (v : (finiteEtaleFiberFunctor Ω x).obj Y) :
    (finiteEtaleFiberPointIso Ω Ω' x y e).hom.app Y v = e.inv ≫ v := rfl

end AlgebraicGeometry.Scheme
