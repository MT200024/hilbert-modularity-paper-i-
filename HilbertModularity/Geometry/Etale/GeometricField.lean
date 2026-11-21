/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.GaloisAction
public import HilbertModularity.Geometry.Etale.GeometricFiber
public import HilbertModularity.Geometry.FiniteGeometricPoints
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Geometric field extension on finite étale covers

Pulling a finite cover back to the geometric point reduces its field-extension
map to the finite-scheme comparison over that algebraically closed field.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme
universe u
variable (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [Algebra Ω Ω']
  {S : Scheme.{u}} (x : Spec (CommRingCat.of Ω) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- Extending an algebraically closed geometric point is bijective on every finite étale fibre. -/
theorem finiteEtaleFiberFieldMap_bijective (X : S.FiniteEtale) :
    Function.Bijective ((finiteEtaleFiberFieldMap Ω x Ω' (algebraMap Ω Ω')).app X) := by
  let Y : Over S := (Etale.forget S).obj X.obj
  let A := Over.mk (Spec.algebraMap Ω Ω)
  let B := Over.mk (Spec.algebraMap Ω Ω')
  let q : B ⟶ A := (Spec.overHomEquivAlgHom Ω Ω Ω').symm
    (IsScalarTower.toAlgHom Ω Ω Ω')
  let P := (Over.pullback x).obj Y
  let : IsFinite P.hom := by
    change IsFinite (pullback.snd X.obj.hom x)
    infer_instance
  have h : Function.Bijective (fun y : A ⟶ P => q ≫ y) :=
    bijective_precomp_fieldExtension_of_isFinite Ω Ω Ω' P.hom
  let adj := Over.mapPullbackAdj x
  let eA := adj.homEquiv A Y
  let eB := adj.homEquiv B Y
  have hb : Function.Bijective (fun y : (Over.map x).obj A ⟶ Y =>
      (Over.map x).map q ≫ y) := by
    have hh := eB.symm.bijective.comp (h.comp eA.bijective)
    convert hh using 1
    funext y
    apply eB.injective
    exact (adj.homEquiv_naturality_left q y).trans (eB.apply_symm_apply _).symm
  have hq : q = Over.homMk (U := B) (V := A) (Spec.algebraMap Ω Ω')
      (by simp [A, B, Spec.algebraMap, Algebra.algebraMap_self]) := by
    apply Over.OverMorphism.ext
    exact Spec.overHomEquivAlgHom_symm_left Ω Ω Ω' _
  rw [hq] at hb
  let i : (Over.map x).obj A ≅ Over.mk x :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ x = Spec.algebraMap Ω Ω ≫ x
      simp [Spec.algebraMap, Algebra.algebraMap_self])
  have hh := hb.comp (i.homCongr (Iso.refl Y)).symm.bijective
  change Function.Bijective (fun y : Over.mk x ⟶ Y =>
    (Over.homMk (U := Over.mk (Spec.algebraMap Ω Ω' ≫ x)) (V := Over.mk x)
      (Spec.algebraMap Ω Ω') rfl) ≫ y)
  convert hh using 1
  · rfl
  · funext y
    apply Over.OverMorphism.ext
    change Spec.algebraMap Ω Ω' ≫ y.left =
      Spec.algebraMap Ω Ω' ≫ (𝟙 _ ≫ y.left ≫ 𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

/-- The actual field-extension map is a natural isomorphism of finite étale fibre functors. -/
def finiteEtaleFiberFieldIso : finiteEtaleFiberFunctor Ω x ≅
    finiteEtaleFiberFunctor Ω' (Spec.algebraMap Ω Ω' ≫ x) := by
  let η := finiteEtaleFiberFieldMap Ω x Ω' (algebraMap Ω Ω')
  exact NatIso.ofComponents
    (fun X => FintypeCat.equivEquivIso (Equiv.ofBijective (η.app X)
      (finiteEtaleFiberFieldMap_bijective Ω Ω' x X)))
    (fun {_X _Y} f => η.naturality f)

/-- The natural isomorphism is the original field-extension map on all covers. -/
@[simp]
theorem finiteEtaleFiberFieldIso_hom :
    (finiteEtaleFiberFieldIso Ω Ω' x).hom =
      finiteEtaleFiberFieldMap Ω x Ω' (algebraMap Ω Ω') := rfl

/-- Extension of the geometric field preserves the profinite fibre-automorphism group. -/
def finiteEtaleFiberAutFieldEquiv : Aut (finiteEtaleFiberFunctor Ω x) ≃ₜ*
    Aut (finiteEtaleFiberFunctor Ω' (Spec.algebraMap Ω Ω' ≫ x)) :=
  let e := finiteEtaleFiberFieldIso Ω Ω' x
  { e.conjAut with
    continuous_toFun := PreGaloisCategory.continuous_conjAut e
    continuous_invFun := PreGaloisCategory.continuous_conjAut e.symm }

end AlgebraicGeometry.Scheme
