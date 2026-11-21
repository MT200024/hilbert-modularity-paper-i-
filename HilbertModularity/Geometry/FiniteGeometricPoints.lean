/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.AffinePoints
public import HilbertModularity.Geometry.FiniteFiber
public import Mathlib.CategoryTheory.HomCongr

/-! # Finite scheme points after extending a geometric field

Finite schemes are affine. Their finite coordinate algebras show that an
extension of an algebraically closed geometric field does not change their points.
-/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme
universe u
variable (k Ω Ω' : Type u) [Field k] [Field Ω] [IsAlgClosed Ω] [Field Ω']
  [Algebra k Ω] [Algebra k Ω'] [Algebra Ω Ω'] [IsScalarTower k Ω Ω']

set_option backward.isDefEq.respectTransparency false in
/-- Enlarging a closed geometric field does not change the points of a finite scheme. -/
theorem bijective_precomp_fieldExtension_of_isFinite {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] :
    Function.Bijective (fun y : Over.mk (Spec.algebraMap k Ω) ⟶ Over.mk f =>
      (Spec.overHomEquivAlgHom k Ω Ω').symm (IsScalarTower.toAlgHom k Ω Ω') ≫ y) := by
  let : IsAffine X := isAffine_of_isAffineHom f
  let A : CommRingCat := Γ(X, ⊤)
  let a : CommRingCat.of k ⟶ A := Spec.preimage (X.isoSpec.inv ≫ f)
  let : Algebra k A := a.hom.toAlgebra
  have ha : Spec.algebraMap k A = X.isoSpec.inv ≫ f := Spec.map_preimage _
  have hf : a.hom.Finite := by
    rw [← IsFinite.SpecMap_iff]
    change IsFinite (Spec.map (Spec.preimage (X.isoSpec.inv ≫ f)))
    rw [Spec.map_preimage]
    infer_instance
  let : Module.Finite k A := hf
  let e : Over.mk f ≅ Over.mk (Spec.algebraMap k A) := Over.isoMk X.isoSpec (by
    change X.isoSpec.hom ≫ Spec.algebraMap k A = f
    rw [ha, ← Category.assoc, Iso.hom_inv_id, Category.id_comp])
  let eΩ := (Iso.refl (Over.mk (Spec.algebraMap k Ω))).homCongr e
  let eΩ' := (Iso.refl (Over.mk (Spec.algebraMap k Ω'))).homCongr e
  have h := (Spec.bijective_precomp_of_isAlgClosed k A Ω Ω').comp eΩ.bijective
  have h' := eΩ'.symm.bijective.comp h
  convert h' using 1
  funext y
  apply eΩ'.injective
  have hnat : eΩ' ((Spec.overHomEquivAlgHom k Ω Ω').symm
      (IsScalarTower.toAlgHom k Ω Ω') ≫ y) =
        (Spec.overHomEquivAlgHom k Ω Ω').symm (IsScalarTower.toAlgHom k Ω Ω') ≫ eΩ y := by
    change 𝟙 _ ≫ (_ ≫ y) ≫ e.hom = _ ≫ (𝟙 _ ≫ y ≫ e.hom)
    simp only [Category.id_comp, Category.assoc]
  exact hnat.trans (eΩ'.apply_symm_apply _).symm

end AlgebraicGeometry.Scheme
