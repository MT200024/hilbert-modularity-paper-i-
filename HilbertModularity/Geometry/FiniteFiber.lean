/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.RationalPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Finite geometric fibres

A finite scheme over a field has finitely many rational points. The universal
property of a scheme pullback identifies sections of the geometric fibre with
morphisms over the original base. These statements supply finite fibres for
finite étale covers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.RationalPoint

universe u
variable (K : Type u) [Field K] {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A finite scheme over a field has finitely many rational points. -/
instance finite_of_isFinite (f : X ⟶ Spec (CommRingCat.of K)) [IsFinite f] :
    Finite (Scheme.RationalPoint f) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let R : CommRingCat := Γ(X, ⊤)
  let a : CommRingCat.of K ⟶ R := Spec.preimage (X.isoSpec.inv ≫ f)
  let : Algebra K R := a.hom.toAlgebra
  have ha : Spec.map (CommRingCat.ofHom (algebraMap K R)) = X.isoSpec.inv ≫ f :=
    Spec.map_preimage _
  have hf : a.hom.Finite := by
    rw [← IsFinite.SpecMap_iff]
    change IsFinite (Spec.map (Spec.preimage (X.isoSpec.inv ≫ f)))
    rw [Spec.map_preimage]
    infer_instance
  have : Module.Finite K R := hf
  have : Finite (R →ₐ[K] K) := inferInstance
  have : Finite (Scheme.RationalPoint (Spec.map (CommRingCat.ofHom (algebraMap K R)))) :=
    Finite.of_equiv (R →ₐ[K] K) (Scheme.affineRationalPointEquiv K R).symm
  have hi : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) = f := by
    rw [ha, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact Finite.of_injective (map X.isoSpec.hom hi) (map_injective X.isoSpec.hom hi)

set_option backward.isDefEq.respectTransparency false in
/-- Sections of a geometric fibre are precisely morphisms over the original base. -/
def pullbackEquiv (f : X ⟶ S) (x : Spec (CommRingCat.of K) ⟶ S) :
    (Over.mk x ⟶ Over.mk f) ≃ Scheme.RationalPoint (pullback.snd f x) where
  toFun y := ⟨pullback.lift (f := f) (g := x) y.left (𝟙 _) (by simpa using y.w),
    pullback.lift_snd _ _ _⟩
  invFun y := Over.homMk (y.val ≫ pullback.fst f x) (by
    change (y.val ≫ pullback.fst f x) ≫ f = x
    rw [Category.assoc, pullback.condition, ← Category.assoc, y.property, Category.id_comp])
  left_inv y := by
    apply Over.OverMorphism.ext
    simp
  right_inv y := by
    apply Subtype.ext
    apply pullback.hom_ext <;> simp [y.property]

/-- A finite cover has a finite geometric fibre at every field-valued point. -/
theorem finite_geometricFiber (f : X ⟶ S) [IsFinite f]
    (x : Spec (CommRingCat.of K) ⟶ S) : Finite (Over.mk x ⟶ Over.mk f) :=
  Finite.of_equiv (Scheme.RationalPoint (pullback.snd f x)) (pullbackEquiv K f x).symm

end AlgebraicGeometry.Scheme.RationalPoint
