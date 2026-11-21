/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GeometricFiber
public import Mathlib.RingTheory.Etale.Finite

/-! # Finite étale covers of an affine scheme

Taking spectra identifies finite étale algebras over a commutative ring with
finite étale covers of its spectrum. No field hypothesis is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
universe u
variable (K : Type u) [CommRing K]

set_option backward.isDefEq.respectTransparency false in
/-- The spectrum of a finite étale algebra is an actual finite étale cover. -/
def finiteEtaleAlgebraCover (A : CommAlgCat.FiniteEtale.{u} K) :
    (Spec (CommRingCat.of K)).FiniteEtale := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K A))
  have : AlgebraicGeometry.Etale f := by
    change AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap K A)))
    apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
    exact RingHom.etale_algebraMap.mpr inferInstance
  refine ⟨Scheme.Etale.mk f, ?_⟩
  change IsFinite f
  rw [IsFinite.SpecMap_iff]
  change (algebraMap K A).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- An algebra homomorphism induces the corresponding morphism of finite étale covers. -/
def finiteEtaleAlgebraMap {A B : CommAlgCat.FiniteEtale.{u} K} (φ : A.obj →ₐ[K] B.obj) :
    finiteEtaleAlgebraCover K B ⟶ finiteEtaleAlgebraCover K A :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) =
          Spec.map (CommRingCat.ofHom (algebraMap K B))
      rw [← Spec.map_comp]
      congr 1
      ext a
      exact φ.commutes a))

set_option backward.isDefEq.respectTransparency false in
/-- The contravariant spectrum functor on actual finite étale algebras. -/
def finiteEtaleSpec : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ⥤
    (Spec (CommRingCat.of K)).FiniteEtale where
  obj A := finiteEtaleAlgebraCover K A.unop
  map f := finiteEtaleAlgebraMap K f.unop.hom.hom
  map_id A := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_id (CommRingCat.of A.unop.obj)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (f.unop.hom.hom.comp g.unop.hom.hom).toRingHom) =
      Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom)
    exact Spec.map_comp (CommRingCat.ofHom g.unop.hom.hom.toRingHom)
      (CommRingCat.ofHom f.unop.hom.hom.toRingHom)

set_option backward.isDefEq.respectTransparency false in
/-- Every finite étale cover of an affine scheme is the spectrum of a finite étale algebra. -/
instance finiteEtaleSpec_essSurj : (finiteEtaleSpec K).EssSurj where
  mem_essImage X := by
    let f : X.obj.left ⟶ Spec (CommRingCat.of K) := X.obj.hom
    have : IsFinite f := X.property
    have : AlgebraicGeometry.Etale f := X.obj.prop
    let : IsAffine X.obj.left := isAffine_of_isAffineHom f
    let R : CommRingCat := Γ(X.obj.left, ⊤)
    let a : CommRingCat.of K ⟶ R :=
      Spec.preimage (X.obj.left.isoSpec.inv ≫ f)
    let : Algebra K R := a.hom.toAlgebra
    have hs : Spec.map (CommRingCat.ofHom (algebraMap K R)) =
        X.obj.left.isoSpec.inv ≫ f := Spec.map_preimage _
    have hf : a.hom.Finite := by
      rw [← IsFinite.SpecMap_iff]
      change IsFinite (Spec.map (Spec.preimage (X.obj.left.isoSpec.inv ≫ f)))
      rw [Spec.map_preimage]
      infer_instance
    let : Module.Finite K R := hf
    have he : a.hom.Etale := by
      apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp
      change AlgebraicGeometry.Etale
        (Spec.map (Spec.preimage (X.obj.left.isoSpec.inv ≫ f)))
      rw [Spec.map_preimage]
      infer_instance
    let : Algebra.Etale K R := RingHom.etale_algebraMap.mp he
    let A := CommAlgCat.FiniteEtale.of K R
    refine ⟨op A, ⟨ObjectProperty.isoMk _
      (MorphismProperty.Over.isoMk X.obj.left.isoSpec.symm ?_)⟩⟩
    exact hs.symm


set_option backward.isDefEq.respectTransparency false in
/-- Morphisms of affine finite étale covers come from algebra homomorphisms. -/
instance finiteEtaleSpec_full : (finiteEtaleSpec K).Full where
  map_surjective {A B} f := by
    let φ : B.unop.obj →ₐ[K] A.unop.obj :=
      { __ := (Spec.preimage f.hom.left).hom
        commutes' r := by
          have hr : CommRingCat.ofHom (algebraMap K B.unop.obj) ≫ Spec.preimage f.hom.left =
              CommRingCat.ofHom (algebraMap K A.unop.obj) := by
            rw [← Spec.map_inj, Spec.map_comp, Spec.map_preimage]
            exact f.hom.w
          exact congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of A.unop.obj => h r) hr }
    refine ⟨(CommAlgCat.FiniteEtale.ofHom φ).op, ?_⟩
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_preimage f.hom.left

set_option backward.isDefEq.respectTransparency false in
/-- The spectrum construction detects every homomorphism of finite étale algebras. -/
instance finiteEtaleSpec_faithful : (finiteEtaleSpec K).Faithful where
  map_injective {A B} f g h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    have he := congrArg (fun k => k.hom.left) h
    change Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) at he
    rw [Spec.map_inj] at he
    exact congrArg (fun k : CommRingCat.of B.unop.obj ⟶ CommRingCat.of A.unop.obj => k a) he

/-- The finite étale spectrum functor is an equivalence of categories. -/
instance finiteEtaleSpec_isEquivalence : (finiteEtaleSpec K).IsEquivalence where

/-- Finite étale algebras and finite étale covers of the affine spectrum are
contravariantly equivalent. -/
def finiteEtaleSpecEquivalence : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌
    (Spec (CommRingCat.of K)).FiniteEtale := (finiteEtaleSpec K).asEquivalence

end AlgebraicGeometry.Scheme
