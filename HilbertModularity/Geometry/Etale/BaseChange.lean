/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Affine
public import HilbertModularity.Geometry.Etale.Pullback

/-! # Algebraic base change and pullback of finite étale covers

The spectrum of the scalar-extended algebra is the actual pullback cover.
The comparison uses the standard tensor-product description of affine pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of an affine finite étale cover is the spectrum of its base-changed algebra. -/
def finiteEtaleSpecBaseChangeObjIso (A : CommAlgCat.FiniteEtale.{u} R) :
    (finiteEtalePullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
        (finiteEtaleAlgebraCover R A) ≅
      finiteEtaleAlgebraCover S ((CommAlgCat.FiniteEtale.baseChange R S).obj A) :=
  ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk
    (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R S A) (by
      change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R S A).hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) = _
      rw [Category.assoc, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]
      rfl))

set_option backward.isDefEq.respectTransparency false in
/-- The algebraic base-change comparison preserves the projection to the original cover. -/
@[reassoc]
theorem finiteEtaleSpecBaseChangeObjIso_hom_fst (A : CommAlgCat.FiniteEtale.{u} R) :
    (finiteEtaleSpecBaseChangeObjIso R S A).hom.hom.left ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R S A).hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (pullbackSymmetry _ _).hom ≫ f)
      (pullbackSpecIso_hom_snd R S A)).trans (pullbackSymmetry_hom_comp_snd _ _))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison preserves the original-cover projection as well. -/
@[reassoc]
theorem finiteEtaleSpecBaseChangeObjIso_inv_fst (A : CommAlgCat.FiniteEtale.{u} R) :
    (finiteEtaleSpecBaseChangeObjIso R S A).inv.hom.left ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) := by
  rw [← finiteEtaleSpecBaseChangeObjIso_hom_fst R S A, ← Category.assoc]
  have h := congrArg (fun f => f.hom.left) (finiteEtaleSpecBaseChangeObjIso R S A).inv_hom_id
  change (finiteEtaleSpecBaseChangeObjIso R S A).inv.hom.left ≫
    (finiteEtaleSpecBaseChangeObjIso R S A).hom.hom.left = 𝟙 _ at h
  rw [h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison between algebraic base change and pullback is natural in the cover. -/
def finiteEtaleSpecBaseChangeIso :
    finiteEtaleSpec R ⋙ finiteEtalePullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
      (CommAlgCat.FiniteEtale.baseChange R S).op ⋙ finiteEtaleSpec S :=
  NatIso.ofComponents (fun A => finiteEtaleSpecBaseChangeObjIso R S A.unop) (by
    intro A B f
    apply (cancel_mono (finiteEtaleSpecBaseChangeObjIso R S B.unop).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change (pullback.lift _ _ _) ≫ _ =
        ((finiteEtaleSpecBaseChangeObjIso R S A.unop).hom.hom.left ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom).toRingHom) ≫
          (finiteEtaleSpecBaseChangeObjIso R S B.unop).inv.hom.left) ≫
            pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B.unop.obj)))
              (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      rw [pullback.lift_fst, Category.assoc, Category.assoc,
        finiteEtaleSpecBaseChangeObjIso_inv_fst, ← Spec.map_comp]
      have h : CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
            B.unop.obj →ₐ[R] S ⊗[R] B.unop.obj).toRingHom ≫
          CommRingCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom).toRingHom =
          CommRingCat.ofHom f.unop.hom.hom.toRingHom ≫
            CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              A.unop.obj →ₐ[R] S ⊗[R] A.unop.obj).toRingHom := by
        ext a
        change Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom
          ((1 : S) ⊗ₜ[R] a) = (1 : S) ⊗ₜ[R] f.unop.hom.hom a
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [h, Spec.map_comp, ← Category.assoc, finiteEtaleSpecBaseChangeObjIso_hom_fst]
      rfl
    · change (pullback.lift _ _ _) ≫ _ =
        ((finiteEtaleSpecBaseChangeObjIso R S A.unop).hom.hom.left ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom).toRingHom) ≫
          (finiteEtaleSpecBaseChangeObjIso R S B.unop).inv.hom.left) ≫
            pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B.unop.obj)))
              (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      have hi : (finiteEtaleSpecBaseChangeObjIso R S B.unop).inv.hom.left ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B.unop.obj)))
            (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
          Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] B.unop.obj))) :=
        (finiteEtaleSpecBaseChangeObjIso R S B.unop).inv.hom.w
      rw [pullback.lift_snd, Category.assoc, Category.assoc,
        hi, ← Spec.map_comp]
      have h : CommRingCat.ofHom (algebraMap S (S ⊗[R] B.unop.obj)) ≫
          CommRingCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom).toRingHom =
          CommRingCat.ofHom (algebraMap S (S ⊗[R] A.unop.obj)) := by
        ext a
        exact (Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom).commutes a
      rw [h]
      exact (finiteEtaleSpecBaseChangeObjIso R S A.unop).hom.hom.w.symm)

end AlgebraicGeometry.Scheme
