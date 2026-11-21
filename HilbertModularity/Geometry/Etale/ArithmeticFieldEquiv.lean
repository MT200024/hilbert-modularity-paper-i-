/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiberGroupoid
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import HilbertModularity.FieldTheory.Galois.FieldEquiv

/-! # Arithmetic fibres under a change of field coordinates

A field isomorphism extends to a chosen isomorphism of its algebraic closures.
The spectrum map identifies the actual geometric points and hence their finite
étale fibres. This retains the semilinear meaning of a generic parameter change.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.Scheme
universe u
variable (E K : Type u) [Field E] [Field K] (σ : E ≃+* K)
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)

/-- The chosen algebraic-closure extension of a field isomorphism identifies the geometric points. -/
theorem geometricPointOver_fieldEquiv :
    Spec.map (CommRingCat.ofHom
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ).toRingHom) ≫
        (geometricPointOver E x).hom =
      (geometricPointOver K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)).hom := by
  have h : CommRingCat.ofHom (algebraMap E (AlgebraicClosure E)) ≫
      CommRingCat.ofHom
        (IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ).toRingHom =
        CommRingCat.ofHom σ.toRingHom ≫
          CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    ext a
    exact IsAlgClosure.equivOfEquiv_algebraMap _ _ σ a
  simp only [geometricPointOver_hom, ← Category.assoc, ← Spec.map_comp, h]

/-- A field-coordinate isomorphism gives an actual isomorphism of geometric points over the scheme. -/
def arithmeticGeometricPointFieldEquiv :
    geometricPointOver K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) ≅
      geometricPointOver E x :=
  Over.isoMk
    (Scheme.Spec.mapIso
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ).toCommRingCatIso.op)
    (geometricPointOver_fieldEquiv E K σ x)

/-- The actual finite étale fibre functors are isomorphic under a change of field coordinates. -/
def arithmeticFiberFieldEquivIso : finiteArithmeticFiberFunctor E x ≅
    finiteArithmeticFiberFunctor K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) := by
  let e := arithmeticGeometricPointFieldEquiv E K σ x
  refine NatIso.ofComponents (fun Y => FintypeCat.equivEquivIso
    (e.symm.homCongr (Iso.refl ((Etale.forget S).obj Y.obj)))) ?_
  intro Y Z f
  apply FintypeCat.hom_ext
  intro v
  change e.hom ≫ ((v ≫ (Etale.forget S).map f.hom) ≫ 𝟙 _) =
    (e.hom ≫ (v ≫ 𝟙 _)) ≫ (Etale.forget S).map f.hom
  simp only [Category.comp_id, Category.assoc]
  exact congrArg (fun w => e.hom ≫ w ≫ (Etale.forget S).map f.hom)
    (Category.comp_id v).symm

/-- The finite-cover comparison is precomposition with the actual closure spectrum map. -/
@[simp]
theorem arithmeticFiberFieldEquivIso_hom_app_left (Y : S.FiniteEtale)
    (v : (finiteArithmeticFiberFunctor E x).obj Y) :
    ((arithmeticFiberFieldEquivIso E K σ x).hom.app Y v).left =
      Spec.map (CommRingCat.ofHom
        (IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ).toRingHom) ≫
          v.left := by
  change ((arithmeticGeometricPointFieldEquiv E K σ x).hom ≫ (v ≫ 𝟙 _)).left = _
  rfl

/-- The finite-cover comparison intertwines the original and conjugate arithmetic Galois actions. -/
theorem arithmeticFiberFieldEquivIso_galois
    (g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
    (arithmeticFiberFieldEquivIso E K σ x).hom ≫
        (galoisToEtaleFundamentalGroup K
          (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
          (AlgebraicClosure.galoisFieldEquiv E K σ g)).hom =
      (galoisToEtaleFundamentalGroup E x g).hom ≫
        (arithmeticFiberFieldEquivIso E K σ x).hom := by
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro v
  apply Over.OverMorphism.ext
  let j := IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ
  have hj : CommRingCat.ofHom j.toRingHom ≫
      CommRingCat.ofHom (AlgebraicClosure.galoisFieldEquiv E K σ g).toRingHom =
        CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom j.toRingHom := by
    ext a
    exact AlgebraicClosure.galoisFieldEquiv_intertwines E K σ g a
  change Spec.map (CommRingCat.ofHom
      (AlgebraicClosure.galoisFieldEquiv E K σ g).toRingHom) ≫
      ((arithmeticFiberFieldEquivIso E K σ x).hom.app Y v).left =
    ((arithmeticFiberFieldEquivIso E K σ x).hom.app Y
      ((galoisToEtaleFundamentalGroup E x g).hom.app Y v)).left
  rw [arithmeticFiberFieldEquivIso_hom_app_left, arithmeticFiberFieldEquivIso_hom_app_left]
  change Spec.map (CommRingCat.ofHom
      (AlgebraicClosure.galoisFieldEquiv E K σ g).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ v.left) =
    Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ v.left)
  rw [← Category.assoc, ← Spec.map_comp, hj, Spec.map_comp, Category.assoc]

/-- The actual fibre-automorphism conjugation carries arithmetic loops to the native
Galois automorphisms transported by the field-coordinate isomorphism. -/
theorem arithmeticFiberFieldEquivIso_conj_galois
    (g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
    (arithmeticFiberFieldEquivIso E K σ x).conjAut
        (galoisToEtaleFundamentalGroup E x g) =
      galoisToEtaleFundamentalGroup K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
        (AlgebraicClosure.galoisFieldEquiv E K σ g) := by
  apply Iso.ext
  apply (cancel_epi (arithmeticFiberFieldEquivIso E K σ x).hom).mp
  change (arithmeticFiberFieldEquivIso E K σ x).hom ≫
      ((arithmeticFiberFieldEquivIso E K σ x).inv ≫
        (galoisToEtaleFundamentalGroup E x g).hom ≫
          (arithmeticFiberFieldEquivIso E K σ x).hom) = _
  rw [(arithmeticFiberFieldEquivIso E K σ x).hom_inv_id_assoc]
  exact (arithmeticFiberFieldEquivIso_galois E K σ x g).symm

end AlgebraicGeometry.Scheme
