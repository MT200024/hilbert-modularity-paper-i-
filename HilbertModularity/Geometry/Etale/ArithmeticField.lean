/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GeometricField
public import HilbertModularity.Geometry.Etale.FiberGroupoid

/-! # Arithmetic fibres over a larger parameter field

An embedding of the original algebraic closure into the new one identifies the
finite étale fibre functors. Conjugating the original arithmetic action then
gives loops at the same point viewed over the larger parameter field.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme
universe u
variable (E K : Type u) [Field E] [Field K] [Algebra E K]
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)
  (j : AlgebraicClosure E →ₐ[E] AlgebraicClosure K)

/-- An embedding of algebraic closures identifies the two geometric points over the same base. -/
theorem geometricPointOver_fieldExtension :
    Spec.map (CommRingCat.ofHom j.toRingHom) ≫ (geometricPointOver E x).hom =
      (geometricPointOver K (Spec.algebraMap E K ≫ x)).hom := by
  have hj : CommRingCat.ofHom (algebraMap E (AlgebraicClosure E)) ≫
        CommRingCat.ofHom j.toRingHom =
      CommRingCat.ofHom (algebraMap E K) ≫
        CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    ext a
    exact (j.commutes a).trans (IsScalarTower.algebraMap_apply E K (AlgebraicClosure K) a)
  change Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap E (AlgebraicClosure E))) ≫ x) =
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap E K)) ≫ x)
  rw [← Category.assoc, ← AlgebraicGeometry.Spec.map_comp, hj,
    AlgebraicGeometry.Spec.map_comp, Category.assoc]

/-- Extending the parameter field identifies the actual arithmetic fibre functors,
for a specified embedding of algebraic closures. Such an embedding exists by `IsAlgClosed.lift`. -/
def arithmeticFiberFieldIso : finiteArithmeticFiberFunctor E x ≅
    finiteArithmeticFiberFunctor K (Spec.algebraMap E K ≫ x) := by
  let : Algebra (AlgebraicClosure E) (AlgebraicClosure K) := j.toRingHom.toAlgebra
  let i : Over.mk (Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      (geometricPointOver E x).hom) ≅
      geometricPointOver K (Spec.algebraMap E K ≫ x) :=
    Over.isoMk (Iso.refl _) ((Category.id_comp _).trans
      (geometricPointOver_fieldExtension E K x j).symm)
  let η := finiteEtaleFiberFieldMap (AlgebraicClosure E) (geometricPointOver E x).hom
    (AlgebraicClosure K) j.toRingHom
  let e (X : S.FiniteEtale) :=
    (Equiv.ofBijective (η.app X)
      (finiteEtaleFiberFieldMap_bijective (AlgebraicClosure E) (AlgebraicClosure K)
        (geometricPointOver E x).hom X)).trans
      (i.homCongr (Iso.refl ((Etale.forget S).obj X.obj)))
  refine NatIso.ofComponents (fun X => FintypeCat.equivEquivIso (e X)) ?_
  intro X Y f
  apply FintypeCat.hom_ext
  intro v
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ ((Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      (v.left ≫ ((Etale.forget S).map f.hom).left)) ≫ 𝟙 _) =
    (𝟙 _ ≫ ((Spec.map (CommRingCat.ofHom j.toRingHom) ≫ v.left) ≫ 𝟙 _)) ≫
      ((Etale.forget S).map f.hom).left
  simp only [Category.id_comp, Category.comp_id, Category.assoc]

/-- The arithmetic fibre comparison is the original spectrum map on every finite cover. -/
@[simp]
theorem arithmeticFiberFieldIso_hom_app_left (X : S.FiniteEtale)
    (v : (finiteArithmeticFiberFunctor E x).obj X) :
    ((arithmeticFiberFieldIso E K x j).hom.app X v).left =
      Spec.map (CommRingCat.ofHom j.toRingHom) ≫ v.left := by
  change 𝟙 _ ≫ ((Spec.map (CommRingCat.ofHom j.toRingHom) ≫ v.left) ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- The original arithmetic Galois group acts on the fibre over the larger parameter field. -/
def galoisToEtaleFundamentalGroupOverField :
    (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) →*
      etaleFundamentalGroup K (Spec.algebraMap E K ≫ x) :=
  (arithmeticFiberFieldIso E K x j).conjAut.toMonoidHom.comp
    (galoisToEtaleFundamentalGroup E x)

/-- The transported arithmetic action is continuous for the actual profinite fibre topology. -/
theorem continuous_galoisToEtaleFundamentalGroupOverField :
    Continuous (galoisToEtaleFundamentalGroupOverField E K x j) :=
  (PreGaloisCategory.continuous_conjAut (arithmeticFiberFieldIso E K x j)).comp
    (continuous_galoisToEtaleFundamentalGroup E x)

/-- Arithmetic automorphisms of the original field give loops in the common parameter-field groupoid. -/
def arithmeticFiberLoopOverField (g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
    etaleFiberPoint K S (Spec.algebraMap E K ≫ x) ⟶
      etaleFiberPoint K S (Spec.algebraMap E K ≫ x) :=
  etaleFiberPath K S (galoisToEtaleFundamentalGroupOverField E K x j g)

/-- The field-comparison isomorphism intertwines the original and transported arithmetic actions. -/
theorem arithmeticFiberFieldIso_galois
    (g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
    (arithmeticFiberFieldIso E K x j).hom ≫
        (galoisToEtaleFundamentalGroupOverField E K x j g).hom =
      (galoisToEtaleFundamentalGroup E x g).hom ≫ (arithmeticFiberFieldIso E K x j).hom := by
  change (arithmeticFiberFieldIso E K x j).hom ≫
      ((arithmeticFiberFieldIso E K x j).conjAut
        (galoisToEtaleFundamentalGroup E x g)).hom = _
  change (arithmeticFiberFieldIso E K x j).hom ≫
      ((arithmeticFiberFieldIso E K x j).inv ≫
        (galoisToEtaleFundamentalGroup E x g).hom ≫
        (arithmeticFiberFieldIso E K x j).hom) = _
  exact (arithmeticFiberFieldIso E K x j).hom_inv_id_assoc _

end AlgebraicGeometry.Scheme
