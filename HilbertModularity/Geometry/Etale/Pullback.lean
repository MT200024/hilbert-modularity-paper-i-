/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Continuity
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.HomCongr

/-! # Pullback of finite étale covers and geometric fibres

Actual base change preserves finite étale covers. The pullback adjunction
identifies the geometric fibre of a pulled-back cover with the fibre at the
composite geometric point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

universe u
variable {S T : Scheme.{u}} (f : S ⟶ T)

local instance finiteEtale_hasPullbacksAlong :
    MorphismProperty.HasPullbacksAlong (@AlgebraicGeometry.Etale) f where
  hasPullback _ _ := inferInstance

local instance finiteEtale_stableUnderBaseChangeAlong :
    MorphismProperty.IsStableUnderBaseChangeAlong (@AlgebraicGeometry.Etale) f where
  of_isPullback h hg := MorphismProperty.IsStableUnderBaseChange.of_isPullback h hg

set_option backward.isDefEq.respectTransparency false in
/-- Pull back actual finite étale covers along a scheme morphism. -/
def finiteEtalePullback : T.FiniteEtale ⥤ S.FiniteEtale :=
  ObjectProperty.lift (fun X : S.Etale => IsFinite X.hom)
    ((show ObjectProperty T.Etale from fun X => IsFinite X.hom).ι ⋙
      MorphismProperty.Over.pullback (@AlgebraicGeometry.Etale) ⊤ f) (fun X => by
        change IsFinite (Limits.pullback.snd X.obj.hom f)
        infer_instance)

variable (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S)

/-- The geometric point of a composite rational point is the mapped geometric point. -/
def geometricPointMapIso :
    (Over.map f).obj (geometricPointOver K x) ≅ geometricPointOver K (x ≫ f) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
      (x ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ x ≫ f
    simp only [Category.id_comp])

set_option backward.isDefEq.respectTransparency false in
/-- The pullback adjunction identifies the actual geometric fibres. -/
def finiteArithmeticFiberPullbackEquiv (Y : T.FiniteEtale) :
    (finiteArithmeticFiberFunctor K (x ≫ f)).obj Y ≃
      (finiteArithmeticFiberFunctor K x).obj ((finiteEtalePullback f).obj Y) :=
  (Iso.homCongr (geometricPointMapIso f K x).symm (Iso.refl _)).trans
    ((Over.mapPullbackAdj f).homEquiv (geometricPointOver K x)
      ((Etale.forget T).obj Y.obj))

set_option backward.isDefEq.respectTransparency false in
/-- Identification of pullback fibres is natural in the finite étale cover. -/
def finiteArithmeticFiberPullbackIso :
    finiteArithmeticFiberFunctor K (x ≫ f) ≅
      finiteEtalePullback f ⋙ finiteArithmeticFiberFunctor K x :=
  NatIso.ofComponents (fun Y => FintypeCat.equivEquivIso
    (finiteArithmeticFiberPullbackEquiv f K x Y)) (by
      intro Y Z h
      apply FintypeCat.hom_ext
      intro y
      change (finiteArithmeticFiberPullbackEquiv f K x Z)
          (y ≫ (Etale.forget T).map h.hom) =
        (finiteArithmeticFiberPullbackEquiv f K x Y y) ≫
          (Over.pullback f).map ((Etale.forget T).map h.hom)
      change (Over.mapPullbackAdj f).homEquiv _ _
          ((geometricPointMapIso f K x).hom ≫ (y ≫ (Etale.forget T).map h.hom)) =
        (Over.mapPullbackAdj f).homEquiv _ _ ((geometricPointMapIso f K x).hom ≫ y) ≫
          (Over.pullback f).map ((Etale.forget T).map h.hom)
      rw [← Category.assoc]
      exact (Over.mapPullbackAdj f).homEquiv_naturality_right _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The geometric point comparison commutes with the actual arithmetic action. -/
theorem geometricPointMapIso_naturality
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (geometricPointMapIso f K x).hom ≫ arithmeticFiberPointMap K (x ≫ f) g =
      (Over.map f).map (arithmeticFiberPointMap K x g) ≫
        (geometricPointMapIso f K x).hom := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback fibre identification intertwines the actual Galois actions. -/
theorem finiteArithmeticFiberPullbackEquiv_smul (Y : T.FiniteEtale)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (y : (finiteArithmeticFiberFunctor K (x ≫ f)).obj Y) :
    finiteArithmeticFiberPullbackEquiv f K x Y (g • y) =
      g • finiteArithmeticFiberPullbackEquiv f K x Y y := by
  change (Over.mapPullbackAdj f).homEquiv _ _
      ((geometricPointMapIso f K x).hom ≫ (arithmeticFiberPointMap K (x ≫ f) g ≫ y)) =
    arithmeticFiberPointMap K x g ≫ (Over.mapPullbackAdj f).homEquiv _ _
      ((geometricPointMapIso f K x).hom ≫ y)
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1

/-- A scheme morphism induces a homomorphism of the actual étale fundamental groups. -/
def etaleFundamentalGroupMap : etaleFundamentalGroup K x →*
    etaleFundamentalGroup K (x ≫ f) :=
  (finiteArithmeticFiberPullbackIso f K x).symm.conjAut.toMonoidHom.comp
    (((whiskeringLeft T.FiniteEtale S.FiniteEtale FintypeCat).obj
      (finiteEtalePullback f)).mapAut (finiteArithmeticFiberFunctor K x))

set_option backward.isDefEq.respectTransparency false in
/-- The fundamental-group map respects the arithmetic homomorphisms supplied by
rational points. -/
theorem etaleFundamentalGroupMap_galois
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    etaleFundamentalGroupMap f K x (galoisToEtaleFundamentalGroup K x g) =
      galoisToEtaleFundamentalGroup K (x ≫ f) g := by
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro y
  let e := finiteArithmeticFiberPullbackEquiv f K x Y
  change e.symm (g • e y) = g • y
  apply e.injective
  rw [e.apply_symm_apply]
  exact (finiteArithmeticFiberPullbackEquiv_smul f K x Y g y).symm

/-- Functoriality of the actual fundamental group is continuous. -/
theorem continuous_etaleFundamentalGroupMap :
    Continuous (etaleFundamentalGroupMap f K x) :=
  (PreGaloisCategory.continuous_conjAut
    (finiteArithmeticFiberPullbackIso f K x).symm).comp
      (PreGaloisCategory.continuous_mapAut_whiskeringLeft
        (finiteArithmeticFiberFunctor K x) (finiteEtalePullback f))

/-- The continuous fundamental-group map supplied by a scheme morphism. -/
def etaleFundamentalGroupContinuousMap : etaleFundamentalGroup K x →ₜ*
    etaleFundamentalGroup K (x ≫ f) where
  __ := etaleFundamentalGroupMap f K x
  continuous_toFun := continuous_etaleFundamentalGroupMap f K x

end AlgebraicGeometry.Scheme
