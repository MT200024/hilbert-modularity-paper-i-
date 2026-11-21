/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Types.Basic

/-! # Arithmetic action on geometric étale fibres

A rational point of a scheme supplies a geometric point after extending to an
algebraic closure. The absolute Galois group acts naturally on the actual
geometric fibres of étale covers, hence by natural automorphisms of the fibre
functor. This constructs the arithmetic action; no fundamental-group exact
sequence or lisse realization is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

open GroupScheme

universe u
variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S)

/-- The geometric point of the scheme induced by one rational point. -/
def geometricPointOver : Over S :=
  (Over.map x).obj (fieldPoint K (AlgebraicClosure K))

@[simp]
theorem geometricPointOver_hom :
    (geometricPointOver K x).hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ x := rfl

/-- The actual geometric fibre functor on the small étale category at a rational point. -/
def arithmeticFiberFunctor : S.Etale ⥤ Type u :=
  Etale.forget S ⋙ coyoneda.obj (op (geometricPointOver K x))

/-- This is the fibre functor of the standard geometric point of the small étale site. -/
theorem arithmeticFiberFunctor_eq_pointSmallEtale :
    arithmeticFiberFunctor K x = (pointSmallEtale (geometricPointOver K x).hom).fiber := rfl

/-- A base-field Galois automorphism acts on the chosen geometric point over the same scheme. -/
def arithmeticFiberPointMap (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    geometricPointOver K x ⟶ geometricPointOver K x :=
  (Over.map x).map (fieldPointMap K (AlgebraicClosure K) g)

@[simp]
theorem arithmeticFiberPointMap_one : arithmeticFiberPointMap K x 1 = 𝟙 _ := by
  unfold arithmeticFiberPointMap geometricPointOver
  rw [fieldPointMap_one]
  exact (Over.map x).map_id (fieldPoint K (AlgebraicClosure K))

/-- Contravariance of field spectra gives the composition order for the left action on fibres. -/
theorem arithmeticFiberPointMap_mul
    (g h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    arithmeticFiberPointMap K x (g * h) =
      arithmeticFiberPointMap K x g ≫ arithmeticFiberPointMap K x h := by
  unfold arithmeticFiberPointMap geometricPointOver
  rw [fieldPointMap_mul]
  exact (Over.map x).map_comp (fieldPointMap K (AlgebraicClosure K) g)
    (fieldPointMap K (AlgebraicClosure K) h)

set_option backward.isDefEq.respectTransparency false in
/-- The absolute Galois group acts on each actual geometric étale fibre. -/
instance arithmeticFiberMulAction (X : S.Etale) :
    MulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      ((arithmeticFiberFunctor K x).obj X) where
  smul g y := arithmeticFiberPointMap K x g ≫ y
  one_smul y := by
    change arithmeticFiberPointMap K x 1 ≫ y = y
    rw [arithmeticFiberPointMap_one]
    exact Category.id_comp y
  mul_smul g h y := by
    change arithmeticFiberPointMap K x (g * h) ≫ y =
      arithmeticFiberPointMap K x g ≫ (arithmeticFiberPointMap K x h ≫ y)
    rw [arithmeticFiberPointMap_mul]
    exact Category.assoc (arithmeticFiberPointMap K x g) (arithmeticFiberPointMap K x h) y

set_option backward.isDefEq.respectTransparency false in
/-- Maps of actual étale covers commute with the arithmetic Galois action. -/
theorem arithmeticFiber_map_smul {X Y : S.Etale} (f : X ⟶ Y)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (y : (arithmeticFiberFunctor K x).obj X) :
    (arithmeticFiberFunctor K x).map f (g • y) =
      g • (arithmeticFiberFunctor K x).map f y := by
  change (arithmeticFiberPointMap K x g ≫ y) ≫ (Etale.forget S).map f =
    arithmeticFiberPointMap K x g ≫ (y ≫ (Etale.forget S).map f)
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The arithmetic action is a genuine homomorphism into natural automorphisms
of the geometric étale fibre functor. -/
def arithmeticFiberGaloisAut :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Aut (arithmeticFiberFunctor K x) where
  toFun g := NatIso.ofComponents
    (fun X => (MulAction.toPermHom (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      ((arithmeticFiberFunctor K x).obj X) g).toIso) (by
      intro X Y f
      apply ConcreteCategory.hom_ext
      intro y
      exact (arithmeticFiber_map_smul K x f g y).symm)
  map_one' := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro y
    change (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) • y = y
    exact one_smul _ _
  map_mul' g h := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro y
    change (g * h) • y = g • (h • y)
    exact mul_smul _ _ _

@[simp]
theorem arithmeticFiberGaloisAut_hom_app
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (X : S.Etale)
    (y : (arithmeticFiberFunctor K x).obj X) :
    (arithmeticFiberGaloisAut K x g).hom.app X y = g • y := rfl

end AlgebraicGeometry.Scheme
