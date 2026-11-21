/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.Fiber
public import HilbertModularity.Geometry.Etale.ArithmeticFiber
public import HilbertModularity.CategoryTheory.GroupObjectPoints
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Geometric points of an actual scheme-theoretic fibre -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S)

/-- Geometric points over a parameter are exactly points of the actual pullback fibre. -/
def geometricFiberPointsEquiv :
    (Scheme.geometricPointOver K x ⟶ A.X) ≃
      (fieldPoint K (AlgebraicClosure K) ⟶ (fiber K A x).X) :=
  (Over.mapPullbackAdj x).homEquiv (fieldPoint K (AlgebraicClosure K)) A.X

/-- The fibre comparison retains the original map to the total space. -/
@[simp]
theorem geometricFiberPointsEquiv_fst (v : Scheme.geometricPointOver K x ⟶ A.X) :
    (geometricFiberPointsEquiv K A x v).left ≫ pullback.fst A.X.hom x = v.left := by
  exact congrArg (fun z : Scheme.geometricPointOver K x ⟶ A.X => z.left)
    ((geometricFiberPointsEquiv K A x).symm_apply_apply v)

/-- Returning from a fibre point is composition with the actual pullback projection. -/
@[simp]
theorem geometricFiberPointsEquiv_symm_left
    (v : fieldPoint K (AlgebraicClosure K) ⟶ (fiber K A x).X) :
    ((geometricFiberPointsEquiv K A x).symm v).left = v.left ≫ pullback.fst A.X.hom x := rfl

attribute [local instance] CategoryTheory.coyonedaBraided

/-- Pullback adjunction compares the two actual representable point functors naturally. -/
def geometricFiberPointFunctorIso :
    coyoneda.obj (op (Scheme.geometricPointOver K x)) ≅
      Over.pullback x ⋙ coyoneda.obj (op (fieldPoint K (AlgebraicClosure K))) :=
  NatIso.ofComponents
    (fun A => ((Over.mapPullbackAdj x).homEquiv (fieldPoint K (AlgebraicClosure K)) A).toIso)
    (by
      intro A B f
      apply ConcreteCategory.hom_ext
      intro v
      exact (Over.mapPullbackAdj x).homEquiv_naturality_right v f)


/-- The adjunction identifies the actual commutative group fibres. -/
def geometricFiberGroupIso :
    ((coyoneda.obj (op (Scheme.geometricPointOver K x))).mapCommGrp ⋙
      commGrpTypeEquivalenceCommGrp.functor).obj A ≅
    ((coyoneda.obj (op (fieldPoint K (AlgebraicClosure K)))).mapCommGrp ⋙
      commGrpTypeEquivalenceCommGrp.functor).obj (fiber K A x) :=
  commGrpTypeEquivalenceCommGrp.functor.mapIso
    ((Functor.mapCommGrpNatIso (geometricFiberPointFunctorIso K x)).app A ≪≫
      (Functor.mapCommGrpCompIso (F := Over.pullback x)
        (G := coyoneda.obj (op (fieldPoint K (AlgebraicClosure K))))).app A)

/-- The geometric fibre-point comparison preserves the original group law. -/
def geometricFiberPointsMulEquiv :
    (Scheme.geometricPointOver K x ⟶ A.X) ≃*
      (fieldPoint K (AlgebraicClosure K) ⟶ (fiber K A x).X) :=
  (CategoryTheory.coyonedaCommGroupPointsEquiv (Scheme.geometricPointOver K x) A).symm.trans
    ((geometricFiberGroupIso K A x).commGroupIsoToMulEquiv.trans
      (CategoryTheory.coyonedaCommGroupPointsEquiv (fieldPoint K (AlgebraicClosure K))
        (fiber K A x)))

/-- The multiplicative comparison has the original pullback-adjunction map on points. -/
@[simp]
theorem geometricFiberPointsMulEquiv_apply (v : Scheme.geometricPointOver K x ⟶ A.X) :
    geometricFiberPointsMulEquiv K A x v = geometricFiberPointsEquiv K A x v := rfl

/-- The actual geometric point groups agree additively before forming their Tate modules. -/
def geometricFiberPointsAddEquiv :
    Additive (Scheme.geometricPointOver K x ⟶ A.X) ≃+
      Points K (AlgebraicClosure K) (fiber K A x).X :=
  (geometricFiberPointsMulEquiv K A x).toAdditive

/-- The comparison intertwines the two actual arithmetic actions by precomposition. -/
theorem geometricFiberPointsAddEquiv_arithmetic
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : Additive (Scheme.geometricPointOver K x ⟶ A.X)) :
    (geometricFiberPointsAddEquiv K A x
      (Additive.ofMul (Scheme.arithmeticFiberPointMap K x g ≫ v.toMul))).toMul =
      fieldPointMap K (AlgebraicClosure K) g ≫ (geometricFiberPointsAddEquiv K A x v).toMul := by
  have h₁ := geometricFiberPointsMulEquiv_apply K A x
    (Scheme.arithmeticFiberPointMap K x g ≫ v.toMul)
  have h₂ := (Over.mapPullbackAdj x).homEquiv_naturality_left
    (fieldPointMap K (AlgebraicClosure K) g) v.toMul
  have h₃ := congrArg (fun w : fieldPoint K (AlgebraicClosure K) ⟶ (fiber K A x).X =>
    fieldPointMap K (AlgebraicClosure K) g ≫ w)
      (geometricFiberPointsMulEquiv_apply K A x v.toMul)
  have h₄ := h₂.trans h₃.symm
  exact h₁.trans h₄


end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A B : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S) (f : A ⟶ B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Comparing points with the pullback fibre respects every original group-scheme morphism. -/
theorem geometricFiberPointsMulEquiv_natural
    (v : Scheme.geometricPointOver K x ⟶ A.X) :
    geometricFiberPointsMulEquiv K B x (v ≫ f.hom.hom.hom) =
      geometricFiberPointsMulEquiv K A x v ≫
        ((Over.pullback x).mapCommGrp.map f).hom.hom.hom := by
  exact (Over.mapPullbackAdj x).homEquiv_naturality_right v f.hom.hom.hom

/-- The additive point comparison intertwines the original point map with its fibre specialization. -/
theorem geometricFiberPointsAddEquiv_map
    (v : Additive (Scheme.geometricPointOver K x ⟶ A.X)) :
    geometricFiberPointsAddEquiv K B x
        ((IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive v) =
      pointsMap K (AlgebraicClosure K) ((Over.pullback x).mapCommGrp.map f).hom.hom.hom
        (geometricFiberPointsAddEquiv K A x v) :=
  geometricFiberPointsMulEquiv_natural K A B x f v.toMul


end AlgebraicGeometry.GroupScheme
