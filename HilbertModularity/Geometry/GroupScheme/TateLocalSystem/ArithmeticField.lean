/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.ArithmeticField
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Fiber

/-! # Arithmetic field comparison and finite torsion monodromy -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory TensorProduct

namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory
variable (E K : Type u) [Field E] [Field K] [Algebra E K]
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)
  (j : AlgebraicClosure E →ₐ[E] AlgebraicClosure K)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The Tate field comparison agrees at every level with the natural comparison
of the actual finite étale torsion cover. -/
theorem arithmeticTateFieldEquiv_torsion
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) (n : ℕ) :
    finiteTorsionFiberPointsEquiv K (Spec.algebraMap E K ≫ x) A (p ^ n)
      (Additive.ofMul ((Scheme.arithmeticFiberFieldIso E K x j).hom.app
        (finiteEtaleTorsionObject A (p ^ n)).X
        ((finiteTorsionFiberPointsEquiv E x A (p ^ n)).symm (v.val n)).toMul)) =
      (arithmeticTateFieldEquiv E K x j A p v).val n := by
  let e := finiteTorsionFiberPointsEquiv E x A (p ^ n)
  have hv := congrArg (fun w => w.val.toMul.left) (e.apply_symm_apply (v.val n))
  change (e.symm (v.val n)).toMul.left ≫
    (Grp.kernelInclusion (p ^ n • 𝟙 A).hom).left = (v.val n).val.toMul.left at hv
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change ((Scheme.arithmeticFiberFieldIso E K x j).hom.app
      (finiteEtaleTorsionObject A (p ^ n)).X (e.symm (v.val n)).toMul).left ≫
      (Grp.kernelInclusion (p ^ n • 𝟙 A).hom).left = _
  have h := Scheme.arithmeticFiberFieldIso_hom_app_left E K x j
    (finiteEtaleTorsionObject A (p ^ n)).X (e.symm (v.val n)).toMul
  exact (congrArg (fun f => f ≫ (Grp.kernelInclusion (p ^ n • 𝟙 A).hom).left) h).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => Spec.map (CommRingCat.ofHom j.toRingHom) ≫ f) hv).trans
        (arithmeticTateFieldEquiv_projection E K x j A p v n).symm))

set_option maxHeartbeats 1000000 in
/-- The actual integral Tate fibres intertwine the original arithmetic action with
its transported action in the common parameter-field groupoid. -/
def arithmeticTateFieldRepresentationEquiv :
    Representation.Equiv
      ((integralTateMonodromy E x A p).comp (Scheme.galoisToEtaleFundamentalGroup E x))
      ((integralTateMonodromy K (Spec.algebraMap E K ≫ x) A p).comp
        (Scheme.galoisToEtaleFundamentalGroupOverField E K x j)) :=
  .mk (arithmeticTateFieldEquiv E K x j A p) (by
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext n
    let X := finiteEtaleTorsionObject A (p ^ n)
    let e := finiteTorsionFiberPointsEquiv E x A (p ^ n)
    let e' := finiteTorsionFiberPointsEquiv K (Spec.algebraMap E K ≫ x) A (p ^ n)
    let α := Scheme.arithmeticFiberFieldIso E K x j
    let σ := Scheme.galoisToEtaleFundamentalGroup E x g
    let σ' := Scheme.galoisToEtaleFundamentalGroupOverField E K x j g
    have hc (w : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
        (arithmeticTateFieldEquiv E K x j A p w).val n =
          e' (Additive.ofMul (α.hom.app X.X (e.symm (w.val n)).toMul)) :=
      (arithmeticTateFieldEquiv_torsion E K x j A p w n).symm
    have hn : α.hom.app X.X (σ.hom.app X.X (e.symm (v.val n)).toMul) =
        σ'.hom.app X.X (α.hom.app X.X (e.symm (v.val n)).toMul) := by
      have h := congrArg (fun transformation : Scheme.finiteArithmeticFiberFunctor E x ⟶
          Scheme.finiteArithmeticFiberFunctor K (Spec.algebraMap E K ≫ x) =>
          transformation.app X.X (e.symm (v.val n)).toMul)
        (Scheme.arithmeticFiberFieldIso_galois E K x j g)
      exact h.symm
    change (arithmeticTateFieldEquiv E K x j A p
        (integralTateMonodromy E x A p σ v)).val n =
      (finiteTorsionMonodromy K (Spec.algebraMap E K ≫ x) A (p ^ n) σ').toAdd
        ((arithmeticTateFieldEquiv E K x j A p v).val n)
    rw [hc, hc]
    change e' (Additive.ofMul (α.hom.app X.X
        (e.symm (e (Additive.ofMul (σ.hom.app X.X (e.symm (v.val n)).toMul)))).toMul)) =
      e' (Additive.ofMul (σ'.hom.app X.X
        (e'.symm (e' (Additive.ofMul (α.hom.app X.X (e.symm (v.val n)).toMul)))).toMul))
    simp only [AddEquiv.symm_apply_apply]
    exact congrArg (fun z => e' (Additive.ofMul z)) hn)

/-- The common-field comparison also intertwines the actual rational arithmetic Tate representations. -/
def arithmeticRationalTateFieldRepresentationEquiv :
    Representation.Equiv
      ((rationalTateMonodromy E x A p).comp (Scheme.galoisToEtaleFundamentalGroup E x))
      ((rationalTateMonodromy K (Spec.algebraMap E K ≫ x) A p).comp
        (Scheme.galoisToEtaleFundamentalGroupOverField E K x j)) :=
  .mk (arithmeticRationalTateFieldEquiv E K x j A p)
    ((arithmeticTateFieldRepresentationEquiv E K x j A p).baseChange ℚ_[p]).isIntertwining'

/-- Arithmetic monodromy over the larger parameter field recovers the native rational
Tate representation of the original scheme-theoretic fibre. -/
def tateMonodromyOverField_arithmeticEquiv :
    Representation.Equiv
      ((rationalTateMonodromy K (Spec.algebraMap E K ≫ x) A p).comp
        (Scheme.galoisToEtaleFundamentalGroupOverField E K x j))
      (tateRepresentation E (fiber E A x).X p) :=
  (arithmeticRationalTateFieldRepresentationEquiv E K x j A p).symm.trans
    (rationalGeometricFiberTateEquiv E A x p)

set_option maxHeartbeats 1000000 in
/-- One Tate family over the common parameter-field groupoid specializes to the native
Tate representation at the original rational point, through its transported arithmetic loops. -/
def rationalTateLocalSystem_overFieldEquiv :
    Representation.Equiv
      ((Scheme.fiberMonodromy K S (rationalTateLocalSystem K A p)
        (Spec.algebraMap E K ≫ x)).comp
          (Scheme.galoisToEtaleFundamentalGroupOverField E K x j))
      (tateRepresentation E (fiber E A x).X p) := by
  let e := tateMonodromyOverField_arithmeticEquiv E K x j A p
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  have h₁ := congrArg e (rationalTateLocalSystem_loop K A p (Spec.algebraMap E K ≫ x)
    (Scheme.galoisToEtaleFundamentalGroupOverField E K x j g) v)
  have h₂ := LinearMap.congr_fun (e.isIntertwining' g) v
  exact h₁.trans h₂

end AlgebraicGeometry.GroupScheme
