/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.FieldCoordinate
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Fiber
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.ArithmeticCoefficients

/-! # Field-coordinate comparison of arithmetic Tate monodromy -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory TensorProduct

namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory
variable (E K : Type u) [Field E] [Field K] (σ : E ≃+* K)
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The Tate field comparison agrees at every level with the natural comparison
of the actual finite étale torsion cover. -/
theorem tateFieldCoordinateEquiv_torsion
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) (n : ℕ) :
    finiteTorsionFiberPointsEquiv K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) A (p ^ n)
      (Additive.ofMul ((Scheme.arithmeticFiberFieldEquivIso E K σ x).hom.app
        (finiteEtaleTorsionObject A (p ^ n)).X
        ((finiteTorsionFiberPointsEquiv E x A (p ^ n)).symm (v.val n)).toMul)) =
      (tateFieldCoordinateEquiv E K σ x A p v).val n := by
  let e := finiteTorsionFiberPointsEquiv E x A (p ^ n)
  have hv := congrArg (fun w => w.val.toMul.left) (e.apply_symm_apply (v.val n))
  change (e.symm (v.val n)).toMul.left ≫
    (Grp.kernelInclusion (p ^ n • 𝟙 A).hom).left = (v.val n).val.toMul.left at hv
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change ((Scheme.arithmeticFiberFieldEquivIso E K σ x).hom.app
      (finiteEtaleTorsionObject A (p ^ n)).X (e.symm (v.val n)).toMul).left ≫
      (Grp.kernelInclusion (p ^ n • 𝟙 A).hom).left = _
  have h := Scheme.arithmeticFiberFieldEquivIso_hom_app_left E K σ x
    (finiteEtaleTorsionObject A (p ^ n)).X (e.symm (v.val n)).toMul
  exact (congrArg (fun f => f ≫ (Grp.kernelInclusion (p ^ n • 𝟙 A).hom).left) h).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => Spec.map (CommRingCat.ofHom
        (IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ).toRingHom) ≫ f) hv).trans
        (tateFieldCoordinateEquiv_projection E K σ x A p v n).symm))

set_option maxHeartbeats 1000000 in
/-- The actual integral Tate fibres intertwine the original arithmetic action with
the native Galois action conjugated by the field-coordinate isomorphism. -/
def tateFieldCoordinateRepresentationEquiv :
    Representation.Equiv
      ((integralTateMonodromy E x A p).comp (Scheme.galoisToEtaleFundamentalGroup E x))
      ((integralTateMonodromy K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) A p).comp
        (((Scheme.galoisToEtaleFundamentalGroup K
          (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)).comp
        (AlgebraicClosure.galoisFieldEquiv E K σ).toMonoidHom))) :=
  .mk (tateFieldCoordinateEquiv E K σ x A p) (by
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext n
    let X := finiteEtaleTorsionObject A (p ^ n)
    let e := finiteTorsionFiberPointsEquiv E x A (p ^ n)
    let e' := finiteTorsionFiberPointsEquiv K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) A (p ^ n)
    let α := Scheme.arithmeticFiberFieldEquivIso E K σ x
    let gE := Scheme.galoisToEtaleFundamentalGroup E x g
    let gK := ((Scheme.galoisToEtaleFundamentalGroup K
          (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)).comp
        (AlgebraicClosure.galoisFieldEquiv E K σ).toMonoidHom) g
    have hc (w : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
        (tateFieldCoordinateEquiv E K σ x A p w).val n =
          e' (Additive.ofMul (α.hom.app X.X (e.symm (w.val n)).toMul)) :=
      (tateFieldCoordinateEquiv_torsion E K σ x A p w n).symm
    have hn : α.hom.app X.X (gE.hom.app X.X (e.symm (v.val n)).toMul) =
        gK.hom.app X.X (α.hom.app X.X (e.symm (v.val n)).toMul) := by
      have h := congrArg (fun transformation : Scheme.finiteArithmeticFiberFunctor E x ⟶
          Scheme.finiteArithmeticFiberFunctor K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) =>
          transformation.app X.X (e.symm (v.val n)).toMul)
        (Scheme.arithmeticFiberFieldEquivIso_galois E K σ x g)
      exact h.symm
    change (tateFieldCoordinateEquiv E K σ x A p
        (integralTateMonodromy E x A p gE v)).val n =
      (finiteTorsionMonodromy K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) A (p ^ n) gK).toAdd
        ((tateFieldCoordinateEquiv E K σ x A p v).val n)
    rw [hc, hc]
    change e' (Additive.ofMul (α.hom.app X.X
        (e.symm (e (Additive.ofMul (gE.hom.app X.X (e.symm (v.val n)).toMul)))).toMul)) =
      e' (Additive.ofMul (gK.hom.app X.X
        (e'.symm (e' (Additive.ofMul (α.hom.app X.X (e.symm (v.val n)).toMul)))).toMul))
    simp only [AddEquiv.symm_apply_apply]
    exact congrArg (fun z => e' (Additive.ofMul z)) hn)

/-- The field-coordinate comparison also intertwines the actual rational arithmetic Tate representations. -/
def rationalTateFieldCoordinateRepresentationEquiv :
    Representation.Equiv
      ((rationalTateMonodromy E x A p).comp (Scheme.galoisToEtaleFundamentalGroup E x))
      ((rationalTateMonodromy K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) A p).comp
        (((Scheme.galoisToEtaleFundamentalGroup K
          (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)).comp
        (AlgebraicClosure.galoisFieldEquiv E K σ).toMonoidHom))) :=
  .mk (rationalTateFieldCoordinateEquiv E K σ x A p)
    ((tateFieldCoordinateRepresentationEquiv E K σ x A p).baseChange ℚ_[p]).isIntertwining'

/-- Arithmetic monodromy over the isomorphic parameter field recovers the native rational
Tate representation of the original scheme-theoretic fibre. -/
def tateMonodromyFieldCoordinate_arithmeticEquiv :
    Representation.Equiv
      ((rationalTateMonodromy K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) A p).comp
        (((Scheme.galoisToEtaleFundamentalGroup K
          (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)).comp
        (AlgebraicClosure.galoisFieldEquiv E K σ).toMonoidHom)))
      (tateRepresentation E (fiber E A x).X p) :=
  (rationalTateFieldCoordinateRepresentationEquiv E K σ x A p).symm.trans
    (rationalGeometricFiberTateEquiv E A x p)

set_option maxHeartbeats 1000000 in
/-- Evaluation of the Tate family after a parameter-field isomorphism recovers the native
Tate representation at the original rational point with the correctly conjugated action. -/
def rationalTateLocalSystem_fieldCoordinateEquiv :
    Representation.Equiv
      ((Scheme.fiberMonodromy K S (rationalTateLocalSystem K A p)
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)).comp
          ((Scheme.galoisToEtaleFundamentalGroup K
            (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)).comp
              (AlgebraicClosure.galoisFieldEquiv E K σ).toMonoidHom))
      (tateRepresentation E (fiber E A x).X p) := by
  let e := tateMonodromyFieldCoordinate_arithmeticEquiv E K σ x A p
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  have h₁ := congrArg e (rationalTateLocalSystem_loop K A p
    (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
    (Scheme.galoisToEtaleFundamentalGroup K
      (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)
      (AlgebraicClosure.galoisFieldEquiv E K σ g)) v)
  have h₂ := LinearMap.congr_fun (e.isIntertwining' g) v
  exact h₁.trans h₂

set_option maxHeartbeats 1000000 in
open scoped NumberField in
/-- Field-coordinate transport preserves the evaluated coefficient algebra of the Tate family. -/
theorem rationalTateFieldCoordinateEquiv_familyCoefficients
    (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
    (a : ℚ_[p] ⊗[ℚ] F)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
    rationalTateFieldCoordinateEquiv E K σ x A p
        (((tensorTateLocalSystemAction E A p F φ a).app (Scheme.etaleFiberPoint E S x)).hom v) =
      ((tensorTateLocalSystemAction K A p F φ a).app
        (Scheme.etaleFiberPoint K S (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x))).hom
        (rationalTateFieldCoordinateEquiv E K σ x A p v) := by
  rw [tensorTateLocalSystemAction_app, tensorTateLocalSystemAction_app]
  exact rationalTateFieldCoordinateEquiv_tensorCoefficients E K σ x A p F φ a v

end AlgebraicGeometry.GroupScheme
