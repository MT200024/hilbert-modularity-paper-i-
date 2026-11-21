/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateGeometricPath
public import HilbertModularity.Geometry.GroupScheme.TorsionLocalSystemMaps

/-! # Naturality of geometric Tate transport in the original group scheme

In particular, actual coefficient endomorphisms of one group scheme commute
with transport between geometric fibres over different fields.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory Scheme.finiteEtaleBraidedCategory
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  {A B : CommGrp (Over S)}

set_option backward.isDefEq.respectTransparency false in
/-- Native torsion transport is natural in actual morphisms of the original group schemes. -/
theorem torsionGeometricPathEquiv_natural (n : ℕ)
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left]
    [IsFinite (n • 𝟙 B).hom.hom.hom.left] [Etale (n • 𝟙 B).hom.hom.hom.left]
    (f : A ⟶ B)
    (v : AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    torsionGeometricPathEquiv K L e B n ((torsionPointLocalSystemMap K n f).app x v) =
      (torsionPointLocalSystemMap L n f).app y (torsionGeometricPathEquiv K L e A n v) := by
  let Ax := finiteTorsionFiberPointsEquiv K x A n
  let Bx := finiteTorsionFiberPointsEquiv K x B n
  let Ay := finiteTorsionFiberPointsEquiv L y A n
  let By := finiteTorsionFiberPointsEquiv L y B n
  let fK := (Scheme.finiteGroupFiberFunctor K x).map (finiteEtaleTorsionMap n f)
  let fL := (Scheme.finiteGroupFiberFunctor L y).map (finiteEtaleTorsionMap n f)
  change By (Additive.ofMul (e.hom.app (finiteEtaleTorsionObject B n).X
      (Bx.symm (Bx (Additive.ofMul (fK (Ax.symm v).toMul)))).toMul)) =
    By (Additive.ofMul (fL (Ay.symm (Ay (Additive.ofMul
      (e.hom.app (finiteEtaleTorsionObject A n).X (Ax.symm v).toMul)))).toMul))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact congrArg (fun z => By (Additive.ofMul z))
    (ConcreteCategory.congr_hom
      ((Scheme.finiteGroupFiberGeometricPathIso K L e).hom.naturality
        (finiteEtaleTorsionMap n f)) (Ax.symm v).toMul)

variable (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 B).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 B).hom.hom.hom.left]

/-- Integral Tate path transport commutes with the ordinary Tate map of a group-scheme morphism. -/
theorem integralTateGeometricPathEquiv_natural (f : A ⟶ B) :
    (integralTateGeometricPathEquiv K L e B p).toLinearMap.comp
        (TateModule.map p
          (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive) =
      (TateModule.map p
        (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver L y)).toAdditive).comp
          (integralTateGeometricPathEquiv K L e A p).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext n
  have h := torsionGeometricPathEquiv_natural K L e (p ^ n) f (v.val n)
  change torsionGeometricPathEquiv K L e B (p ^ n)
      ((torsionPadicLocalSystemMap K p f n).app x (v.val n)) =
    (torsionPadicLocalSystemMap L p f n).app y
      (torsionGeometricPathEquiv K L e A (p ^ n) (v.val n)) at h
  exact (congrArg (torsionGeometricPathEquiv K L e B (p ^ n))
    (torsionPadicLocalSystemMap_eq K p f n x (v.val n))).symm.trans
      (h.trans (torsionPadicLocalSystemMap_eq L p f n y
        (torsionGeometricPathEquiv K L e A (p ^ n) (v.val n))))

set_option maxHeartbeats 1000000 in
/-- Rational Tate transport commutes with maps of the original group schemes. -/
theorem rationalTateGeometricPathEquiv_natural (f : A ⟶ B) :
    (rationalTateGeometricPathEquiv K L e B p).toLinearMap.comp
        (TateModule.rationalMap p
          (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive) =
      (TateModule.rationalMap p
        (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver L y)).toAdditive).comp
          (rationalTateGeometricPathEquiv K L e A p).toLinearMap := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul c w =>
    change c ⊗ₜ[ℤ_[p]] (integralTateGeometricPathEquiv K L e B p
        (TateModule.map p
          (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive w)) =
      c ⊗ₜ[ℤ_[p]] (TateModule.map p
        (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver L y)).toAdditive
          (integralTateGeometricPathEquiv K L e A p w))
    exact congrArg (fun z => c ⊗ₜ[ℤ_[p]] z)
      (LinearMap.congr_fun (integralTateGeometricPathEquiv_natural K L e p f) w)
  | add v w hv hw => simp only [map_add, hv, hw]

end AlgebraicGeometry.GroupScheme
