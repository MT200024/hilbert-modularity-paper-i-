/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Maps
public import HilbertModularity.Algebra.TateModule.Endomorphism
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Endomorphisms of the actual Tate family -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Actual scheme endomorphisms act as a ring on the single integral Tate family. -/
def integralTateLocalSystemEndomorphismMap : End A →+* End (integralTateLocalSystem K A p) := by
  let F (x : Scheme.EtaleFiberGroupoid K S) :=
    (TateModule.endomorphismMap p (Additive (Scheme.geometricPointOver K x ⟶ A.X))).comp
      (CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver K x) A)
  exact {
    toFun f := integralTateLocalSystemMap K p f
    map_one' := by
      apply NatTrans.ext
      funext x
      apply ModuleCat.hom_ext
      exact (F x).map_one
    map_mul' f g := by
      apply NatTrans.ext
      funext x
      apply ModuleCat.hom_ext
      exact (F x).map_mul f g
    map_zero' := by
      apply NatTrans.ext
      funext x
      apply ModuleCat.hom_ext
      exact (F x).map_zero
    map_add' f g := by
      apply NatTrans.ext
      funext x
      apply ModuleCat.hom_ext
      exact (F x).map_add f g }

/-- Actual scheme endomorphisms act as a ring on the single rational Tate family. -/
def rationalTateLocalSystemEndomorphismMap : End A →+* End (rationalTateLocalSystem K A p) := by
  let F (x : Scheme.EtaleFiberGroupoid K S) :=
    (TateModule.rationalEndomorphismMap p (Additive (Scheme.geometricPointOver K x ⟶ A.X))).comp
      (CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver K x) A)
  exact {
    toFun f := rationalTateLocalSystemMap K p f
    map_one' := by
      apply NatTrans.ext
      funext x
      apply ModuleCat.hom_ext
      exact (F x).map_one
    map_mul' f g := by
      apply NatTrans.ext
      funext x
      apply ModuleCat.hom_ext
      exact (F x).map_mul f g
    map_zero' := by
      apply NatTrans.ext
      funext x
      apply ModuleCat.hom_ext
      exact (F x).map_zero
    map_add' f g := by
      apply NatTrans.ext
      funext x
      apply ModuleCat.hom_ext
      exact (F x).map_add f g }

end AlgebraicGeometry.GroupScheme
