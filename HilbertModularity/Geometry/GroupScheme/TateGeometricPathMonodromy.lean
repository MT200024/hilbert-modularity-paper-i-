/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateGeometricPath
public import HilbertModularity.Geometry.GroupScheme.TateMonodromy

/-! # Monodromy compatibility of geometric Tate transport -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory Scheme.finiteEtaleBraidedCategory
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S))

set_option backward.isDefEq.respectTransparency false in
/-- Transport on native torsion intertwines the actual monodromy actions. -/
theorem torsionGeometricPathEquiv_monodromy (n : ℕ)
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left]
    (σ : Scheme.etaleFundamentalGroup K x)
    (v : AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    torsionGeometricPathEquiv K L e A n ((finiteTorsionMonodromy K x A n σ).toAdd v) =
      (finiteTorsionMonodromy L y A n (Scheme.geometricFiberPathGroupEquiv K L e σ)).toAdd
        (torsionGeometricPathEquiv K L e A n v) := by
  let T := finiteEtaleTorsionObject A n
  let ex := finiteTorsionFiberPointsEquiv K x A n
  let ey := finiteTorsionFiberPointsEquiv L y A n
  change ey (Additive.ofMul (e.hom.app T.X
      (ex.symm (ex (Additive.ofMul (σ.hom.app T.X (ex.symm v).toMul)))).toMul)) =
    ey (Additive.ofMul ((e.conjAut σ).hom.app T.X
      (ey.symm (ey (Additive.ofMul (e.hom.app T.X (ex.symm v).toMul)))).toMul))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact congrArg (fun z => ey (Additive.ofMul z))
    (Scheme.finiteGroupFiberGeometricPathIso_smul K L e T σ (ex.symm v).toMul)

variable (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Integral Tate transport intertwines monodromy under the actual path conjugation. -/
def integralTateGeometricPathRepresentationEquiv :
    (integralTateMonodromy K x A p).Equiv
      ((integralTateMonodromy L y A p).comp
        (Scheme.geometricFiberPathGroupEquiv K L e).toMonoidHom) :=
  .mk (integralTateGeometricPathEquiv K L e A p) (by
    intro σ
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext n
    exact torsionGeometricPathEquiv_monodromy K L e A (p ^ n) σ (v.val n))

/-- Rationalizing the same path gives an equivalence of actual Tate monodromy representations. -/
def rationalTateGeometricPathRepresentationEquiv :
    (rationalTateMonodromy K x A p).Equiv
      ((rationalTateMonodromy L y A p).comp
        (Scheme.geometricFiberPathGroupEquiv K L e).toMonoidHom) :=
  (integralTateGeometricPathRepresentationEquiv K L e A p).baseChange ℚ_[p]

end AlgebraicGeometry.GroupScheme
