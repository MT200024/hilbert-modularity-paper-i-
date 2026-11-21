/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GroupGeometricPath
public import HilbertModularity.Geometry.GroupScheme.TorsionTransitionComparison

/-! # Native torsion transport along geometric paths over different fields -/

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

/-- A path transports the native torsion subgroup of one geometric fibre to the other. -/
def torsionGeometricPathEquiv (n : ℕ)
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left] :
    AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n ≃+
      AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver L y ⟶ A.X)) n :=
  (finiteTorsionFiberPointsEquiv K x A n).symm.trans
    (((Scheme.finiteGroupFiberGeometricPathIso K L e).app
      (finiteEtaleTorsionObject A n)).commGroupIsoToMulEquiv.toAdditive.trans
        (finiteTorsionFiberPointsEquiv L y A n))

/-- Native torsion transport uses the actual path on the finite torsion cover. -/
theorem torsionGeometricPathEquiv_apply (n : ℕ)
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left]
    (v : AddSubgroup.torsionBy (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :
    torsionGeometricPathEquiv K L e A n v =
      finiteTorsionFiberPointsEquiv L y A n (Additive.ofMul
        ((Scheme.finiteGroupFiberGeometricPathIso K L e).hom.app (finiteEtaleTorsionObject A n)
          ((finiteTorsionFiberPointsEquiv K x A n).symm v).toMul)) := rfl

variable (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Geometric path transport is linear for the canonical finite-level p-adic action. -/
def torsionGeometricPathLinearMap (n : ℕ) :
    TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n →ₗ[ℤ_[p]]
      TateModule.Torsion p (Additive (Scheme.geometricPointOver L y ⟶ A.X)) n where
  __ := (torsionGeometricPathEquiv K L e A (p ^ n)).toAddMonoidHom
  map_smul' r v := by
    change torsionGeometricPathEquiv K L e A (p ^ n) (r.toZModPow n • v) =
      r.toZModPow n • torsionGeometricPathEquiv K L e A (p ^ n) v
    exact ZMod.map_smul (torsionGeometricPathEquiv K L e A (p ^ n)).toAddMonoidHom _ _

/-- The same path transports the entire torsion tower and commutes with multiplication by p. -/
theorem torsionGeometricPathLinearMap_transition (n : ℕ)
    (v : TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) (n + 1)) :
    TateModule.transition p (Additive (Scheme.geometricPointOver L y ⟶ A.X)) n
        (torsionGeometricPathLinearMap K L e A p (n + 1) v) =
      torsionGeometricPathLinearMap K L e A p n
        (TateModule.transition p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n v) := by
  let ex := finiteTorsionFiberPointsEquiv K x A (p ^ (n + 1))
  let ey := finiteTorsionFiberPointsEquiv L y A (p ^ n)
  obtain ⟨w, rfl⟩ := ex.surjective v
  change TateModule.transition p (Additive (Scheme.geometricPointOver L y ⟶ A.X)) n
      (torsionGeometricPathEquiv K L e A (p ^ (n + 1)) (ex w)) =
    torsionGeometricPathEquiv K L e A (p ^ n)
      (TateModule.transition p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n (ex w))
  rw [torsionGeometricPathEquiv_apply, torsionGeometricPathEquiv_apply]
  rw [AddEquiv.symm_apply_apply]
  rw [← finiteTorsionFiberPointsEquiv_transition K x A p n w]
  rw [AddEquiv.symm_apply_apply]
  rw [← finiteTorsionFiberPointsEquiv_transition L y A p n]
  have h := ConcreteCategory.congr_hom
    ((Scheme.finiteGroupFiberGeometricPathIso K L e).hom.naturality
      (finiteEtaleTorsionTransition A p n)) w.toMul
  exact congrArg (fun z => ey (Additive.ofMul z)) h.symm

end AlgebraicGeometry.GroupScheme
