/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.EtaleKernel
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # The actual finite étale torsion tower of a group scheme

When multiplication by each `p`-power is finite étale, its actual kernels
form an inverse sequence of finite étale commutative group schemes.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.GroupScheme

universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory

variable {S : Scheme.{u}} (A : CommGrp (Over S)) (p : ℕ)
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Multiplication by `p` is the actual transition between successive finite étale torsion covers. -/
def finiteEtaleTorsionTransition (n : ℕ) :
    finiteEtaleTorsionObject A (p ^ (n + 1)) ⟶ finiteEtaleTorsionObject A (p ^ n) :=
  Scheme.finiteEtaleGroupObjectMap (CommGrp.torsionTransition A p n)

/-- The canonical inverse sequence of actual finite étale torsion group objects. -/
def finiteEtaleTorsionTower : ℕᵒᵖ ⥤ CommGrp S.FiniteEtale :=
  Functor.ofOpSequence (X := fun n => finiteEtaleTorsionObject A (p ^ n))
    (finiteEtaleTorsionTransition A p)

/-- The `n`th cover in the tower is the actual kernel of multiplication by `p^n`. -/
@[simp]
theorem finiteEtaleTorsionTower_obj (n : ℕ) :
    (finiteEtaleTorsionTower A p).obj (Opposite.op n) =
      finiteEtaleTorsionObject A (p ^ n) := rfl

/-- The geometric fibre of this one torsion tower is an inverse sequence of actual finite groups. -/
def torsionGroupFiberTower (K : Type u) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ S) : ℕᵒᵖ ⥤ CommGrpCat :=
  finiteEtaleTorsionTower A p ⋙ Scheme.finiteGroupFiberFunctor K x

/-- One torsion group-scheme tower supplies an inverse sequence of actual group-fibre families. -/
def torsionGroupLocalSystemTower (K : Type u) [Field K] :
    ℕᵒᵖ ⥤ (Scheme.EtaleFiberGroupoid K S ⥤ CommGrpCat) :=
  finiteEtaleTorsionTower A p ⋙ Scheme.finiteGroupFiberLocalSystemFunctor K S

end AlgebraicGeometry.GroupScheme
