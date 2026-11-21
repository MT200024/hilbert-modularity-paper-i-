/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientAction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Scalar extension of the single Tate family

The standard module-category scalar-extension functor extends one whole Tate
family and its natural endomorphisms over the original geometric fibre groupoid.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra ChangeOfRings
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [Field L] [Algebra ℚ_[p] L]

/-- Extend coefficients on the whole Tate family, leaving its geometric paths unchanged. -/
def extendedTateLocalSystem : Scheme.EtaleFiberGroupoid K S ⥤ ModuleCat L :=
  rationalTateLocalSystem K A p ⋙ ModuleCat.extendScalars (algebraMap ℚ_[p] L)

/-- Extended transport fixes the new coefficient and uses the original family path map. -/
@[simp]
theorem extendedTateLocalSystem_map_tmul {x y : Scheme.EtaleFiberGroupoid K S}
    (e : x ⟶ y) (c : L) (v : (rationalTateLocalSystem K A p).obj x) :
    (extendedTateLocalSystem K A p L).map e
        (c ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L] v) =
      c ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L] ((rationalTateLocalSystem K A p).map e v) :=
  ModuleCat.ExtendScalars.map_tmul _ _ _ _

/-- A natural endomorphism extends on the same family by the scalar-extension functor. -/
def extendedTateLocalSystemEndomorphism
    (f : End (rationalTateLocalSystem K A p)) : End (extendedTateLocalSystem K A p L) :=
  Functor.whiskerRight f (ModuleCat.extendScalars (algebraMap ℚ_[p] L))

set_option maxHeartbeats 1000000 in
/-- At a rational point a natural endomorphism extends by the ordinary module functor. -/
@[simp]
theorem extendedTateLocalSystemEndomorphism_app
    (f : End (rationalTateLocalSystem K A p)) (x : Spec (CommRingCat.of K) ⟶ S) :
    (extendedTateLocalSystemEndomorphism K A p L f).app (Scheme.etaleFiberPoint K S x) =
      (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map
        (f.app (Scheme.etaleFiberPoint K S x)) := rfl

/-- Extension of natural Tate endomorphisms preserves their ring operations. -/
def extendedTateLocalSystemEndomorphismMap :
    End (rationalTateLocalSystem K A p) →+* End (extendedTateLocalSystem K A p L) where
  toFun := extendedTateLocalSystemEndomorphism K A p L
  map_one' := by
    apply NatTrans.ext
    funext x
    exact (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map_id _
  map_mul' f g := by
    apply NatTrans.ext
    funext x
    exact (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map_comp (g.app x) (f.app x)
  map_zero' := by
    apply NatTrans.ext
    funext x
    change (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map (0 : _ ⟶ _) = 0
    apply ModuleCat.ExtendScalars.hom_ext
    intro v
    let : Module ℚ_[p] L := Module.compHom L (algebraMap ℚ_[p] L)
    change (1 : L) ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L]
      (0 : (rationalTateLocalSystem K A p).obj x) = 0
    exact TensorProduct.tmul_zero (R := ℚ_[p]) _ (1 : L)
  map_add' f g := by
    apply NatTrans.ext
    funext x
    change (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map (f.app x + g.app x) =
      (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map (f.app x) +
        (ModuleCat.extendScalars (algebraMap ℚ_[p] L)).map (g.app x)
    apply ModuleCat.ExtendScalars.hom_ext
    intro v
    let : Module ℚ_[p] L := Module.compHom L (algebraMap ℚ_[p] L)
    change (1 : L) ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L] (f.app x v + g.app x v) =
      (1 : L) ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L] (f.app x v) +
        (1 : L) ⊗ₜ[ℚ_[p], algebraMap ℚ_[p] L] (g.app x v)
    exact TensorProduct.tmul_add (R := ℚ_[p]) (1 : L) _ _

end AlgebraicGeometry.GroupScheme
