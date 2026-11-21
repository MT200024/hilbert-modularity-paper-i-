/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TorsionLocalSystemMaps
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem

/-! # Covariant maps of the actual Tate local systems -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} {A B : CommGrp (Over S)}
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 B).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 B).hom.hom.hom.left]

/-- A group-scheme morphism induces a natural transformation of the actual integral Tate families. -/
def integralTateLocalSystemMap (f : A ⟶ B) :
    integralTateLocalSystem K A p ⟶ integralTateLocalSystem K B p where
  app x := ModuleCat.ofHom (TateModule.map p
    (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive)
  naturality {x y} e := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext n
    have h := congrArg (fun g : (torsionPadicLocalSystem K A p n).obj x ⟶
        (torsionPadicLocalSystem K B p n).obj y => g (v.val n))
      ((torsionPadicLocalSystemMap K p f n).naturality e)
    change (torsionPadicLocalSystemMap K p f n).app y
        ((torsionPadicLocalSystem K A p n).map e (v.val n)) =
      (torsionPadicLocalSystem K B p n).map e
        ((torsionPadicLocalSystemMap K p f n).app x (v.val n)) at h
    have hy := torsionPadicLocalSystemMap_eq K p f n y
      (((torsionPadicLocalSystem K A p n).map e).hom (v.val n))
    have hx := congrArg (fun w : TateModule.Torsion p
        (Additive (Scheme.geometricPointOver K x ⟶ B.X)) n =>
      ((torsionPadicLocalSystem K B p n).map e).hom w)
        (torsionPadicLocalSystemMap_eq K p f n x (v.val n))
    have h' := h.trans hx
    exact hy.symm.trans h' 

/-- The actual integral-family map preserves identity morphisms. -/
@[simp]
theorem integralTateLocalSystemMap_id :
    integralTateLocalSystemMap K p (𝟙 A) = 𝟙 (integralTateLocalSystem K A p) := by
  apply NatTrans.ext
  funext x
  apply ModuleCat.hom_ext
  change TateModule.map p (IsMonHom.monoidHom (𝟙 A.X)
    (Scheme.geometricPointOver K x)).toAdditive = LinearMap.id
  rw [IsMonHom.monoidHom_id]
  exact TateModule.map_id p

/-- Scalar extension of the actual covariant family map gives a rational family map. -/
def rationalTateLocalSystemMap (f : A ⟶ B) :
    rationalTateLocalSystem K A p ⟶ rationalTateLocalSystem K B p where
  app x := ModuleCat.ofHom (((integralTateLocalSystemMap K p f).app x).hom.baseChange ℚ_[p])
  naturality {x y} e := by
    apply ModuleCat.hom_ext
    have h := congrArg ModuleCat.Hom.hom ((integralTateLocalSystemMap K p f).naturality e)
    have he := congrArg (fun z : (integralTateLocalSystem K A p).obj x →ₗ[ℤ_[p]]
      (integralTateLocalSystem K B p).obj y => z.baseChange ℚ_[p]) h
    change (((integralTateLocalSystemMap K p f).app y).hom.baseChange ℚ_[p]).comp
        (((integralTateLocalSystem K A p).map e).hom.baseChange ℚ_[p]) =
      (((integralTateLocalSystem K B p).map e).hom.baseChange ℚ_[p]).comp
        (((integralTateLocalSystemMap K p f).app x).hom.baseChange ℚ_[p])
    simpa only [ModuleCat.hom_comp, LinearMap.baseChange_comp] using he

set_option maxHeartbeats 1000000 in
/-- At a rational point the family map applies the native Tate map of the original point map. -/
@[simp]
theorem rationalTateLocalSystemMap_app_apply (f : A ⟶ B)
    (x : Spec (CommRingCat.of K) ⟶ S)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    ((rationalTateLocalSystemMap K p f).app (Scheme.etaleFiberPoint K S x)).hom v =
      TateModule.rationalMap p
        (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive v := rfl

end AlgebraicGeometry.GroupScheme
