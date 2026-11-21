/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.ArithmeticField
public import HilbertModularity.Geometry.Etale.Pullback

/-! # Geometric base change at a specified geometric point

The base is extended to its actual algebraic closure. An embedding of that
closure into the geometric residue field lifts the original point to this
scheme pullback. No fundamental-group exact sequence is assumed here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
universe u
variable (K F : Type u) [Field K] [Field F] [Algebra K F]
  {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of K))
  (x : Spec (CommRingCat.of F) ⟶ S) (hx : x ≫ f = Spec.algebraMap K F)
  (j : AlgebraicClosure K →ₐ[K] AlgebraicClosure F)

/-- The actual extension of the base scheme to the algebraic closure of its ground field. -/
abbrev geometricBaseChange := pullback f (Spec.algebraMap K (AlgebraicClosure K))

include hx in
/-- The geometric residue-field point and the embedded constant closure form a commuting square. -/
theorem geometricPointOver_baseChange_condition :
    (geometricPointOver F x).hom ≫ f =
      Spec.map (CommRingCat.ofHom j.toRingHom) ≫ Spec.algebraMap K (AlgebraicClosure K) := by
  have hj : CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) ≫
      CommRingCat.ofHom j.toRingHom =
      CommRingCat.ofHom (algebraMap K F) ≫
        CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)) := by
    ext a
    exact (j.commutes a).trans (IsScalarTower.algebraMap_apply K F (AlgebraicClosure F) a)
  change (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))) ≫ x) ≫ f = _
  rw [Category.assoc, hx]
  change Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K F)) =
      Spec.map (CommRingCat.ofHom j.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  rw [← Spec.map_comp, ← Spec.map_comp, hj]

/-- The specified geometric point lifts to the actual geometric base change. -/
def geometricBaseChangePoint :
    Spec (CommRingCat.of (AlgebraicClosure F)) ⟶ geometricBaseChange K f :=
  pullback.lift (geometricPointOver F x).hom (Spec.map (CommRingCat.ofHom j.toRingHom))
    (geometricPointOver_baseChange_condition K F f x hx j)

/-- Projection of the lifted point is the original geometric point. -/
@[reassoc, simp] theorem geometricBaseChangePoint_fst :
    geometricBaseChangePoint K F f x hx j ≫ pullback.fst f
      (Spec.algebraMap K (AlgebraicClosure K)) = (geometricPointOver F x).hom :=
  pullback.lift_fst _ _ _

/-- The lifted point is defined over the specified embedded algebraic closure of constants. -/
@[reassoc, simp] theorem geometricBaseChangePoint_snd :
    geometricBaseChangePoint K F f x hx j ≫ pullback.snd f
      (Spec.algebraMap K (AlgebraicClosure K)) = Spec.map (CommRingCat.ofHom j.toRingHom) :=
  pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme
