/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine
public import HilbertModularity.Geometry.GroupScheme.Isomorphism
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Fibres of a commutative group scheme

A single group scheme over a parameter scheme specializes by actual scheme
pullback. Properness, smooth relative dimension and geometric connectedness
are inherited by its fibres. Their covariant Tate representations and maps
are those of the geometric points of these pullbacks.
This is the family-to-fibre interface used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GroupScheme

universe u

variable {S : Scheme.{u}} (K : Type u) [Field K]
  (A : CommGrp (Over S)) (x : Spec (CommRingCat.of K) ⟶ S)

/-- The fibre of one commutative group scheme at a field-valued parameter. -/
def fiber : CommGrp (Over (Spec (CommRingCat.of K))) :=
  (Over.pullback x).mapCommGrp.obj A

/-- Its underlying structure morphism is the actual scheme pullback projection. -/
@[simp]
theorem fiber_hom : (fiber K A x).X.hom = pullback.snd A.X.hom x := rfl

set_option backward.isDefEq.respectTransparency false in
instance fiber_isProper [IsProper A.X.hom] : IsProper (fiber K A x).X.hom := by
  exact MorphismProperty.baseChange_obj (P := @IsProper) x A.X inferInstance

set_option backward.isDefEq.respectTransparency false in
instance fiber_smooth [Smooth A.X.hom] : Smooth (fiber K A x).X.hom := by
  exact MorphismProperty.baseChange_obj (P := @Smooth) x A.X inferInstance

set_option backward.isDefEq.respectTransparency false in
instance fiber_smoothOfRelativeDimension (d : ℕ) [SmoothOfRelativeDimension d A.X.hom] :
    SmoothOfRelativeDimension d (fiber K A x).X.hom := by
  exact MorphismProperty.baseChange_obj (P := @SmoothOfRelativeDimension d) x A.X inferInstance

set_option backward.isDefEq.respectTransparency false in
instance fiber_geometricallyConnected [GeometricallyConnected A.X.hom] :
    GeometricallyConnected (fiber K A x).X.hom := by
  exact MorphismProperty.baseChange_obj (P := @GeometricallyConnected) x A.X inferInstance

/-- The specialization of a family over the actual three-punctured projective line. -/
def parameterFiber (A : CommGrp (Over (ProjectiveLine.punctured K)))
    (ξ : ProjectiveLine.Parameter K) : CommGrp (Over (Spec (CommRingCat.of K))) :=
  fiber K A (ProjectiveLine.puncturedPoint K ξ)

variable {A} {B : CommGrp (Over S)} (p : ℕ) [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of families induces an actual integral Galois intertwiner on the same fibre. -/
def fiberIntegralTateMap (f : A ⟶ B) :
    (integralTateRepresentation K (fiber K A x).X p).IntertwiningMap
      (integralTateRepresentation K (fiber K B x).X p) :=
  integralTateIntertwiningMap K p ((Over.pullback x).mapCommGrp.map f).hom.hom.hom

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of families induces the covariant rational Tate intertwiner on every fibre. -/
def fiberTateMap (f : A ⟶ B) :
    (tateRepresentation K (fiber K A x).X p).IntertwiningMap
      (tateRepresentation K (fiber K B x).X p) :=
  rationalTateIntertwiningMap K p ((Over.pullback x).mapCommGrp.map f).hom.hom.hom

/-- The integral Galois action on the fibre of a proper smooth family is continuous. -/
theorem continuous_fiber_integralTate [IsProper A.X.hom] [Smooth A.X.hom] :
    Continuous (fun gx : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ×
      integralTate K (fiber K A x).X p =>
        integralTateRepresentation K (fiber K A x).X p gx.1 gx.2) :=
  continuous_integralTateRepresentation K (fiber K A x).X p

/-- The rational covariant Tate action on a characteristic-zero fibre is continuous. -/
theorem continuous_fiber_tate [CharZero K] [IsProper A.X.hom] [Smooth A.X.hom] :
    Continuous (fun gx : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ×
      rationalTate K (fiber K A x).X p =>
        tateRepresentation K (fiber K A x).X p gx.1 gx.2) :=
  continuous_tateRepresentation K (fiber K A x).X p

set_option backward.isDefEq.respectTransparency false in
/-- Fibre specialization and the integral Tate construction respect composition of family maps. -/
@[simp]
theorem fiberIntegralTateMap_comp {C : CommGrp (Over S)} (f : A ⟶ B) (g : B ⟶ C) :
    (fiberIntegralTateMap K x p (f ≫ g)).toLinearMap =
      (fiberIntegralTateMap K x p g).toLinearMap.comp
        (fiberIntegralTateMap K x p f).toLinearMap := by
  simp only [fiberIntegralTateMap, integralTateIntertwiningMap, Functor.map_comp,
    CommGrp.comp_hom, Grp.comp_hom_hom]
  exact integralTateMap_comp K p _ _

set_option backward.isDefEq.respectTransparency false in
/-- Fibre specialization and rationalization respect composition of family maps. -/
@[simp]
theorem fiberTateMap_comp {C : CommGrp (Over S)} (f : A ⟶ B) (g : B ⟶ C) :
    (fiberTateMap K x p (f ≫ g)).toLinearMap =
      (fiberTateMap K x p g).toLinearMap.comp (fiberTateMap K x p f).toLinearMap := by
  simp only [fiberTateMap, rationalTateIntertwiningMap, Functor.map_comp,
    CommGrp.comp_hom, Grp.comp_hom_hom]
  exact rationalTateMap_comp K p _ _


set_option backward.isDefEq.respectTransparency false in
/-- The identity of a family induces the identity on the integral Tate module of a fibre. -/
@[simp]
theorem fiberIntegralTateMap_id :
    (fiberIntegralTateMap K x p (𝟙 A)).toLinearMap = LinearMap.id := by
  simp only [fiberIntegralTateMap, integralTateIntertwiningMap, (Over.pullback x).mapCommGrp.map_id A,
    CommGrp.id_hom, Grp.id_hom_hom]
  exact integralTateMap_id K p (A := (fiber K A x).X)

set_option backward.isDefEq.respectTransparency false in
/-- The identity of a family induces the identity on the rational Tate module of a fibre. -/
@[simp]
theorem fiberTateMap_id :
    (fiberTateMap K x p (𝟙 A)).toLinearMap = LinearMap.id := by
  simp only [fiberTateMap, rationalTateIntertwiningMap, (Over.pullback x).mapCommGrp.map_id A,
    CommGrp.id_hom, Grp.id_hom_hom]
  exact rationalTateMap_id K p (A := (fiber K A x).X)

/-- An isomorphism of families induces the integral Tate equivalence on each fibre. -/
def fiberIntegralTateEquiv (e : A ≅ B) :
    (integralTateRepresentation K (fiber K A x).X p).Equiv
      (integralTateRepresentation K (fiber K B x).X p) :=
  integralTateEquiv K p ((Over.pullback x).mapCommGrp.mapIso e)

/-- An isomorphism of families induces the covariant rational Tate equivalence on each fibre. -/
def fiberTateEquiv (e : A ≅ B) :
    (tateRepresentation K (fiber K A x).X p).Equiv
      (tateRepresentation K (fiber K B x).X p) :=
  tateEquiv K p ((Over.pullback x).mapCommGrp.mapIso e)

end AlgebraicGeometry.GroupScheme
