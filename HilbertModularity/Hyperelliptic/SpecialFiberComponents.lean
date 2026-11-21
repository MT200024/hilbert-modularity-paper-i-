/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCharts
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Component maps of the scaled double cover at parameter zero

The four maps below are morphisms into the actual glued double cover.  On each
affine chart their restrictions are closed immersions, since evaluation at a
chosen square root of the branch polynomial is a surjective ring map.  Global
closedness and the scheme-theoretic intersection require a separate gluing
argument.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

theorem positiveComponent_surjective (H : k[X]) :
    Function.Surjective (positiveComponent H) := by
  intro f
  refine ⟨algebraMap k[X] (SquareBranchRing H) f, ?_⟩
  simp [positiveComponent_apply]

theorem negativeComponent_surjective (H : k[X]) :
    Function.Surjective (negativeComponent H) := by
  intro f
  refine ⟨algebraMap k[X] (SquareBranchRing H) f, ?_⟩
  simp [negativeComponent_apply]

/-- The positive component of the finite chart as a map to the actual special fibre. -/
def finitePositiveMap (P : k[X]) :
    Spec (CommRingCat.of k[X]) ⟶ scaledDoubleCover P 0 :=
  Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom) ≫
    AlgebraicGeometry.DoubleCover.finiteChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)

theorem finitePositiveMap_eq (P : k[X]) :
    finitePositiveMap P =
      Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom) ≫
        AlgebraicGeometry.DoubleCover.finiteChart
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0) := (rfl)

/-- The negative component of the finite chart as a map to the actual special fibre. -/
def finiteNegativeMap (P : k[X]) :
    Spec (CommRingCat.of k[X]) ⟶ scaledDoubleCover P 0 :=
  Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom) ≫
    AlgebraicGeometry.DoubleCover.finiteChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)

theorem finiteNegativeMap_eq (P : k[X]) :
    finiteNegativeMap P =
      Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom) ≫
        AlgebraicGeometry.DoubleCover.finiteChart
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0) := (rfl)

/-- The positive component of the reciprocal chart as a map to the actual special fibre. -/
def infinityPositiveMap (P : k[X]) :
    Spec (CommRingCat.of k[X]) ⟶ scaledDoubleCover P 0 :=
  Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom) ≫
    AlgebraicGeometry.DoubleCover.infinityChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)

theorem infinityPositiveMap_eq (P : k[X]) :
    infinityPositiveMap P =
      Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom) ≫
        AlgebraicGeometry.DoubleCover.infinityChart
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0) := (rfl)

/-- The negative component of the reciprocal chart as a map to the actual special fibre. -/
def infinityNegativeMap (P : k[X]) :
    Spec (CommRingCat.of k[X]) ⟶ scaledDoubleCover P 0 :=
  Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom) ≫
    AlgebraicGeometry.DoubleCover.infinityChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)

theorem infinityNegativeMap_eq (P : k[X]) :
    infinityNegativeMap P =
      Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom) ≫
        AlgebraicGeometry.DoubleCover.infinityChart
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0) := (rfl)

/-- The positive finite branch projects to the ordinary affine chart of the base line. -/
theorem finitePositiveMap_projection (P : k[X]) :
    finitePositiveMap P ≫ scaledDoubleCoverProjection P 0 =
      ProjectiveLine.chartMap k 0 1 (by decide) := by
  unfold finitePositiveMap scaledDoubleCoverProjection scaledDoubleCover
  rw [Category.assoc, AlgebraicGeometry.DoubleCover.finiteChart_toProjectiveLine,
    AlgebraicGeometry.DoubleCover.finiteProjection_factor]
  rw [← Category.assoc, ← Spec.map_comp]
  have h : (finitePositiveComponent P).toRingHom.comp
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial P 0))) = RingHom.id k[X] := by
    apply RingHom.ext
    intro f
    exact finitePositiveComponent_base P f
  change Spec.map (CommRingCat.ofHom ((finitePositiveComponent P).toRingHom.comp
    (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
      (finiteBranchPolynomial P 0))))) ≫ _ = _
  rw [h]
  simp

/-- The negative finite branch has the same base projection. -/
theorem finiteNegativeMap_projection (P : k[X]) :
    finiteNegativeMap P ≫ scaledDoubleCoverProjection P 0 =
      ProjectiveLine.chartMap k 0 1 (by decide) := by
  unfold finiteNegativeMap scaledDoubleCoverProjection scaledDoubleCover
  rw [Category.assoc, AlgebraicGeometry.DoubleCover.finiteChart_toProjectiveLine,
    AlgebraicGeometry.DoubleCover.finiteProjection_factor]
  rw [← Category.assoc, ← Spec.map_comp]
  have h : (finiteNegativeComponent P).toRingHom.comp
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial P 0))) = RingHom.id k[X] := by
    apply RingHom.ext
    intro f
    exact finiteNegativeComponent_base P f
  change Spec.map (CommRingCat.ofHom ((finiteNegativeComponent P).toRingHom.comp
    (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
      (finiteBranchPolynomial P 0))))) ≫ _ = _
  rw [h]
  simp

/-- The positive reciprocal branch projects to the chart at infinity. -/
theorem infinityPositiveMap_projection (P : k[X]) :
    infinityPositiveMap P ≫ scaledDoubleCoverProjection P 0 =
      ProjectiveLine.chartMap k 1 0 (by decide) := by
  unfold infinityPositiveMap scaledDoubleCoverProjection scaledDoubleCover
  rw [Category.assoc, AlgebraicGeometry.DoubleCover.infinityChart_toProjectiveLine,
    AlgebraicGeometry.DoubleCover.infinityProjection_factor]
  rw [← Category.assoc, ← Spec.map_comp]
  have h : (infinityPositiveComponent P).toRingHom.comp
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial P 0))) = RingHom.id k[X] := by
    apply RingHom.ext
    intro f
    exact infinityPositiveComponent_base P f
  change Spec.map (CommRingCat.ofHom ((infinityPositiveComponent P).toRingHom.comp
    (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
      (infinityBranchPolynomial P 0))))) ≫ _ = _
  rw [h]
  simp

/-- The negative reciprocal branch projects to the chart at infinity. -/
theorem infinityNegativeMap_projection (P : k[X]) :
    infinityNegativeMap P ≫ scaledDoubleCoverProjection P 0 =
      ProjectiveLine.chartMap k 1 0 (by decide) := by
  unfold infinityNegativeMap scaledDoubleCoverProjection scaledDoubleCover
  rw [Category.assoc, AlgebraicGeometry.DoubleCover.infinityChart_toProjectiveLine,
    AlgebraicGeometry.DoubleCover.infinityProjection_factor]
  rw [← Category.assoc, ← Spec.map_comp]
  have h : (infinityNegativeComponent P).toRingHom.comp
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial P 0))) = RingHom.id k[X] := by
    apply RingHom.ext
    intro f
    exact infinityNegativeComponent_base P f
  change Spec.map (CommRingCat.ofHom ((infinityNegativeComponent P).toRingHom.comp
    (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
      (infinityBranchPolynomial P 0))))) ≫ _ = _
  rw [h]
  simp

theorem finitePositiveComponent_surjective (P : k[X]) :
    Function.Surjective (finitePositiveComponent P) := by
  intro f
  exact ⟨algebraMap k[X] _ f, finitePositiveComponent_base P f⟩

theorem finiteNegativeComponent_surjective (P : k[X]) :
    Function.Surjective (finiteNegativeComponent P) := by
  intro f
  exact ⟨algebraMap k[X] _ f, finiteNegativeComponent_base P f⟩

theorem infinityPositiveComponent_surjective (P : k[X]) :
    Function.Surjective (infinityPositiveComponent P) := by
  intro f
  exact ⟨algebraMap k[X] _ f, infinityPositiveComponent_base P f⟩

theorem infinityNegativeComponent_surjective (P : k[X]) :
    Function.Surjective (infinityNegativeComponent P) := by
  intro f
  exact ⟨algebraMap k[X] _ f, infinityNegativeComponent_base P f⟩

instance finitePositiveComponent_isClosedImmersion (P : k[X]) :
    AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom)) :=
  AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (finitePositiveComponent_surjective P)

instance finiteNegativeComponent_isClosedImmersion (P : k[X]) :
    AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom)) :=
  AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (finiteNegativeComponent_surjective P)

instance infinityPositiveComponent_isClosedImmersion (P : k[X]) :
    AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom)) :=
  AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (infinityPositiveComponent_surjective P)

instance infinityNegativeComponent_isClosedImmersion (P : k[X]) :
    AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom)) :=
  AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (infinityNegativeComponent_surjective P)

end HilbertModularity.Hyperelliptic
