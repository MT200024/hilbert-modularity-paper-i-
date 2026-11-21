/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flatness of the scaled double cover

Each quadratic chart is free of rank two over its affine base chart. The
pullback squares for the two standard opens then give flatness of the actual
glued projection to the projective line.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial LaurentPolynomial

namespace AlgebraicGeometry.DoubleCover

variable {R : Type*} [CommRing R]

/-- A quadratic chart is flat over its base affine line. -/
instance chartProjection_flat (f : R[X]) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R[X] (ChartRing f)))) := by
  rw [Flat.SpecMap_iff]
  change (algebraMap R[X] (ChartRing f)).Flat
  rw [RingHom.flat_algebraMap_iff]
  let : Module.Free R[X] (ChartRing f) := Module.Free.of_basis (chartBasis f)
  exact Module.Flat.of_free

/-- The glued quadratic cover is flat over the projective line. -/
instance toProjectiveLine_flat (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    Flat (toProjectiveLine f g n h) := by
  let : IsZariskiLocalAtTarget (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat)
  apply IsZariskiLocalAtTarget.of_openCover (P := @Flat)
    (ProjectiveLine.standardOpenCover R)
  intro b
  cases b
  · change Flat (pullback.snd (toProjectiveLine f g n h)
      (ProjectiveLine.chartMap R 0 1 (by decide)))
    rw [← (finiteChart_isPullback f g n h).flip.isoPullback_inv_snd]
    infer_instance
  · change Flat (pullback.snd (toProjectiveLine f g n h)
      (ProjectiveLine.chartMap R 1 0 (by decide)))
    rw [← (infinityChart_isPullback f g n h).flip.isoPullback_inv_snd]
    infer_instance

end AlgebraicGeometry.DoubleCover

namespace AlgebraicGeometry.ProjectiveLine

/-- The projective line is flat over its coefficient ring, checked on its standard charts. -/
instance toSpec_flat (R : Type*) [CommRing R] : Flat (toSpec R) := by
  let : IsZariskiLocalAtSource (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat) (standardOpenCover R)
  intro b
  cases b <;>
    (change Flat (chartMap R _ _ (by decide) ≫ toSpec R)
     rw [chartMap_toSpec, Flat.SpecMap_iff]
     change (algebraMap R R[X]).Flat
     rw [RingHom.flat_algebraMap_iff]
     exact Module.Flat.of_free)

end AlgebraicGeometry.ProjectiveLine

namespace HilbertModularity.Hyperelliptic

variable {R : Type*} [CommRing R]

/-- The actual scaled cover is flat over its projective base for every parameter. -/
instance scaledDoubleCoverProjection_flat (P : R[X]) (t : R) :
    AlgebraicGeometry.Flat (scaledDoubleCoverProjection P t) := by
  change AlgebraicGeometry.Flat (AlgebraicGeometry.DoubleCover.toProjectiveLine
    (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
    (P.natDegree + 1) (branch_transition P t))
  infer_instance

/-- The scaled cover is flat over the coefficient ring. -/
instance scaledDoubleCover_toSpec_flat (P : R[X]) (t : R) :
    AlgebraicGeometry.Flat
      (scaledDoubleCoverProjection P t ≫ AlgebraicGeometry.ProjectiveLine.toSpec R) := by
  infer_instance

end HilbertModularity.Hyperelliptic
