/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberGluing

/-! # Projective components of the square-branch special fibre

The signed component maps agree on the Laurent overlap of the two ordinary
affine charts. These are equalities into the actual scaled double cover.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial LaurentPolynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

def finiteSourceOverlap :
    Spec (CommRingCat.of k[T;T⁻¹]) ⟶ Spec (CommRingCat.of k[X]) :=
  Spec.map (CommRingCat.ofHom toLaurent)

theorem finiteSourceOverlap_eq :
    finiteSourceOverlap (k := k) = Spec.map (CommRingCat.ofHom toLaurent) := (rfl)

def infinitySourceOverlap :
    Spec (CommRingCat.of k[T;T⁻¹]) ⟶ Spec (CommRingCat.of k[X]) :=
  Spec.map (CommRingCat.ofHom (invert.toRingHom.comp toLaurent))

theorem infinitySourceOverlap_eq :
    infinitySourceOverlap (k := k) =
      Spec.map (CommRingCat.ofHom (invert.toRingHom.comp toLaurent)) := (rfl)

instance : IsOpenImmersion (finiteSourceOverlap (k := k)) :=
  IsOpenImmersion.of_isLocalization (X : k[X])

theorem finiteSourceOverlap_opensRange (k : Type*) [Field k] :
    (finiteSourceOverlap (k := k)).opensRange =
      PrimeSpectrum.basicOpen (X : k[X]) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (k[T;T⁻¹]) (X : k[X])

/-- The positive branches agree on the actual cover overlap. -/
theorem positiveComponent_sourceOverlap (P : k[X]) :
    finiteSourceOverlap (k := k) ≫ finitePositiveMap P =
      infinitySourceOverlap (k := k) ≫ infinityPositiveMap P := by
  rw [finitePositiveMap_eq, infinityPositiveMap_eq]
  unfold finiteSourceOverlap infinitySourceOverlap
  change
    (Spec.map (CommRingCat.ofHom toLaurent) ≫
      Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom)) ≫
      AlgebraicGeometry.DoubleCover.finiteChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0) =
    (Spec.map (CommRingCat.ofHom (invert.toRingHom.comp toLaurent)) ≫
      Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom)) ≫
      AlgebraicGeometry.DoubleCover.infinityChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)
  rw [← finitePositiveComponent_overlapInclusion P]
  rw [Category.assoc, AlgebraicGeometry.DoubleCover.overlap_condition]
  rw [← Category.assoc, positiveOverlapComponent_gluing]
  rw [Category.assoc, infinityPositiveComponent_overlapInclusion]
  simp only [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The negative branches agree on the actual cover overlap. -/
theorem negativeComponent_sourceOverlap (P : k[X]) :
    finiteSourceOverlap (k := k) ≫ finiteNegativeMap P =
      infinitySourceOverlap (k := k) ≫ infinityNegativeMap P := by
  rw [finiteNegativeMap_eq, infinityNegativeMap_eq]
  unfold finiteSourceOverlap infinitySourceOverlap
  change
    (Spec.map (CommRingCat.ofHom toLaurent) ≫
      Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom)) ≫
      AlgebraicGeometry.DoubleCover.finiteChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0) =
    (Spec.map (CommRingCat.ofHom (invert.toRingHom.comp toLaurent)) ≫
      Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom)) ≫
      AlgebraicGeometry.DoubleCover.infinityChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)
  rw [← finiteNegativeComponent_overlapInclusion P]
  rw [Category.assoc, AlgebraicGeometry.DoubleCover.overlap_condition]
  rw [← Category.assoc, negativeOverlapComponent_gluing]
  rw [Category.assoc, infinityNegativeComponent_overlapInclusion]
  simp only [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The source chart maps agree on their Laurent overlap. -/
theorem projectiveSourceOverlap (P : k[X]) :
    finiteSourceOverlap (k := k) ≫ ProjectiveLine.chartMap k 0 1 (by decide) =
      infinitySourceOverlap (k := k) ≫ ProjectiveLine.chartMap k 1 0 (by decide) := by
  rw [← finitePositiveMap_projection P, ← infinityPositiveMap_projection P]
  rw [← Category.assoc, ← Category.assoc, positiveComponent_sourceOverlap P]

end HilbertModularity.Hyperelliptic
