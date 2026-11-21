/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberComponents

/-! # Laurent overlap of the two special-fibre components

The two signed component evaluations commute with the actual reciprocal
transition of the scaled double cover.  The identities below are equalities
of algebra maps, so they can be used to glue scheme morphisms.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial LaurentPolynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- Evaluation of a square-branch overlap at the positive square root. -/
def positiveOverlapComponent (f H : k[X]) (hf : f = H ^ 2) :
    AlgebraicGeometry.DoubleCover.OverlapRing f →ₐ[k] k[T;T⁻¹] where
  toFun z := z.re + z.im * toLaurent H
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    simp only [hf, LaurentPolynomial.algebraMap_eq_toLaurent, map_pow, map_zero]
    ring
  commutes' r := by simp

/-- Evaluation of a square-branch overlap at the negative square root. -/
def negativeOverlapComponent (f H : k[X]) (hf : f = H ^ 2) :
    AlgebraicGeometry.DoubleCover.OverlapRing f →ₐ[k] k[T;T⁻¹] where
  toFun z := z.re - z.im * toLaurent H
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    simp only [hf, LaurentPolynomial.algebraMap_eq_toLaurent, map_pow, map_zero]
    ring
  commutes' r := by simp

/-- Restriction of the positive affine component to the Laurent overlap. -/
theorem positiveOverlapComponent_localize (H : k[X]) :
    (positiveOverlapComponent (H ^ 2) H rfl).toRingHom.comp
      (algebraMap (AlgebraicGeometry.DoubleCover.ChartRing (H ^ 2))
        (AlgebraicGeometry.DoubleCover.OverlapRing (H ^ 2))) =
      toLaurent.comp (positiveComponent H).toRingHom := by
  apply RingHom.ext
  intro z
  change (algebraMap (SquareBranchRing H)
      (AlgebraicGeometry.DoubleCover.OverlapRing (H ^ 2)) z).re +
      (algebraMap (SquareBranchRing H)
        (AlgebraicGeometry.DoubleCover.OverlapRing (H ^ 2)) z).im * toLaurent H =
    toLaurent (positiveComponent H z)
  rw [positiveComponent_apply]
  simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
    QuadraticAlgebra.mapCoeffs, map_add, map_mul]

/-- Restriction of the negative affine component to the Laurent overlap. -/
theorem negativeOverlapComponent_localize (H : k[X]) :
    (negativeOverlapComponent (H ^ 2) H rfl).toRingHom.comp
      (algebraMap (AlgebraicGeometry.DoubleCover.ChartRing (H ^ 2))
        (AlgebraicGeometry.DoubleCover.OverlapRing (H ^ 2))) =
      toLaurent.comp (negativeComponent H).toRingHom := by
  apply RingHom.ext
  intro z
  change (algebraMap (SquareBranchRing H)
      (AlgebraicGeometry.DoubleCover.OverlapRing (H ^ 2)) z).re -
      (algebraMap (SquareBranchRing H)
        (AlgebraicGeometry.DoubleCover.OverlapRing (H ^ 2)) z).im * toLaurent H =
    toLaurent (negativeComponent H z)
  rw [negativeComponent_apply]
  simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
    QuadraticAlgebra.mapCoeffs, map_sub, map_mul]

/-- The Laurent restriction of a positive branch is the overlap restriction. -/
theorem positiveComponent_overlapInclusion (H : k[X]) :
    Spec.map (CommRingCat.ofHom
        (positiveOverlapComponent (H ^ 2) H rfl).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusion (H ^ 2) =
    Spec.map (CommRingCat.ofHom toLaurent) ≫
      Spec.map (CommRingCat.ofHom (positiveComponent H).toRingHom) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (positiveOverlapComponent_localize H)

/-- The Laurent restriction of a negative branch is the overlap restriction. -/
theorem negativeComponent_overlapInclusion (H : k[X]) :
    Spec.map (CommRingCat.ofHom
        (negativeOverlapComponent (H ^ 2) H rfl).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusion (H ^ 2) =
    Spec.map (CommRingCat.ofHom toLaurent) ≫
      Spec.map (CommRingCat.ofHom (negativeComponent H).toRingHom) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (negativeOverlapComponent_localize H)

/-- The finite positive component agrees with its signed Laurent evaluation. -/
theorem finitePositiveComponent_overlapInclusion (P : k[X]) :
    Spec.map (CommRingCat.ofHom
        (positiveOverlapComponent (finiteBranchPolynomial P 0)
          (finiteComponentPolynomial P) (finiteBranchPolynomial_zero P)).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusion (finiteBranchPolynomial P 0) =
    Spec.map (CommRingCat.ofHom toLaurent) ≫
      Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (by
    apply RingHom.ext
    intro z
    change (algebraMap
      (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0))
      (AlgebraicGeometry.DoubleCover.OverlapRing (finiteBranchPolynomial P 0)) z).re +
      (algebraMap
        (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0))
        (AlgebraicGeometry.DoubleCover.OverlapRing (finiteBranchPolynomial P 0)) z).im *
        toLaurent (finiteComponentPolynomial P) =
      toLaurent (finitePositiveComponent P z)
    rw [finitePositiveComponent_apply]
    simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs, map_add, map_mul])

/-- The finite negative component restricts to its signed Laurent evaluation. -/
theorem finiteNegativeComponent_overlapInclusion (P : k[X]) :
    Spec.map (CommRingCat.ofHom
        (negativeOverlapComponent (finiteBranchPolynomial P 0)
          (finiteComponentPolynomial P) (finiteBranchPolynomial_zero P)).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusion (finiteBranchPolynomial P 0) =
    Spec.map (CommRingCat.ofHom toLaurent) ≫
      Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (by
    apply RingHom.ext
    intro z
    change (algebraMap
      (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0))
      (AlgebraicGeometry.DoubleCover.OverlapRing (finiteBranchPolynomial P 0)) z).re -
      (algebraMap
        (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0))
        (AlgebraicGeometry.DoubleCover.OverlapRing (finiteBranchPolynomial P 0)) z).im *
        toLaurent (finiteComponentPolynomial P) =
      toLaurent (finiteNegativeComponent P z)
    rw [finiteNegativeComponent_apply]
    simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs, map_sub, map_mul])

/-- The reciprocal positive component restricts to its signed Laurent evaluation. -/
theorem infinityPositiveComponent_overlapInclusion (P : k[X]) :
    Spec.map (CommRingCat.ofHom
        (positiveOverlapComponent (infinityBranchPolynomial P 0)
          (infinityComponentPolynomial P) (infinityBranchPolynomial_zero P)).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusion (infinityBranchPolynomial P 0) =
    Spec.map (CommRingCat.ofHom toLaurent) ≫
      Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (by
    apply RingHom.ext
    intro z
    change (algebraMap
      (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0))
      (AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P 0)) z).re +
      (algebraMap
        (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0))
        (AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P 0)) z).im *
        toLaurent (infinityComponentPolynomial P) =
      toLaurent (infinityPositiveComponent P z)
    rw [infinityPositiveComponent_apply]
    simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs, map_add, map_mul])

/-- The reciprocal negative component restricts to its signed Laurent evaluation. -/
theorem infinityNegativeComponent_overlapInclusion (P : k[X]) :
    Spec.map (CommRingCat.ofHom
        (negativeOverlapComponent (infinityBranchPolynomial P 0)
          (infinityComponentPolynomial P) (infinityBranchPolynomial_zero P)).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusion (infinityBranchPolynomial P 0) =
    Spec.map (CommRingCat.ofHom toLaurent) ≫
      Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (by
    apply RingHom.ext
    intro z
    change (algebraMap
      (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0))
      (AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P 0)) z).re -
      (algebraMap
        (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0))
        (AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P 0)) z).im *
        toLaurent (infinityComponentPolynomial P) =
      toLaurent (infinityNegativeComponent P z)
    rw [infinityNegativeComponent_apply]
    simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs, map_sub, map_mul])

/-- The positive evaluation intertwines the actual double-cover transition
with inversion of the Laurent coordinate. -/
theorem positiveOverlapComponent_transition (P : k[X]) :
    (positiveOverlapComponent (finiteBranchPolynomial P 0)
      (finiteComponentPolynomial P) (finiteBranchPolynomial_zero P)).toRingHom.comp
      (AlgebraicGeometry.DoubleCover.transition
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)).toRingHom =
      invert.toRingHom.comp
        (positiveOverlapComponent (infinityBranchPolynomial P 0)
          (infinityComponentPolynomial P) (infinityBranchPolynomial_zero P)).toRingHom := by
  apply RingHom.ext
  intro z
  change
    (AlgebraicGeometry.DoubleCover.transition
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0) z).re +
      (AlgebraicGeometry.DoubleCover.transition
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0) z).im *
        toLaurent (finiteComponentPolynomial P) =
      invert (z.re + z.im * toLaurent (infinityComponentPolynomial P))
  exact positiveComponent_overlap P z

/-- The negative evaluation obeys the same transition. -/
theorem negativeOverlapComponent_transition (P : k[X]) :
    (negativeOverlapComponent (finiteBranchPolynomial P 0)
      (finiteComponentPolynomial P) (finiteBranchPolynomial_zero P)).toRingHom.comp
      (AlgebraicGeometry.DoubleCover.transition
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)).toRingHom =
      invert.toRingHom.comp
        (negativeOverlapComponent (infinityBranchPolynomial P 0)
          (infinityComponentPolynomial P) (infinityBranchPolynomial_zero P)).toRingHom := by
  apply RingHom.ext
  intro z
  change
    (AlgebraicGeometry.DoubleCover.transition
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0) z).re -
      (AlgebraicGeometry.DoubleCover.transition
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0) z).im *
        toLaurent (finiteComponentPolynomial P) =
      invert (z.re - z.im * toLaurent (infinityComponentPolynomial P))
  exact negativeComponent_overlap P z

/-- The positive component agrees on the actual gluing span of the scaled cover. -/
theorem positiveOverlapComponent_gluing (P : k[X]) :
    Spec.map (CommRingCat.ofHom
        (positiveOverlapComponent (finiteBranchPolynomial P 0)
          (finiteComponentPolynomial P) (finiteBranchPolynomial_zero P)).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusionInfinity
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0) =
    Spec.map (CommRingCat.ofHom invert.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (positiveOverlapComponent (infinityBranchPolynomial P 0)
          (infinityComponentPolynomial P) (infinityBranchPolynomial_zero P)).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusion (infinityBranchPolynomial P 0) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusionInfinity
  rw [← Category.assoc]
  have htransition :
      (AlgebraicGeometry.DoubleCover.transition
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)).toCommRingCatIso.hom =
      CommRingCat.ofHom
        (AlgebraicGeometry.DoubleCover.transition
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0)).toRingHom := by
    rfl
  rw [htransition]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((positiveOverlapComponent (finiteBranchPolynomial P 0)
        (finiteComponentPolynomial P) (finiteBranchPolynomial_zero P)).toRingHom.comp
        (AlgebraicGeometry.DoubleCover.transition
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0)).toRingHom)) ≫ _ = _
  rw [positiveOverlapComponent_transition]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The negative component agrees on the actual gluing span of the scaled cover. -/
theorem negativeOverlapComponent_gluing (P : k[X]) :
    Spec.map (CommRingCat.ofHom
        (negativeOverlapComponent (finiteBranchPolynomial P 0)
          (finiteComponentPolynomial P) (finiteBranchPolynomial_zero P)).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusionInfinity
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0) =
    Spec.map (CommRingCat.ofHom invert.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (negativeOverlapComponent (infinityBranchPolynomial P 0)
          (infinityComponentPolynomial P) (infinityBranchPolynomial_zero P)).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.overlapInclusion (infinityBranchPolynomial P 0) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusionInfinity
  rw [← Category.assoc]
  have htransition :
      (AlgebraicGeometry.DoubleCover.transition
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)).toCommRingCatIso.hom =
      CommRingCat.ofHom
        (AlgebraicGeometry.DoubleCover.transition
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0)).toRingHom := by
    rfl
  rw [htransition]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((negativeOverlapComponent (finiteBranchPolynomial P 0)
        (finiteComponentPolynomial P) (finiteBranchPolynomial_zero P)).toRingHom.comp
        (AlgebraicGeometry.DoubleCover.transition
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0)).toRingHom)) ≫ _ = _
  rw [negativeOverlapComponent_transition]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end HilbertModularity.Hyperelliptic
