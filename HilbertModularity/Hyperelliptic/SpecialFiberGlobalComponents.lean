/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberProjectiveComponents
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Global components of the square-branch special fibre

The signed maps from the two affine charts descend across the actual overlap
of the standard affine cover of the projective line.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial LaurentPolynomial
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The opposite standard chart pulls back to the nonzero-coordinate open. -/
theorem finiteChart_preimage_infinityRange :
    ProjectiveLine.chartMap k 0 1 (by decide) ⁻¹ᵁ
        (ProjectiveLine.chartMap k 1 0 (by decide)).opensRange =
      PrimeSpectrum.basicOpen (X : k[X]) := by
  rw [ProjectiveLine.chartMap_opensRange]
  have h (s : MvPolynomial (Fin 2) k) (hs : s.IsHomogeneous 1) :
      ProjectiveLine.chartMap k 0 1 (by decide) ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule (Fin 2) k) s =
        PrimeSpectrum.basicOpen (ProjectiveLine.chartCoordinates k 0 s) :=
    Proj.fromSpecOfUnit_preimage_basicOpen_one (homogeneousSubmodule (Fin 2) k)
      (ProjectiveLine.chartCoordinates k 0)
      (isHomogeneous_X k (1 : Fin 2)) hs
      (by simp [ProjectiveLine.chartCoordinates])
  simpa [ProjectiveLine.chartCoordinates] using h (MvPolynomial.X 0) (isHomogeneous_X k 0)

private theorem chartPair_range :
    Set.range ⇑(pullback.fst
      (ProjectiveLine.chartMap k 0 1 (by decide))
      (ProjectiveLine.chartMap k 1 0 (by decide))) ⊆
      Set.range ⇑(finiteSourceOverlap (k := k)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  let j₀ := ProjectiveLine.chartMap k 0 1 (by decide)
  let j₁ := ProjectiveLine.chartMap k 1 0 (by decide)
  have heq : j₀ (pullback.fst j₀ j₁ y) = j₁ (pullback.snd j₀ j₁ y) := by
    exact congrArg (fun f : pullback j₀ j₁ ⟶ ProjectiveLine k => f y)
      (pullback.condition (f := j₀) (g := j₁))
  have hm : j₀ (pullback.fst j₀ j₁ y) ∈ j₁.opensRange := by
    rw [heq]
    exact ⟨_, rfl⟩
  have hx : pullback.fst j₀ j₁ y ∈ PrimeSpectrum.basicOpen (X : k[X]) := by
    rw [← finiteChart_preimage_infinityRange]
    exact hm
  change pullback.fst j₀ j₁ y ∈ (finiteSourceOverlap (k := k)).opensRange
  rwa [finiteSourceOverlap_opensRange]

private def chartPairToOverlap :
    pullback (ProjectiveLine.chartMap k 0 1 (by decide))
      (ProjectiveLine.chartMap k 1 0 (by decide)) ⟶
      Spec (CommRingCat.of k[T;T⁻¹]) :=
  IsOpenImmersion.lift (finiteSourceOverlap (k := k))
    (pullback.fst (ProjectiveLine.chartMap k 0 1 (by decide))
      (ProjectiveLine.chartMap k 1 0 (by decide))) chartPair_range

private theorem chartPairToOverlap_finite :
    chartPairToOverlap (k := k) ≫ finiteSourceOverlap (k := k) =
      pullback.fst (ProjectiveLine.chartMap k 0 1 (by decide))
        (ProjectiveLine.chartMap k 1 0 (by decide)) :=
  IsOpenImmersion.lift_fac _ _ _

private theorem chartPairToOverlap_infinity :
    chartPairToOverlap (k := k) ≫ infinitySourceOverlap (k := k) =
      pullback.snd (ProjectiveLine.chartMap k 0 1 (by decide))
        (ProjectiveLine.chartMap k 1 0 (by decide)) := by
  apply (cancel_mono (ProjectiveLine.chartMap k 1 0 (by decide))).mp
  rw [Category.assoc, ← projectiveSourceOverlap (P := (0 : k[X]))]
  rw [← Category.assoc, chartPairToOverlap_finite, pullback.condition]

private theorem reverseChartPair_range :
    Set.range ⇑(pullback.snd
      (ProjectiveLine.chartMap k 1 0 (by decide))
      (ProjectiveLine.chartMap k 0 1 (by decide))) ⊆
      Set.range ⇑(finiteSourceOverlap (k := k)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  let j₀ := ProjectiveLine.chartMap k 0 1 (by decide)
  let j₁ := ProjectiveLine.chartMap k 1 0 (by decide)
  have heq : j₁ (pullback.fst j₁ j₀ y) = j₀ (pullback.snd j₁ j₀ y) := by
    exact congrArg (fun f : pullback j₁ j₀ ⟶ ProjectiveLine k => f y)
      (pullback.condition (f := j₁) (g := j₀))
  have hm : j₀ (pullback.snd j₁ j₀ y) ∈ j₁.opensRange := by
    rw [← heq]
    exact ⟨_, rfl⟩
  have hx : pullback.snd j₁ j₀ y ∈ PrimeSpectrum.basicOpen (X : k[X]) := by
    rw [← finiteChart_preimage_infinityRange]
    exact hm
  change pullback.snd j₁ j₀ y ∈ (finiteSourceOverlap (k := k)).opensRange
  rwa [finiteSourceOverlap_opensRange]

private def reverseChartPairToOverlap :
    pullback (ProjectiveLine.chartMap k 1 0 (by decide))
      (ProjectiveLine.chartMap k 0 1 (by decide)) ⟶
      Spec (CommRingCat.of k[T;T⁻¹]) :=
  IsOpenImmersion.lift (finiteSourceOverlap (k := k))
    (pullback.snd (ProjectiveLine.chartMap k 1 0 (by decide))
      (ProjectiveLine.chartMap k 0 1 (by decide))) reverseChartPair_range

private theorem reverseChartPairToOverlap_finite :
    reverseChartPairToOverlap (k := k) ≫ finiteSourceOverlap (k := k) =
      pullback.snd (ProjectiveLine.chartMap k 1 0 (by decide))
        (ProjectiveLine.chartMap k 0 1 (by decide)) :=
  IsOpenImmersion.lift_fac _ _ _

private theorem reverseChartPairToOverlap_infinity :
    reverseChartPairToOverlap (k := k) ≫ infinitySourceOverlap (k := k) =
      pullback.fst (ProjectiveLine.chartMap k 1 0 (by decide))
        (ProjectiveLine.chartMap k 0 1 (by decide)) := by
  apply (cancel_mono (ProjectiveLine.chartMap k 1 0 (by decide))).mp
  rw [Category.assoc, ← projectiveSourceOverlap (P := (0 : k[X]))]
  rw [← Category.assoc, reverseChartPairToOverlap_finite]
  exact (pullback.condition (f := ProjectiveLine.chartMap k 1 0 (by decide))
    (g := ProjectiveLine.chartMap k 0 1 (by decide))).symm

/-- Glue chart maps when they agree on the actual Laurent overlap. -/
def gluedComponent (P : k[X])
    (finite infinity : Spec (CommRingCat.of k[X]) ⟶ scaledDoubleCover P 0)
    (h : finiteSourceOverlap (k := k) ≫ finite =
      infinitySourceOverlap (k := k) ≫ infinity) :
    ProjectiveLine k ⟶ scaledDoubleCover P 0 :=
  (ProjectiveLine.standardOpenCover k).glueMorphisms
    (fun b => match b with | false => finite | true => infinity) (by
      intro i j
      cases i <;> cases j
      · change pullback.fst (ProjectiveLine.chartMap k 0 1 (by decide))
            (ProjectiveLine.chartMap k 0 1 (by decide)) ≫ finite =
          pullback.snd (ProjectiveLine.chartMap k 0 1 (by decide))
            (ProjectiveLine.chartMap k 0 1 (by decide)) ≫ finite
        have : Mono (ProjectiveLine.chartMap k 0 1 (by decide)) :=
          IsOpenImmersion.mono _
        simp only [fst_eq_snd_of_mono_eq]
      · change pullback.fst (ProjectiveLine.chartMap k 0 1 (by decide))
            (ProjectiveLine.chartMap k 1 0 (by decide)) ≫ finite =
          pullback.snd (ProjectiveLine.chartMap k 0 1 (by decide))
            (ProjectiveLine.chartMap k 1 0 (by decide)) ≫ infinity
        let q := chartPairToOverlap (k := k)
        calc
          _ = (q ≫ finiteSourceOverlap (k := k)) ≫ finite := by
            rw [chartPairToOverlap_finite]
          _ = q ≫ (infinitySourceOverlap (k := k) ≫ infinity) := by
            rw [Category.assoc, h]
          _ = _ := by rw [← Category.assoc, chartPairToOverlap_infinity]
      · change pullback.fst (ProjectiveLine.chartMap k 1 0 (by decide))
            (ProjectiveLine.chartMap k 0 1 (by decide)) ≫ infinity =
          pullback.snd (ProjectiveLine.chartMap k 1 0 (by decide))
            (ProjectiveLine.chartMap k 0 1 (by decide)) ≫ finite
        let q := reverseChartPairToOverlap (k := k)
        calc
          _ = (q ≫ infinitySourceOverlap (k := k)) ≫ infinity := by
            rw [reverseChartPairToOverlap_infinity]
          _ = q ≫ (finiteSourceOverlap (k := k) ≫ finite) := by
            rw [Category.assoc, h]
          _ = _ := by rw [← Category.assoc, reverseChartPairToOverlap_finite]
      · change pullback.fst (ProjectiveLine.chartMap k 1 0 (by decide))
            (ProjectiveLine.chartMap k 1 0 (by decide)) ≫ infinity =
          pullback.snd (ProjectiveLine.chartMap k 1 0 (by decide))
            (ProjectiveLine.chartMap k 1 0 (by decide)) ≫ infinity
        have : Mono (ProjectiveLine.chartMap k 1 0 (by decide)) :=
          IsOpenImmersion.mono _
        simp only [fst_eq_snd_of_mono_eq])

/-- The positive projective sheet of the actual square-branch cover. -/
def positiveGlobalComponent (P : k[X]) :
    ProjectiveLine k ⟶ scaledDoubleCover P 0 :=
  gluedComponent P (finitePositiveMap P) (infinityPositiveMap P)
    (positiveComponent_sourceOverlap P)

/-- The negative projective sheet of the actual square-branch cover. -/
def negativeGlobalComponent (P : k[X]) :
    ProjectiveLine k ⟶ scaledDoubleCover P 0 :=
  gluedComponent P (finiteNegativeMap P) (infinityNegativeMap P)
    (negativeComponent_sourceOverlap P)

theorem positiveGlobalComponent_eq (P : k[X]) :
    positiveGlobalComponent P =
      gluedComponent P (finitePositiveMap P) (infinityPositiveMap P)
        (positiveComponent_sourceOverlap P) := (rfl)

theorem negativeGlobalComponent_eq (P : k[X]) :
    negativeGlobalComponent P =
      gluedComponent P (finiteNegativeMap P) (infinityNegativeMap P)
        (negativeComponent_sourceOverlap P) := (rfl)

@[reassoc]
theorem chartMap_comp_gluedComponent_finite (P : k[X])
    (finite infinity : Spec (CommRingCat.of k[X]) ⟶ scaledDoubleCover P 0)
    (h : finiteSourceOverlap (k := k) ≫ finite =
      infinitySourceOverlap (k := k) ≫ infinity) :
    ProjectiveLine.chartMap k 0 1 (by decide) ≫
      gluedComponent P finite infinity h = finite :=
  by
    change (ProjectiveLine.standardOpenCover k).f false ≫
      gluedComponent P finite infinity h = finite
    unfold gluedComponent
    exact (ProjectiveLine.standardOpenCover k).ι_glueMorphisms _ _ false

@[reassoc]
theorem chartMap_comp_gluedComponent_infinity (P : k[X])
    (finite infinity : Spec (CommRingCat.of k[X]) ⟶ scaledDoubleCover P 0)
    (h : finiteSourceOverlap (k := k) ≫ finite =
      infinitySourceOverlap (k := k) ≫ infinity) :
    ProjectiveLine.chartMap k 1 0 (by decide) ≫
      gluedComponent P finite infinity h = infinity :=
  by
    change (ProjectiveLine.standardOpenCover k).f true ≫
      gluedComponent P finite infinity h = infinity
    unfold gluedComponent
    exact (ProjectiveLine.standardOpenCover k).ι_glueMorphisms _ _ true

@[reassoc] theorem chartMap_comp_positiveGlobalComponent_finite (P : k[X]) :
    ProjectiveLine.chartMap k 0 1 (by decide) ≫ positiveGlobalComponent P =
      finitePositiveMap P := by
  rw [positiveGlobalComponent_eq]
  exact chartMap_comp_gluedComponent_finite P _ _ _

@[reassoc] theorem chartMap_comp_negativeGlobalComponent_finite (P : k[X]) :
    ProjectiveLine.chartMap k 0 1 (by decide) ≫ negativeGlobalComponent P =
      finiteNegativeMap P := by
  rw [negativeGlobalComponent_eq]
  exact chartMap_comp_gluedComponent_finite P _ _ _

@[reassoc] theorem chartMap_comp_positiveGlobalComponent_infinity (P : k[X]) :
    ProjectiveLine.chartMap k 1 0 (by decide) ≫ positiveGlobalComponent P =
      infinityPositiveMap P := by
  rw [positiveGlobalComponent_eq]
  exact chartMap_comp_gluedComponent_infinity P _ _ _

@[reassoc] theorem chartMap_comp_negativeGlobalComponent_infinity (P : k[X]) :
    ProjectiveLine.chartMap k 1 0 (by decide) ≫ negativeGlobalComponent P =
      infinityNegativeMap P := by
  rw [negativeGlobalComponent_eq]
  exact chartMap_comp_gluedComponent_infinity P _ _ _

/-- Compatible chart sections glue to a section of the actual cover. -/
theorem gluedComponent_projection (P : k[X])
    (finite infinity : Spec (CommRingCat.of k[X]) ⟶ scaledDoubleCover P 0)
    (h : finiteSourceOverlap (k := k) ≫ finite =
      infinitySourceOverlap (k := k) ≫ infinity)
    (hf : finite ≫ scaledDoubleCoverProjection P 0 =
      ProjectiveLine.chartMap k 0 1 (by decide))
    (hi : infinity ≫ scaledDoubleCoverProjection P 0 =
      ProjectiveLine.chartMap k 1 0 (by decide)) :
    gluedComponent P finite infinity h ≫ scaledDoubleCoverProjection P 0 = 𝟙 _ := by
  apply (ProjectiveLine.standardOpenCover k).hom_ext
  intro b
  cases b
  · change ProjectiveLine.chartMap k 0 1 (by decide) ≫
        (gluedComponent P finite infinity h ≫ scaledDoubleCoverProjection P 0) =
        ProjectiveLine.chartMap k 0 1 (by decide) ≫ 𝟙 _
    rw [← Category.assoc, chartMap_comp_gluedComponent_finite, hf]
    simp
  · change ProjectiveLine.chartMap k 1 0 (by decide) ≫
        (gluedComponent P finite infinity h ≫ scaledDoubleCoverProjection P 0) =
        ProjectiveLine.chartMap k 1 0 (by decide) ≫ 𝟙 _
    rw [← Category.assoc, chartMap_comp_gluedComponent_infinity, hi]
    simp

theorem positiveGlobalComponent_projection (P : k[X]) :
    positiveGlobalComponent P ≫ scaledDoubleCoverProjection P 0 = 𝟙 _ :=
  gluedComponent_projection P _ _ _
    (finitePositiveMap_projection P) (infinityPositiveMap_projection P)

theorem negativeGlobalComponent_projection (P : k[X]) :
    negativeGlobalComponent P ≫ scaledDoubleCoverProjection P 0 = 𝟙 _ :=
  gluedComponent_projection P _ _ _
    (finiteNegativeMap_projection P) (infinityNegativeMap_projection P)

/-- Each global sheet is a closed subscheme of the square-branch cover. -/
instance positiveGlobalComponent_isClosedImmersion (P : k[X]) :
    AlgebraicGeometry.IsClosedImmersion (positiveGlobalComponent P) := by
  have : AlgebraicGeometry.IsFinite (scaledDoubleCoverProjection P 0) := by
    change AlgebraicGeometry.IsFinite (AlgebraicGeometry.DoubleCover.toProjectiveLine
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0))
    infer_instance
  have : AlgebraicGeometry.IsSeparated (scaledDoubleCoverProjection P 0) := inferInstance
  have : AlgebraicGeometry.IsClosedImmersion
      (positiveGlobalComponent P ≫ scaledDoubleCoverProjection P 0) := by
    rw [positiveGlobalComponent_projection]
    infer_instance
  exact AlgebraicGeometry.IsClosedImmersion.of_comp
    (positiveGlobalComponent P) (scaledDoubleCoverProjection P 0)

instance negativeGlobalComponent_isClosedImmersion (P : k[X]) :
    AlgebraicGeometry.IsClosedImmersion (negativeGlobalComponent P) := by
  have : AlgebraicGeometry.IsFinite (scaledDoubleCoverProjection P 0) := by
    change AlgebraicGeometry.IsFinite (AlgebraicGeometry.DoubleCover.toProjectiveLine
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0))
    infer_instance
  have : AlgebraicGeometry.IsSeparated (scaledDoubleCoverProjection P 0) := inferInstance
  have : AlgebraicGeometry.IsClosedImmersion
      (negativeGlobalComponent P ≫ scaledDoubleCoverProjection P 0) := by
    rw [negativeGlobalComponent_projection]
    infer_instance
  exact AlgebraicGeometry.IsClosedImmersion.of_comp
    (negativeGlobalComponent P) (scaledDoubleCoverProjection P 0)

end HilbertModularity.Hyperelliptic
