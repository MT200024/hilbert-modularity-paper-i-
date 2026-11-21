/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberComponentTopology
public import HilbertModularity.Hyperelliptic.SpecialFiberGlobalIntersection
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The finite map from the two projective sheets

The coproduct of the two signed projective components maps to the actual
square-branch special fibre. Finiteness and surjectivity are established here;
identifying this map as a normalization requires the local nodal calculation.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The canonical map from the two projective sheets to the actual special fibre. -/
def specialFiberComponentCoproductMap (P : k[X]) :
    ProjectiveLine k ⨿ ProjectiveLine k ⟶ scaledDoubleCover P 0 :=
  coprod.desc (positiveGlobalComponent P) (negativeGlobalComponent P)

@[reassoc] theorem positiveComponent_comp_coproductMap (P : k[X]) :
    coprod.inl ≫ specialFiberComponentCoproductMap P =
      positiveGlobalComponent P := coprod.inl_desc _ _

@[reassoc] theorem negativeComponent_comp_coproductMap (P : k[X]) :
    coprod.inr ≫ specialFiberComponentCoproductMap P =
      negativeGlobalComponent P := coprod.inr_desc _ _

/-- The map from both projective sheets is finite. -/
instance specialFiberComponentCoproductMap_isFinite (P : k[X]) :
    IsFinite (specialFiberComponentCoproductMap P) := by
  unfold specialFiberComponentCoproductMap
  infer_instance

/-- The two components jointly cover every point of the actual special fibre. -/
theorem specialFiberComponentCoproductMap_surjective (P : k[X])
    (hP : P.Monic) (h2 : (2 : k) ≠ 0) :
    Function.Surjective (specialFiberComponentCoproductMap P) := by
  intro x
  rcases globalComponents_jointly_surjective P hP h2 x with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine ⟨(coprod.inl : ProjectiveLine k ⟶ _) y, ?_⟩
    simpa only [← Scheme.Hom.comp_apply, positiveComponent_comp_coproductMap] using hy
  · refine ⟨(coprod.inr : ProjectiveLine k ⟶ _) y, ?_⟩
    simpa only [← Scheme.Hom.comp_apply, negativeComponent_comp_coproductMap] using hy

theorem specialFiberComponentCoproductMap_isSurjective (P : k[X])
    (hP : P.Monic) (h2 : (2 : k) ≠ 0) :
    Surjective (specialFiberComponentCoproductMap P) :=
  Surjective.mk (specialFiberComponentCoproductMap_surjective P hP h2)

/-- A signed projective sheet is embedded on points, as its composite with
the cover projection is the identity of the projective line. -/
theorem positiveGlobalComponent_injective (P : k[X]) :
    Function.Injective (positiveGlobalComponent P) := by
  intro y y' h
  have hbase := congrArg (scaledDoubleCoverProjection P 0) h
  simp only [← Scheme.Hom.comp_apply, positiveGlobalComponent_projection] at hbase
  simpa using hbase

theorem negativeGlobalComponent_injective (P : k[X]) :
    Function.Injective (negativeGlobalComponent P) := by
  intro y y' h
  have hbase := congrArg (scaledDoubleCoverProjection P 0) h
  simp only [← Scheme.Hom.comp_apply, negativeGlobalComponent_projection] at hbase
  simpa using hbase

/-- The only identifications made by the two-component map are between the
two signs at the same point over the finite branch divisor. This also rules
out additional identifications at nonclosed scheme points. -/
theorem globalComponents_eq_iff_finiteBranch (P : k[X])
    (hP : P.Monic) (h2 : (2 : k) ≠ 0) (y y' : ProjectiveLine k) :
    positiveGlobalComponent P y = negativeGlobalComponent P y' ↔
      y = y' ∧ ∃ q : Spec (CommRingCat.of k[X]),
        ProjectiveLine.chartMap k 0 1 (by decide) q = y ∧
          finiteComponentPolynomial P ∈ q.asIdeal := by
  constructor
  · intro h
    have hbase := congrArg (scaledDoubleCoverProjection P 0) h
    have hyy : y = y' := by
      simp only [← Scheme.Hom.comp_apply, positiveGlobalComponent_projection,
        negativeGlobalComponent_projection] at hbase
      simpa using hbase
    subst y'
    obtain ⟨q, hq⟩ := globalSignedPoint_eq_implies_finite P hP h2 y h
    refine ⟨rfl, q, hq, ?_⟩
    apply (finiteSignedChartPoint_eq_iff P h2 q).mp
    rw [← hq] at h
    simpa only [← Scheme.Hom.comp_apply,
      chartMap_comp_positiveGlobalComponent_finite,
      chartMap_comp_negativeGlobalComponent_finite] using h
  · rintro ⟨rfl, q, hq, hbranch⟩
    rw [← hq]
    simpa only [← Scheme.Hom.comp_apply,
      chartMap_comp_positiveGlobalComponent_finite,
      chartMap_comp_negativeGlobalComponent_finite] using
      (finiteSignedChartPoint_eq_iff P h2 q).mpr hbranch

/-- For a split branch divisor, precisely the listed rational parameters
identify the two projective sheets. -/
theorem globalComponents_eq_iff_splitCrossings [DecidableEq k]
    (P : k[X]) (S : Finset k) (hP : P.Monic) (h2 : (2 : k) ≠ 0)
    (hsplit : P = ∏ x ∈ S, (X - C x)) (y y' : ProjectiveLine k) :
    positiveGlobalComponent P y = negativeGlobalComponent P y' ↔
      y = y' ∧ ∃ x ∈ insert 0 S,
        y = ProjectiveLine.chartMap k 0 1 (by decide) (finiteRootPoint x) := by
  constructor
  · intro h
    have hyy := (globalComponents_eq_iff_finiteBranch P hP h2 y y').mp h |>.1
    subst y'
    have hz : positiveGlobalComponent P y ∈
        Set.range ⇑(positiveGlobalComponent P) ∩
          Set.range ⇑(negativeGlobalComponent P) :=
      ⟨⟨y, rfl⟩, ⟨y, h.symm⟩⟩
    rw [globalComponent_ranges_inter_eq_splitCrossings P S hP h2 hsplit] at hz
    obtain ⟨x, hx, heq⟩ := hz
    refine ⟨rfl, x, hx, ?_⟩
    apply positiveGlobalComponent_injective P
    rw [heq]
    simp only [← Scheme.Hom.comp_apply,
      chartMap_comp_positiveGlobalComponent_finite]
  · rintro ⟨rfl, x, hx, rfl⟩
    apply (globalComponents_eq_iff_finiteBranch P hP h2 _ _).mpr
    refine ⟨rfl, finiteRootPoint x, rfl, ?_⟩
    rw [finiteComponentPolynomial_eq_split P S hsplit,
      mem_finiteRootPoint_asIdeal_iff]
    exact (splitFiniteBranchPolynomial_root_iff S x).mpr
      (Finset.mem_insert.mp hx)

end HilbertModularity.Hyperelliptic
