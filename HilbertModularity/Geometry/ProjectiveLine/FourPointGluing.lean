/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.FourPointCover
public import HilbertModularity.Geometry.Scheme.CommonOpenGluing

/-! # Reconstruction of the projective line from four branch neighbourhoods

The four target neighbourhoods of [TripathiGoswamiRevised, Definition 2.3]
meet in the complement of the four branch sections. Gluing those actual open
subschemes along their common complement recovers the target projective line.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveLine

universe u

variable (R : Type u) [CommRing R] (t : R)

-- The common-open gluing API uses one universe for its index and its schemes.

/-- The common four-point complement, included in a branch neighbourhood. -/
@[expose]
def fourPointToBranch (i : FourPointBranch) :
    fourPointComplement R t ⟶ branchNeighbourhood R t i :=
  (ProjectiveLine R).homOfLE (by
    rw [fourPointOpen_eq_branchOpen_inf R t i]
    exact inf_le_left)

instance fourPointToBranch_isOpenImmersion (i : FourPointBranch) :
    IsOpenImmersion (fourPointToBranch R t i) :=
  inferInstanceAs (IsOpenImmersion ((ProjectiveLine R).homOfLE (by
    rw [fourPointOpen_eq_branchOpen_inf R t i]
    exact inf_le_left)))

/-- Each common-open inclusion agrees with the inclusion in the target line. -/
@[reassoc (attr := simp)]
theorem fourPointToBranch_comp_inclusion (i : FourPointBranch) :
    fourPointToBranch R t i ≫ branchInclusion R t i = fourPointInclusion R t :=
  by
    unfold fourPointToBranch branchInclusion fourPointInclusion
    exact Scheme.homOfLE_ι _ _

/-- The target line reconstructed by gluing its four branch neighbourhoods. -/
@[expose]
def fourPointGlued (R : Type u) [CommRing R] (t : R) : Scheme :=
  @Scheme.commonOpenGlued (ULift.{u} FourPointBranch) (fourPointComplement R t)
    (fun i => branchNeighbourhood R t i.down)
    (fun i => fourPointToBranch R t i.down)
    (fun i => fourPointToBranch_isOpenImmersion R t i.down)

/-- Inclusion of a branch neighbourhood in the reconstructed target. -/
@[expose]
def fourPointGluedChart (i : FourPointBranch) :
    branchNeighbourhood R t i ⟶ fourPointGlued R t :=
  @Scheme.commonOpenChart (ULift.{u} FourPointBranch) (fourPointComplement R t)
    (fun j => branchNeighbourhood R t j.down)
    (fun j => fourPointToBranch R t j.down)
    (fun j => fourPointToBranch_isOpenImmersion R t j.down) (ULift.up i)

instance fourPointGluedChart_isOpenImmersion (i : FourPointBranch) :
    IsOpenImmersion (fourPointGluedChart R t i) :=
  Scheme.commonOpenChart_isOpenImmersion (fourPointComplement R t)
    (fun j : ULift.{u} FourPointBranch => branchNeighbourhood R t j.down)
    (fun j => fourPointToBranch R t j.down)
    (fun j => fourPointToBranch_isOpenImmersion R t j.down) (ULift.up i)

/-- Maps out of the reconstructed target are determined on its four charts. -/
theorem fourPointGlued_hom_ext {Y : Scheme} {f g : fourPointGlued R t ⟶ Y}
    (h : ∀ i, fourPointGluedChart R t i ≫ f = fourPointGluedChart R t i ≫ g) :
    f = g := by
  apply Scheme.commonOpenChart_hom_ext (fourPointComplement R t)
    (fun i : ULift.{u} FourPointBranch => branchNeighbourhood R t i.down)
    (fun i => fourPointToBranch R t i.down)
    (fun i => fourPointToBranch_isOpenImmersion R t i.down)
  intro i
  exact h i.down

/-- The canonical morphism from the reconstructed target to the projective line. -/
def fourPointGluedToProjectiveLine : fourPointGlued R t ⟶ ProjectiveLine R :=
  Scheme.commonOpenGlueMorphism (fourPointComplement R t)
    (fun i : ULift.{u} FourPointBranch => branchNeighbourhood R t i.down)
    (fun i => fourPointToBranch R t i.down)
    (fun i => fourPointToBranch_isOpenImmersion R t i.down)
    (ProjectiveLine R) (fun i => branchInclusion R t i.down)
    (fun i j => by
      rw [fourPointToBranch_comp_inclusion, fourPointToBranch_comp_inclusion])

/-- The canonical map restricts to the given target inclusion on each chart. -/
@[reassoc (attr := simp)]
theorem fourPointGluedChart_comp_toProjectiveLine (i : FourPointBranch) :
    fourPointGluedChart R t i ≫ fourPointGluedToProjectiveLine R t =
      branchInclusion R t i :=
  Scheme.commonOpenChart_comp_glueMorphism (fourPointComplement R t)
    (fun j : ULift.{u} FourPointBranch => branchNeighbourhood R t j.down)
    (fun j => fourPointToBranch R t j.down)
    (fun j => fourPointToBranch_isOpenImmersion R t j.down)
    (ProjectiveLine R) (fun j => branchInclusion R t j.down)
    (fun i j => by
      rw [fourPointToBranch_comp_inclusion, fourPointToBranch_comp_inclusion]) (ULift.up i)

/-- The four branch neighbourhoods form an open cover of the target line. -/
@[expose]
def fourPointTargetCover (ht : IsUnit t) (ht1 : IsUnit (1 - t)) :
    (ProjectiveLine R).OpenCover where
  I₀ := FourPointBranch
  X := branchNeighbourhood R t
  f := branchInclusion R t
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro x
    have hx : x ∈ ⨆ i : FourPointBranch, branchOpen R t i := by
      rw [branchOpens_cover R t ht ht1]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, by rw [branchInclusion_range]; exact hi⟩

/-- A pairwise target intersection factors through the common complement. -/
private theorem branchPair_range (i j : FourPointBranch) (hij : i ≠ j) :
    Set.range ⇑(pullback.fst (branchInclusion R t i) (branchInclusion R t j) ≫
      branchInclusion R t i) ⊆ Set.range ⇑(fourPointInclusion R t) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  rw [fourPointInclusion_range R t]
  rw [← branchOpen_inf_of_ne R t i j hij]
  change (pullback.fst (branchInclusion R t i) (branchInclusion R t j) ≫
      branchInclusion R t i) y ∈ branchOpen R t i ∧
    (pullback.fst (branchInclusion R t i) (branchInclusion R t j) ≫
      branchInclusion R t i) y ∈ branchOpen R t j
  constructor
  · have hmem : (branchInclusion R t i)
        (pullback.fst (branchInclusion R t i) (branchInclusion R t j) y) ∈
          Set.range ⇑(branchInclusion R t i) := ⟨_, rfl⟩
    rw [branchInclusion_range] at hmem
    exact hmem
  · rw [pullback.condition]
    have hmem : (branchInclusion R t j)
        (pullback.snd (branchInclusion R t i) (branchInclusion R t j) y) ∈
          Set.range ⇑(branchInclusion R t j) := ⟨_, rfl⟩
    rw [branchInclusion_range] at hmem
    exact hmem

private def branchPairToCommon (i j : FourPointBranch) (hij : i ≠ j) :
    pullback (branchInclusion R t i) (branchInclusion R t j) ⟶
      fourPointComplement R t :=
  IsOpenImmersion.lift (fourPointInclusion R t)
    (pullback.fst (branchInclusion R t i) (branchInclusion R t j) ≫
      branchInclusion R t i) (branchPair_range R t i j hij)

private theorem branchPairToCommon_fst (i j : FourPointBranch) (hij : i ≠ j) :
    branchPairToCommon R t i j hij ≫ fourPointToBranch R t i =
      pullback.fst (branchInclusion R t i) (branchInclusion R t j) := by
  apply (cancel_mono (branchInclusion R t i)).mp
  rw [Category.assoc, fourPointToBranch_comp_inclusion]
  exact IsOpenImmersion.lift_fac _ _ _

private theorem branchPairToCommon_snd (i j : FourPointBranch) (hij : i ≠ j) :
    branchPairToCommon R t i j hij ≫ fourPointToBranch R t j =
      pullback.snd (branchInclusion R t i) (branchInclusion R t j) := by
  apply (cancel_mono (branchInclusion R t j)).mp
  rw [Category.assoc, fourPointToBranch_comp_inclusion]
  exact (IsOpenImmersion.lift_fac _ _ _).trans pullback.condition

/-- The inverse is descended from the four chart inclusions. -/
def projectiveLineToFourPointGlued (ht : IsUnit t) (ht1 : IsUnit (1 - t)) :
    ProjectiveLine R ⟶ fourPointGlued R t :=
  (fourPointTargetCover R t ht ht1).glueMorphisms
    (fourPointGluedChart R t) (by
      intro i j
      by_cases hij : i = j
      · subst j
        have : IsOpenImmersion (branchInclusion R t i) :=
          branchInclusion_isOpenImmersion R t i
        have : Mono (branchInclusion R t i) := IsOpenImmersion.mono _
        simp only [fst_eq_snd_of_mono_eq]
      · let k := branchPairToCommon R t i j hij
        calc
          pullback.fst (branchInclusion R t i) (branchInclusion R t j) ≫
              fourPointGluedChart R t i =
                (k ≫ fourPointToBranch R t i) ≫ fourPointGluedChart R t i := by
                  exact (congrArg (fun f => f ≫ fourPointGluedChart R t i)
                    (branchPairToCommon_fst R t i j hij)).symm
          _ = k ≫ (fourPointToBranch R t j ≫ fourPointGluedChart R t j) := by
            have hc := Scheme.commonOpenChart_comp (fourPointComplement R t)
              (fun m : ULift.{u} FourPointBranch => branchNeighbourhood R t m.down)
              (fun m => fourPointToBranch R t m.down)
              (fun m => fourPointToBranch_isOpenImmersion R t m.down)
              (ULift.up i) (ULift.up j)
            rw [Category.assoc]
            exact congrArg (fun f => k ≫ f) hc
          _ = pullback.snd (branchInclusion R t i) (branchInclusion R t j) ≫
                fourPointGluedChart R t j := by
                  exact congrArg (fun f => f ≫ fourPointGluedChart R t j)
                    (branchPairToCommon_snd R t i j hij))

/-- The descended inverse restricts to the glued-chart inclusion. -/
@[reassoc (attr := simp)]
theorem branchInclusion_comp_toFourPointGlued
    (ht : IsUnit t) (ht1 : IsUnit (1 - t)) (i : FourPointBranch) :
    branchInclusion R t i ≫ projectiveLineToFourPointGlued R t ht ht1 =
      fourPointGluedChart R t i :=
  (fourPointTargetCover R t ht ht1).ι_glueMorphisms _ _ i

/-- Gluing the four actual target opens recovers the projective line. -/
def fourPointGluedIso (ht : IsUnit t) (ht1 : IsUnit (1 - t)) :
    fourPointGlued R t ≅ ProjectiveLine R where
  hom := fourPointGluedToProjectiveLine R t
  inv := projectiveLineToFourPointGlued R t ht ht1
  hom_inv_id := by
    apply fourPointGlued_hom_ext R t
    intro i
    rw [← Category.assoc, fourPointGluedChart_comp_toProjectiveLine,
      branchInclusion_comp_toFourPointGlued, Category.comp_id]
  inv_hom_id := by
    apply (fourPointTargetCover R t ht ht1).hom_ext
    intro i
    change branchInclusion R t i ≫
      (projectiveLineToFourPointGlued R t ht ht1 ≫
        fourPointGluedToProjectiveLine R t) = branchInclusion R t i ≫ 𝟙 _
    calc
      branchInclusion R t i ≫
          (projectiveLineToFourPointGlued R t ht ht1 ≫
            fourPointGluedToProjectiveLine R t) =
          (branchInclusion R t i ≫ projectiveLineToFourPointGlued R t ht ht1) ≫
            fourPointGluedToProjectiveLine R t := (Category.assoc _ _ _).symm
      _ = fourPointGluedChart R t i ≫ fourPointGluedToProjectiveLine R t := by
        rw [branchInclusion_comp_toFourPointGlued R t ht ht1 i]
      _ = branchInclusion R t i := fourPointGluedChart_comp_toProjectiveLine R t i
      _ = branchInclusion R t i ≫ 𝟙 _ := by simp

/-- The coefficient structure map on the reconstructed target. -/
def fourPointGluedToSpec : fourPointGlued R t ⟶ Spec (.of R) :=
  fourPointGluedToProjectiveLine R t ≫ toSpec R

/-- On each chart, the coefficient map is the original target coefficient map. -/
@[reassoc (attr := simp)]
theorem fourPointGluedChart_comp_toSpec (i : FourPointBranch) :
    fourPointGluedChart R t i ≫ fourPointGluedToSpec R t =
      branchInclusion R t i ≫ toSpec R := by
  change fourPointGluedChart R t i ≫
      (fourPointGluedToProjectiveLine R t ≫ toSpec R) = _
  rw [← Category.assoc, fourPointGluedChart_comp_toProjectiveLine]

/-- The reconstruction isomorphism respects the coefficient structure map. -/
@[reassoc (attr := simp)]
theorem fourPointGluedIso_hom_comp_toSpec (ht : IsUnit t) (ht1 : IsUnit (1 - t)) :
    (fourPointGluedIso R t ht ht1).hom ≫ toSpec R = fourPointGluedToSpec R t := by
  rfl

end AlgebraicGeometry.ProjectiveLine
