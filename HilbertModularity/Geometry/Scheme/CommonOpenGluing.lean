/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-! # Gluing schemes along one common open subscheme

A family of schemes containing the same open subscheme glues by taking that
subscheme as each off-diagonal overlap. The construction retains the actual
categorical intersections and the universal property for maps out.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u
variable {I : Type u}

/-- The diagonal overlap is the whole chart; every off-diagonal overlap is `C`. -/
def commonOpenOverlap (C : Scheme) (X : I → Scheme) (i j : I) : Scheme := by
  classical
  exact if i = j then X i else C

/-- The inclusion of the `i,j` overlap into its first chart. -/
def commonOpenOverlapInclusion (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (i j : I) : commonOpenOverlap C X i j ⟶ X i := by
  by_cases h : i = j
  · simp only [commonOpenOverlap, h, ↓reduceIte]
    exact 𝟙 _
  · simpa only [commonOpenOverlap, h, ↓reduceIte] using e i

/-- The symmetry of the common overlap, with identity transition on `C`. -/
def commonOpenTransition (C : Scheme) (X : I → Scheme) (i j : I) :
    commonOpenOverlap C X i j ⟶ commonOpenOverlap C X j i := by
  by_cases h : i = j
  · subst j
    simp only [commonOpenOverlap, ↓reduceIte]
    exact 𝟙 (X i)
  · simp only [commonOpenOverlap, h, Ne.symm h, ↓reduceIte]
    exact 𝟙 C

/-- The off-diagonal gluing data. Using `GlueData'` lets Mathlib supply all cases in
which two of the three chart indices coincide. -/
def commonOpenGlueDataAux (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i)) :
    CategoryTheory.GlueData' Scheme := by
  letI (i : I) : IsOpenImmersion (e i) := he i
  refine {
    J := I
    U := X
    V := fun _ _ _ => C
    f := fun i _ _ => e i
    t := fun _ _ _ => 𝟙 C
    t' := fun i j k _ _ _ =>
      pullback.lift (pullback.fst (e i) (e i)) (pullback.fst (e i) (e i))
        (by simp)
    t_fac := ?_
    t_inv := ?_
    cocycle := ?_ }
  · intro i j k hij hik hjk
    exact pullback.lift_snd _ _ _
  · intro i j hij
    simp
  · intro i j k hij hik hjk
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_snd,
        fst_eq_snd_of_mono_eq, Category.id_comp]

/-- Glue data for schemes sharing one open subscheme. -/
def commonOpenGlueData (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i)) :
    Scheme.GlueData := by
  letI (i : I) : IsOpenImmersion (e i) := he i
  refine {
    toGlueData := CategoryTheory.GlueData.ofGlueData'
      (commonOpenGlueDataAux C X e he)
    f_open := ?_ }
  intro i j
  classical
  change IsOpenImmersion ((commonOpenGlueDataAux C X e he).f' i j)
  dsimp [CategoryTheory.GlueData'.f']
  split_ifs with h
  · exact IsOpenImmersion.of_isIso (g := _)
  · dsimp [commonOpenGlueDataAux]
    have h_eq : (if h : i = j then X i else C) = C := dite_eq_right h
    have h_open : IsOpenImmersion (eqToHom h_eq) :=
      IsOpenImmersion.of_isIso (g := _)
    change IsOpenImmersion (eqToHom h_eq ≫ e i)
    exact @IsOpenImmersion.comp _ _ _ _ _ h_open (he i)

/-- The scheme obtained by gluing a family of charts along one common open subscheme. -/
def commonOpenGlued (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i)) : Scheme :=
  (commonOpenGlueData C X e he).glued

/-- The open chart inclusion in the common-open gluing. -/
def commonOpenChart (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i)) (i : I) :
    X i ⟶ commonOpenGlued C X e he :=
  (commonOpenGlueData C X e he).ι i

instance commonOpenChart_isOpenImmersion (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i)) (i : I) :
    IsOpenImmersion (commonOpenChart C X e he i) :=
  (commonOpenGlueData C X e he).ι_isOpenImmersion i

/-- The chart maps cover the glued scheme. -/
theorem commonOpenChart_jointly_surjective (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (x : (commonOpenGlued C X e he).carrier) :
    ∃ (i : I) (y : (X i).carrier), commonOpenChart C X e he i y = x :=
  (commonOpenGlueData C X e he).ι_jointly_surjective x

/-- The actual common subscheme has the same image in all glued charts. -/
theorem commonOpenChart_comp (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (i j : I) :
    e i ≫ commonOpenChart C X e he i = e j ≫ commonOpenChart C X e he j := by
  classical
  by_cases h : i = j
  · subst j; rfl
  · have hglue := (commonOpenGlueData C X e he).glue_condition i j
    have h_eq : (if h : i = j then X i else C) = C := dite_eq_right h
    have hglue' := congrArg (fun f => eqToHom h_eq.symm ≫ f) hglue
    simpa [commonOpenChart, commonOpenGlued, commonOpenGlueData, commonOpenGlueDataAux,
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      h, Ne.symm h] using hglue'.symm

/-- The common subscheme is the actual pairwise intersection of distinct charts. -/
def commonOpenIntersectionIsLimit (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (i j : I) (h : i ≠ j) :
    IsLimit (PullbackCone.mk (e i) (e j) (commonOpenChart_comp C X e he i j)) := by
  classical
  have hlim := (commonOpenGlueData C X e he).vPullbackConeIsLimit i j
  have h_eq : (if h : i = j then X i else C) = C := dite_eq_right h
  refine IsLimit.ofIsoLimit hlim (PullbackCone.ext (eqToIso h_eq) ?_ ?_)
  · simp [Scheme.GlueData.vPullbackCone, commonOpenGlueData,
      commonOpenGlueDataAux, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', h, Ne.symm h]
    congr 1
  · simp [Scheme.GlueData.vPullbackCone, commonOpenGlueData,
      commonOpenGlueDataAux, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', h, Ne.symm h]
    congr 1

/-- A chart intersects itself in the whole chart. -/
def commonOpenDiagonalIsLimit (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i)) (i : I) :
    IsLimit ((commonOpenGlueData C X e he).vPullbackCone i i) :=
  (commonOpenGlueData C X e he).vPullbackConeIsLimit i i

/-- A chart is its own categorical intersection in the glued scheme. -/
def commonOpenSelfIntersectionIsLimit (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i)) (i : I) :
    IsLimit (PullbackCone.mk (𝟙 (X i)) (𝟙 (X i))
      (rfl : (𝟙 (X i)) ≫ commonOpenChart C X e he i =
        (𝟙 (X i)) ≫ commonOpenChart C X e he i)) := by
  letI : Mono (commonOpenChart C X e he i) := IsOpenImmersion.mono _
  exact PullbackCone.isLimitMkIdId (commonOpenChart C X e he i)

/-- The chart inclusions as a scheme open cover. -/
def commonOpenCover (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i)) :
    (commonOpenGlued C X e he).OpenCover :=
  (commonOpenGlueData C X e he).openCover

/-- Compatible maps from the charts glue to a map from the common-open scheme. -/
def commonOpenGlueMorphism (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (Y : Scheme) (f : (i : I) → X i ⟶ Y)
    (hf : ∀ i j, e i ≫ f i = e j ≫ f j) : commonOpenGlued C X e he ⟶ Y := by
  classical
  exact (commonOpenCover C X e he).glueMorphisms f (by
    intro i j
    by_cases h : i = j
    · subst j
      let : HasPullback (commonOpenChart C X e he i)
          (commonOpenChart C X e he i) :=
        HasLimit.mk ⟨(commonOpenGlueData C X e he).vPullbackCone i i,
          (commonOpenGlueData C X e he).vPullbackConeIsLimit i i⟩
      have : IsOpenImmersion (commonOpenChart C X e he i) :=
        commonOpenChart_isOpenImmersion C X e he i
      have : Mono (commonOpenChart C X e he i) := IsOpenImmersion.mono _
      simp only [fst_eq_snd_of_mono_eq]
    · let : HasPullback (commonOpenChart C X e he i)
          (commonOpenChart C X e he j) :=
        HasLimit.mk ⟨(commonOpenGlueData C X e he).vPullbackCone i j,
          (commonOpenGlueData C X e he).vPullbackConeIsLimit i j⟩
      let P := commonOpenIntersectionIsLimit C X e he i j h
      let Q := pullback.isLimit (commonOpenChart C X e he i)
        (commonOpenChart C X e he j)
      let k : C ⟶ pullback (commonOpenChart C X e he i)
          (commonOpenChart C X e he j) := (P.conePointUniqueUpToIso Q).hom
      have hk₁ : k ≫ pullback.fst (commonOpenChart C X e he i)
          (commonOpenChart C X e he j) = e i := by
        change (P.conePointUniqueUpToIso Q).hom ≫
            (pullback.cone (commonOpenChart C X e he i)
              (commonOpenChart C X e he j)).π.app WalkingCospan.left =
          (PullbackCone.mk (e i) (e j)
            (commonOpenChart_comp C X e he i j)).π.app WalkingCospan.left
        exact P.conePointUniqueUpToIso_hom_comp Q WalkingCospan.left
      have hk₂ : k ≫ pullback.snd (commonOpenChart C X e he i)
          (commonOpenChart C X e he j) = e j := by
        change (P.conePointUniqueUpToIso Q).hom ≫
            (pullback.cone (commonOpenChart C X e he i)
              (commonOpenChart C X e he j)).π.app WalkingCospan.right =
          (PullbackCone.mk (e i) (e j)
            (commonOpenChart_comp C X e he i j)).π.app WalkingCospan.right
        exact P.conePointUniqueUpToIso_hom_comp Q WalkingCospan.right
      have : IsIso k := (P.conePointUniqueUpToIso Q).isIso_hom
      apply (cancel_epi k).mp
      change k ≫ pullback.fst (commonOpenChart C X e he i)
          (commonOpenChart C X e he j) ≫ f i =
        k ≫ pullback.snd (commonOpenChart C X e he i)
          (commonOpenChart C X e he j) ≫ f j
      simpa only [← Category.assoc, hk₁, hk₂] using hf i j)

/-- The glued map restricts to the prescribed map on every chart. -/
theorem commonOpenChart_comp_glueMorphism (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (Y : Scheme) (f : (i : I) → X i ⟶ Y)
    (hf : ∀ i j, e i ≫ f i = e j ≫ f j) (i : I) :
    commonOpenChart C X e he i ≫ commonOpenGlueMorphism C X e he Y f hf = f i := by
  unfold commonOpenGlueMorphism
  exact (commonOpenCover C X e he).ι_glueMorphisms f _ i

/-- Maps from the glued scheme are determined by their chart restrictions. -/
theorem commonOpenChart_hom_ext (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    {Y : Scheme} {f g : commonOpenGlued C X e he ⟶ Y}
    (h : ∀ i, commonOpenChart C X e he i ≫ f =
      commonOpenChart C X e he i ≫ g) : f = g :=
  (commonOpenCover C X e he).hom_ext f g h

/-- The compatible chart restrictions characterize the glued morphism. -/
theorem commonOpenGlueMorphism_unique (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (Y : Scheme) (f : (i : I) → X i ⟶ Y)
    (hf : ∀ i j, e i ≫ f i = e j ≫ f j)
    (g : commonOpenGlued C X e he ⟶ Y)
    (hg : ∀ i, commonOpenChart C X e he i ≫ g = f i) :
    g = commonOpenGlueMorphism C X e he Y f hf := by
  apply commonOpenChart_hom_ext C X e he
  intro i
  rw [hg i, commonOpenChart_comp_glueMorphism]

/-- Chart automorphisms with one common action on the open subscheme. -/
structure CommonOpenAutomorphismData (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) where
  chart : (i : I) → X i ≅ X i
  common : C ≅ C
  compatible : ∀ i, e i ≫ (chart i).hom = common.hom ≫ e i

namespace CommonOpenAutomorphismData

/-- Identity chart and common-open actions. -/
def refl (C : Scheme) (X : I → Scheme) (e : (i : I) → C ⟶ X i) :
    CommonOpenAutomorphismData C X e where
  chart := fun i => Iso.refl (X i)
  common := Iso.refl C
  compatible := by simp

/-- Consecutive compatible actions on every chart and on the common open. -/
def comp {C : Scheme} {X : I → Scheme} {e : (i : I) → C ⟶ X i}
    (a b : CommonOpenAutomorphismData C X e) :
    CommonOpenAutomorphismData C X e where
  chart := fun i => (a.chart i).trans (b.chart i)
  common := a.common.trans b.common
  compatible := by
    intro i
    simp only [Iso.trans_hom]
    calc
      e i ≫ (a.chart i).hom ≫ (b.chart i).hom =
          a.common.hom ≫ e i ≫ (b.chart i).hom := by rw [← Category.assoc, a.compatible i, Category.assoc]
      _ = a.common.hom ≫ b.common.hom ≫ e i := by rw [b.compatible i]

/-- Compatibility of the inverse action follows from compatibility of the forward action. -/
theorem inverse_compatible {C : Scheme} {X : I → Scheme}
    {e : (i : I) → C ⟶ X i} (a : CommonOpenAutomorphismData C X e) (i : I) :
    e i ≫ (a.chart i).inv = a.common.inv ≫ e i := by
  have h := congrArg (fun q => a.common.inv ≫ q ≫ (a.chart i).inv) (a.compatible i)
  simpa [Category.assoc] using h.symm

/-- The inverse action on the charts and their common open. -/
def symm {C : Scheme} {X : I → Scheme} {e : (i : I) → C ⟶ X i}
    (a : CommonOpenAutomorphismData C X e) :
    CommonOpenAutomorphismData C X e where
  chart := fun i => (a.chart i).symm
  common := a.common.symm
  compatible := a.inverse_compatible

end CommonOpenAutomorphismData

/-- The map of the glued scheme induced by a compatible action on its charts. -/
def commonOpenAutomorphismHom (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (a : CommonOpenAutomorphismData C X e) :
    commonOpenGlued C X e he ⟶ commonOpenGlued C X e he :=
  commonOpenGlueMorphism C X e he _
    (fun i => (a.chart i).hom ≫ commonOpenChart C X e he i) (by
      intro i j
      calc
        e i ≫ ((a.chart i).hom ≫ commonOpenChart C X e he i) =
            a.common.hom ≫ (e i ≫ commonOpenChart C X e he i) := by
          rw [← Category.assoc, a.compatible i, Category.assoc]
        _ = a.common.hom ≫ (e j ≫ commonOpenChart C X e he j) := by
          rw [commonOpenChart_comp]
        _ = e j ≫ ((a.chart j).hom ≫ commonOpenChart C X e he j) := by
          symm
          rw [← Category.assoc, a.compatible j, Category.assoc])

/-- The induced map restricts to the given automorphism on each chart. -/
theorem commonOpenChart_comp_automorphismHom (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (a : CommonOpenAutomorphismData C X e) (i : I) :
    commonOpenChart C X e he i ≫ commonOpenAutomorphismHom C X e he a =
      (a.chart i).hom ≫ commonOpenChart C X e he i :=
  commonOpenChart_comp_glueMorphism C X e he _ _ _ i

/-- Compatible chart automorphisms induce an automorphism of the glued scheme. -/
def commonOpenAutomorphism (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (a : CommonOpenAutomorphismData C X e) :
    commonOpenGlued C X e he ≅ commonOpenGlued C X e he where
  hom := commonOpenAutomorphismHom C X e he a
  inv := commonOpenAutomorphismHom C X e he a.symm
  hom_inv_id := by
    apply commonOpenChart_hom_ext C X e he
    intro i
    rw [← Category.assoc, commonOpenChart_comp_automorphismHom, Category.assoc,
      commonOpenChart_comp_automorphismHom]
    simp [CommonOpenAutomorphismData.symm, ← Category.assoc]
  inv_hom_id := by
    apply commonOpenChart_hom_ext C X e he
    intro i
    rw [← Category.assoc, commonOpenChart_comp_automorphismHom, Category.assoc,
      commonOpenChart_comp_automorphismHom]
    simp [CommonOpenAutomorphismData.symm, ← Category.assoc]

/-- The induced automorphism has the prescribed restriction on every chart. -/
theorem commonOpenChart_comp_automorphism (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (a : CommonOpenAutomorphismData C X e) (i : I) :
    commonOpenChart C X e he i ≫ (commonOpenAutomorphism C X e he a).hom =
      (a.chart i).hom ≫ commonOpenChart C X e he i :=
  commonOpenChart_comp_automorphismHom C X e he a i

/-- The identity chart action induces the identity automorphism. -/
theorem commonOpenAutomorphism_refl (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i)) :
    commonOpenAutomorphism C X e he (CommonOpenAutomorphismData.refl C X e) =
      Iso.refl (commonOpenGlued C X e he) := by
  apply Iso.ext
  apply commonOpenChart_hom_ext C X e he
  intro i
  rw [commonOpenChart_comp_automorphism]
  simp [CommonOpenAutomorphismData.refl]

/-- Composition of compatible chart actions agrees with composition after gluing. -/
theorem commonOpenAutomorphism_comp (C : Scheme) (X : I → Scheme)
    (e : (i : I) → C ⟶ X i) (he : ∀ i, IsOpenImmersion (e i))
    (a b : CommonOpenAutomorphismData C X e) :
    commonOpenAutomorphism C X e he (a.comp b) =
      (commonOpenAutomorphism C X e he a).trans
        (commonOpenAutomorphism C X e he b) := by
  apply Iso.ext
  apply commonOpenChart_hom_ext C X e he
  intro i
  rw [commonOpenChart_comp_automorphism, Iso.trans_hom, ← Category.assoc,
    commonOpenChart_comp_automorphism]
  simp only [CommonOpenAutomorphismData.comp, Iso.trans_hom, Category.assoc]
  rw [commonOpenChart_comp_automorphism]

end AlgebraicGeometry.Scheme
