/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Scheme.CommonOpenGluing

/-! # Morphisms of common-open gluings

Compatible maps between families of schemes glued along common open subschemes
induce a map of their gluings. Under Cartesian local squares, its restriction to
each target chart has exactly the corresponding source chart as its pullback.

The construction is used for the local-to-global geometry of the Euler cover
in [TripathiGoswamiRevised].
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u
variable {I : Type u}

/-- The morphism induced by maps of charts that agree on a map of their common opens. -/
def commonOpenMorphism (C D : Scheme) (X Y : I → Scheme)
    (e : (i : I) → C ⟶ X i) (d : (i : I) → D ⟶ Y i)
    (he : ∀ i, IsOpenImmersion (e i)) (hd : ∀ i, IsOpenImmersion (d i))
    (c : C ⟶ D) (f : (i : I) → X i ⟶ Y i)
    (hf : ∀ i, e i ≫ f i = c ≫ d i) :
    commonOpenGlued C X e he ⟶ commonOpenGlued D Y d hd :=
  commonOpenGlueMorphism C X e he _
    (fun i => f i ≫ commonOpenChart D Y d hd i) (by
      intro i j
      calc
        e i ≫ (f i ≫ commonOpenChart D Y d hd i) =
            c ≫ (d i ≫ commonOpenChart D Y d hd i) := by
              simp only [← Category.assoc, hf i]
        _ = c ≫ (d j ≫ commonOpenChart D Y d hd j) := by
              rw [commonOpenChart_comp]
        _ = e j ≫ (f j ≫ commonOpenChart D Y d hd j) := by
              simp only [← Category.assoc, hf j])

/-- The glued morphism restricts to the prescribed morphism on each chart. -/
theorem commonOpenChart_comp_commonOpenMorphism (C D : Scheme) (X Y : I → Scheme)
    (e : (i : I) → C ⟶ X i) (d : (i : I) → D ⟶ Y i)
    (he : ∀ i, IsOpenImmersion (e i)) (hd : ∀ i, IsOpenImmersion (d i))
    (c : C ⟶ D) (f : (i : I) → X i ⟶ Y i)
    (hf : ∀ i, e i ≫ f i = c ≫ d i) (i : I) :
    commonOpenChart C X e he i ≫ commonOpenMorphism C D X Y e d he hd c f hf =
      f i ≫ commonOpenChart D Y d hd i :=
  commonOpenChart_comp_glueMorphism C X e he _ _ _ i

/-- A compatible morphism of gluings is uniquely determined by its chart maps. -/
theorem commonOpenMorphism_unique (C D : Scheme) (X Y : I → Scheme)
    (e : (i : I) → C ⟶ X i) (d : (i : I) → D ⟶ Y i)
    (he : ∀ i, IsOpenImmersion (e i)) (hd : ∀ i, IsOpenImmersion (d i))
    (c : C ⟶ D) (f : (i : I) → X i ⟶ Y i)
    (hf : ∀ i, e i ≫ f i = c ≫ d i)
    (g : commonOpenGlued C X e he ⟶ commonOpenGlued D Y d hd)
    (hg : ∀ i, commonOpenChart C X e he i ≫ g =
      f i ≫ commonOpenChart D Y d hd i) :
    g = commonOpenMorphism C D X Y e d he hd c f hf := by
  apply commonOpenChart_hom_ext C X e he
  intro i
  rw [hg i, commonOpenChart_comp_commonOpenMorphism]

private theorem pullback_openRange {C D X Y : Scheme}
    (e : C ⟶ X) (d : D ⟶ Y) (c : C ⟶ D) (f : X ⟶ Y)
    [IsOpenImmersion e] [IsOpenImmersion d]
    (h : IsPullback c e d f) : f ⁻¹ᵁ d.opensRange = e.opensRange := by
  simpa [Scheme.Hom.image_top_eq_opensRange] using
    (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h (⊤ : D.Opens)).symm

/-- On a different chart, the target chart pulls back to the common open. -/
theorem commonOpenChart_preimage_other (D : Scheme) (Y : I → Scheme)
    (d : (i : I) → D ⟶ Y i) (hd : ∀ i, IsOpenImmersion (d i))
    (i j : I) (hij : i ≠ j) :
    commonOpenChart D Y d hd j ⁻¹ᵁ (commonOpenChart D Y d hd i).opensRange =
      (d j).opensRange := by
  exact pullback_openRange (d j) (commonOpenChart D Y d hd i) (d i)
    (commonOpenChart D Y d hd j)
    (IsPullback.of_isLimit (commonOpenIntersectionIsLimit D Y d hd i j hij))

/-- The inverse image of a glued target chart is precisely the matching source chart. -/
theorem commonOpenMorphism_preimage_chart (C D : Scheme) (X Y : I → Scheme)
    (e : (i : I) → C ⟶ X i) (d : (i : I) → D ⟶ Y i)
    (he : ∀ i, IsOpenImmersion (e i)) (hd : ∀ i, IsOpenImmersion (d i))
    (c : C ⟶ D) (f : (i : I) → X i ⟶ Y i)
    (hf : ∀ i, e i ≫ f i = c ≫ d i)
    (hsq : ∀ i, IsPullback c (e i) (d i) (f i)) (i : I) :
    commonOpenMorphism C D X Y e d he hd c f hf ⁻¹ᵁ
        (commonOpenChart D Y d hd i).opensRange =
      (commonOpenChart C X e he i).opensRange := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, q, rfl⟩ := commonOpenChart_jointly_surjective C X e he p
    have hq : (f j q) ∈
        commonOpenChart D Y d hd j ⁻¹ᵁ
          (commonOpenChart D Y d hd i).opensRange := by
      change (commonOpenChart C X e he j ≫
          commonOpenMorphism C D X Y e d he hd c f hf) q ∈
        (commonOpenChart D Y d hd i).opensRange at hp
      rw [commonOpenChart_comp_commonOpenMorphism] at hp
      exact hp
    by_cases hji : j = i
    · subst j
      exact ⟨q, rfl⟩
    · have hq' : q ∈ (e j).opensRange := by
        have hqD : f j q ∈ (d j).opensRange := by
          rw [← commonOpenChart_preimage_other D Y d hd i j (Ne.symm hji)]
          exact hq
        have hpre := pullback_openRange (e j) (d j) c (f j) (hsq j)
        rw [← hpre]
        exact hqD
      obtain ⟨z, rfl⟩ := hq'
      refine ⟨e i z, ?_⟩
      exact congrArg (fun h => h z) (commonOpenChart_comp C X e he j i).symm
  · rintro ⟨q, rfl⟩
    change (commonOpenChart C X e he i ≫
      commonOpenMorphism C D X Y e d he hd c f hf) q ∈
      (commonOpenChart D Y d hd i).opensRange
    rw [commonOpenChart_comp_commonOpenMorphism]
    exact ⟨f i q, rfl⟩

/-- Every chart square of a common-open morphism is Cartesian. -/
theorem commonOpenMorphism_isPullback_chart (C D : Scheme) (X Y : I → Scheme)
    (e : (i : I) → C ⟶ X i) (d : (i : I) → D ⟶ Y i)
    (he : ∀ i, IsOpenImmersion (e i)) (hd : ∀ i, IsOpenImmersion (d i))
    (c : C ⟶ D) (f : (i : I) → X i ⟶ Y i)
    (hf : ∀ i, e i ≫ f i = c ≫ d i)
    (hsq : ∀ i, IsPullback c (e i) (d i) (f i)) (i : I) :
    IsPullback (f i) (commonOpenChart C X e he i)
      (commonOpenChart D Y d hd i)
      (commonOpenMorphism C D X Y e d he hd c f hf) := by
  apply IsOpenImmersion.isPullback
  · exact commonOpenChart_comp_commonOpenMorphism C D X Y e d he hd c f hf i
  · exact commonOpenMorphism_preimage_chart C D X Y e d he hd c f hf hsq i
end AlgebraicGeometry.Scheme
