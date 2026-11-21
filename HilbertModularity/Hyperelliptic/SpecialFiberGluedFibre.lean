/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberAbsoluteFibre

/-! # The chart opens under specialization

The coefficient map preserves the affine coordinate on each quadratic chart.
Consequently its glued map pulls each family chart open back to the matching
chart open in the specialized cover.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial LaurentPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbertModularity.Hyperelliptic

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

private theorem finiteChartMap_X (f : R →+* S) (P : R[X]) (t : R) :
    finiteChartMap f P t
        (algebraMap R[X] (DoubleCover.ChartRing (finiteBranchPolynomial P t)) X) =
      algebraMap S[X] (DoubleCover.ChartRing
        (finiteBranchPolynomial (P.map f) (f t))) X := by
  apply QuadraticAlgebra.ext <;>
    simp

private theorem infinityChartMap_X (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    infinityChartMap f P t hdeg
        (algebraMap R[X] (DoubleCover.ChartRing (infinityBranchPolynomial P t)) X) =
      algebraMap S[X] (DoubleCover.ChartRing
        (infinityBranchPolynomial (P.map f) (f t))) X := by
  apply QuadraticAlgebra.ext <;>
    simp

private theorem finiteChartMap_preimage_overlap (f : R →+* S) (P : R[X]) (t : R) :
    Spec.map (CommRingCat.ofHom (finiteChartMap f P t)) ⁻¹ᵁ
        (DoubleCover.overlapInclusion (finiteBranchPolynomial P t)).opensRange =
      (DoubleCover.overlapInclusion
        (finiteBranchPolynomial (P.map f) (f t))).opensRange := by
  rw [DoubleCover.overlapInclusion_opensRange, SpecMap_preimage_basicOpen,
    DoubleCover.overlapInclusion_opensRange]
  exact congrArg PrimeSpectrum.basicOpen (finiteChartMap_X f P t)

private theorem infinityChartMap_preimage_overlap (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)) ⁻¹ᵁ
        (DoubleCover.overlapInclusion (infinityBranchPolynomial P t)).opensRange =
      (DoubleCover.overlapInclusion
        (infinityBranchPolynomial (P.map f) (f t))).opensRange := by
  rw [DoubleCover.overlapInclusion_opensRange, SpecMap_preimage_basicOpen,
    DoubleCover.overlapInclusion_opensRange]
  exact congrArg PrimeSpectrum.basicOpen (infinityChartMap_X f P t hdeg)

private theorem infinityChart_preimage_finiteChart (F G : R[X]) (n : ℕ)
    (h : invert (toLaurent G) = T (-(n : ℤ)) ^ 2 * toLaurent F) :
    DoubleCover.infinityChart F G n h ⁻¹ᵁ (DoubleCover.finiteChart F G n h).opensRange =
      (DoubleCover.overlapInclusion G).opensRange := by
  let U : (ProjectiveLine R).Opens :=
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1)
  have hU : DoubleCover.toProjectiveLine F G n h ⁻¹ᵁ U =
      (DoubleCover.finiteChart F G n h).opensRange :=
    DoubleCover.toProjectiveLine_preimage_finite F G n h
  rw [← hU, ← Scheme.Hom.comp_preimage,
    DoubleCover.infinityChart_toProjectiveLine]
  exact DoubleCover.infinityProjection_preimage_finite G

private theorem finiteChart_preimage_infinityChart (F G : R[X]) (n : ℕ)
    (h : invert (toLaurent G) = T (-(n : ℤ)) ^ 2 * toLaurent F) :
    DoubleCover.finiteChart F G n h ⁻¹ᵁ (DoubleCover.infinityChart F G n h).opensRange =
      (DoubleCover.overlapInclusion F).opensRange := by
  let U : (ProjectiveLine R).Opens :=
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0)
  have hU : DoubleCover.toProjectiveLine F G n h ⁻¹ᵁ U =
      (DoubleCover.infinityChart F G n h).opensRange :=
    DoubleCover.toProjectiveLine_preimage_infinity F G n h
  rw [← hU, ← Scheme.Hom.comp_preimage,
    DoubleCover.finiteChart_toProjectiveLine]
  exact DoubleCover.finiteProjection_preimage_infinity F

/-- Coefficient change pulls the finite chart open back to the finite chart
open. On the reciprocal chart this reduces to preservation of the Laurent
coordinate `X`. -/
theorem scaledDoubleCoverMap_preimage_finiteChart (f : R →+* S)
    (P : R[X]) (t : R) (hdeg : (P.map f).natDegree = P.natDegree) :
    scaledDoubleCoverMap f P t hdeg ⁻¹ᵁ
        (DoubleCover.finiteChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)).opensRange =
      (DoubleCover.finiteChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t))
        ((P.map f).natDegree + 1)
        (branch_transition (P.map f) (f t))).opensRange := by
  ext x
  rcases DoubleCover.charts_jointly_surjective
      (finiteBranchPolynomial (P.map f) (f t))
      (infinityBranchPolynomial (P.map f) (f t))
      ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) x with
    ⟨y, rfl⟩ | ⟨y, rfl⟩
  · constructor
    · intro _
      exact ⟨y, rfl⟩
    · intro _
      change y ∈ (DoubleCover.finiteChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t))
        ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) ≫
        scaledDoubleCoverMap f P t hdeg) ⁻¹ᵁ
        (DoubleCover.finiteChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)).opensRange
      rw [finiteChart_scaledDoubleCoverMap]
      exact ⟨_, rfl⟩
  · change y ∈ (DoubleCover.infinityChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t))
        ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) ≫
        scaledDoubleCoverMap f P t hdeg) ⁻¹ᵁ
        (DoubleCover.finiteChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)).opensRange ↔
        y ∈ DoubleCover.infinityChart
          (finiteBranchPolynomial (P.map f) (f t))
          (infinityBranchPolynomial (P.map f) (f t))
          ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) ⁻¹ᵁ
          (DoubleCover.finiteChart
            (finiteBranchPolynomial (P.map f) (f t))
            (infinityBranchPolynomial (P.map f) (f t))
            ((P.map f).natDegree + 1)
            (branch_transition (P.map f) (f t))).opensRange
    rw [infinityChart_scaledDoubleCoverMap, Scheme.Hom.comp_preimage,
      infinityChart_preimage_finiteChart,
      infinityChartMap_preimage_overlap,
      infinityChart_preimage_finiteChart]

/-- The reciprocal chart open is likewise preserved by coefficient change. -/
theorem scaledDoubleCoverMap_preimage_infinityChart (f : R →+* S)
    (P : R[X]) (t : R) (hdeg : (P.map f).natDegree = P.natDegree) :
    scaledDoubleCoverMap f P t hdeg ⁻¹ᵁ
        (DoubleCover.infinityChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)).opensRange =
      (DoubleCover.infinityChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t))
        ((P.map f).natDegree + 1)
        (branch_transition (P.map f) (f t))).opensRange := by
  ext x
  rcases DoubleCover.charts_jointly_surjective
      (finiteBranchPolynomial (P.map f) (f t))
      (infinityBranchPolynomial (P.map f) (f t))
      ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) x with
    ⟨y, rfl⟩ | ⟨y, rfl⟩
  · change y ∈ (DoubleCover.finiteChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t))
        ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) ≫
        scaledDoubleCoverMap f P t hdeg) ⁻¹ᵁ
        (DoubleCover.infinityChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)).opensRange ↔
        y ∈ DoubleCover.finiteChart
          (finiteBranchPolynomial (P.map f) (f t))
          (infinityBranchPolynomial (P.map f) (f t))
          ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) ⁻¹ᵁ
          (DoubleCover.infinityChart
            (finiteBranchPolynomial (P.map f) (f t))
            (infinityBranchPolynomial (P.map f) (f t))
            ((P.map f).natDegree + 1)
            (branch_transition (P.map f) (f t))).opensRange
    rw [finiteChart_scaledDoubleCoverMap, Scheme.Hom.comp_preimage,
      finiteChart_preimage_infinityChart,
      finiteChartMap_preimage_overlap,
      finiteChart_preimage_infinityChart]
  · constructor
    · intro _
      exact ⟨y, rfl⟩
    · intro _
      change y ∈ (DoubleCover.infinityChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t))
        ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) ≫
        scaledDoubleCoverMap f P t hdeg) ⁻¹ᵁ
        (DoubleCover.infinityChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)).opensRange
      rw [infinityChart_scaledDoubleCoverMap]
      exact ⟨_, rfl⟩

/-- The finite chart is the pullback of its open in the family cover under
coefficient change. -/
theorem finiteChart_scaledDoubleCoverMap_isPullback (f : R →+* S)
    (P : R[X]) (t : R) (hdeg : (P.map f).natDegree = P.natDegree) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (finiteChartMap f P t)))
      (DoubleCover.finiteChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t))
        ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)))
      (DoubleCover.finiteChart
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t))
      (scaledDoubleCoverMap f P t hdeg) := by
  apply IsOpenImmersion.isPullback
  · exact finiteChart_scaledDoubleCoverMap f P t hdeg
  · exact scaledDoubleCoverMap_preimage_finiteChart f P t hdeg

/-- The reciprocal chart is the pullback of its open in the family cover. -/
theorem infinityChart_scaledDoubleCoverMap_isPullback (f : R →+* S)
    (P : R[X]) (t : R) (hdeg : (P.map f).natDegree = P.natDegree) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)))
      (DoubleCover.infinityChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t))
        ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)))
      (DoubleCover.infinityChart
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t))
      (scaledDoubleCoverMap f P t hdeg) := by
  apply IsOpenImmersion.isPullback
  · exact infinityChart_scaledDoubleCoverMap f P t hdeg
  · exact scaledDoubleCoverMap_preimage_infinityChart f P t hdeg

private theorem localBasePullback_of_chart
    {C D X Y Z Z' : Scheme} (chartS : C ⟶ X) (chartR : D ⟶ Y)
    (chartMap : C ⟶ D) (global : X ⟶ Y)
    (sourceBase : X ⟶ Z) (targetBase : Y ⟶ Z') (base : Z ⟶ Z')
    (hchart : IsPullback chartMap chartS chartR global)
    (hlocal : IsPullback chartMap (chartS ≫ sourceBase)
      (chartR ≫ targetBase) base) :
    IsPullback (pullback.snd global chartR)
      (pullback.fst global chartR ≫ sourceBase)
      (chartR ≫ targetBase) base := by
  let e : C ≅ pullback global chartR :=
    hchart.isoPullback ≪≫ pullbackSymmetry chartR global
  have e_snd : e.hom ≫ pullback.snd global chartR = chartMap := by
    change (hchart.isoPullback.hom ≫ (pullbackSymmetry chartR global).hom) ≫
      pullback.snd global chartR = chartMap
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd,
      hchart.isoPullback_hom_fst]
  have e_fst : e.hom ≫ pullback.fst global chartR = chartS := by
    change (hchart.isoPullback.hom ≫ (pullbackSymmetry chartR global).hom) ≫
      pullback.fst global chartR = chartS
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst,
      hchart.isoPullback_hom_snd]
  refine hlocal.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact e_snd.symm
  · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
      congrArg (fun q => q ≫ sourceBase) e_fst.symm
  · rfl
  · rfl

variable [Algebra R S] [Nontrivial S]

local instance : Algebra R[X] S[X] :=
  (Polynomial.mapRingHom (algebraMap R S)).toAlgebra

omit [Nontrivial S] in
private theorem finiteChart_toSpec_baseChange_isPullback (P : R[X]) (t : R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (finiteChartMap (algebraMap R S) P t)))
      (DoubleCover.finiteChart
        (finiteBranchPolynomial (P.map (algebraMap R S))
          (algebraMap R S t))
        (infinityBranchPolynomial (P.map (algebraMap R S))
          (algebraMap R S t))
        ((P.map (algebraMap R S)).natDegree + 1)
        (branch_transition (P.map (algebraMap R S)) (algebraMap R S t)) ≫
        scaledDoubleCoverToSpec (P.map (algebraMap R S)) (algebraMap R S t))
      (DoubleCover.finiteChart
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) ≫
        scaledDoubleCoverToSpec P t)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [finiteChart_scaledDoubleCoverProjection_toSpec,
    finiteChart_scaledDoubleCoverProjection_toSpec,
    DoubleCover.finiteProjection_toSpec, DoubleCover.finiteProjection_toSpec]
  let e : Spec (CommRingCat.of
      (DoubleCover.ChartRing
        (finiteBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t)))) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
        (Spec.map (CommRingCat.ofHom
          (algebraMap R[X] (DoubleCover.ChartRing (finiteBranchPolynomial P t))))) :=
    Scheme.Spec.mapIso
        (finiteChartTensorEquiv (S := S) P t).toRingEquiv.toCommRingCatIso.op ≪≫
      (pullbackSpecIso R[X] S[X]
        (DoubleCover.ChartRing (finiteBranchPolynomial P t))).symm
  have h₁ : e.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (algebraMap S[X] (DoubleCover.ChartRing
          (finiteBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t))))) := by
    change Spec.map (CommRingCat.ofHom
        (finiteChartTensorEquiv (S := S) P t).toRingHom) ≫
      (pullbackSpecIso R[X] S[X]
        (DoubleCover.ChartRing (finiteBranchPolynomial P t))).inv ≫
      pullback.fst _ _ = _
    rw [pullbackSpecIso_inv_fst', ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp]
    congr 1
    apply RingHom.ext
    intro s
    exact (finiteChartTensorEquiv (S := S) P t).commutes s
  have h₂ : e.hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (finiteChartMap (algebraMap R S) P t)) := by
    change Spec.map (CommRingCat.ofHom
        (finiteChartTensorEquiv (S := S) P t).toRingHom) ≫
      (pullbackSpecIso R[X] S[X]
        (DoubleCover.ChartRing (finiteBranchPolynomial P t))).inv ≫
      pullback.snd _ _ = _
    rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp]
    congr 1
    apply RingHom.ext
    intro z
    exact finiteChartTensorEquiv_includeRight (S := S) P t z
  have h : IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap S[X] (DoubleCover.ChartRing
          (finiteBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t))))))
      (Spec.map (CommRingCat.ofHom (finiteChartMap (algebraMap R S) P t)))
      (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R[X] (DoubleCover.ChartRing (finiteBranchPolynomial P t))))) := by
    apply IsPullback.of_iso_pullback
      (show CommSq _ _ _ _ from ⟨by
        calc
          _ = (e.hom ≫ pullback.fst _ _) ≫ _ := by rw [h₁]
          _ = (e.hom ≫ pullback.snd _ _) ≫ _ := by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
          _ = _ := by rw [h₂]⟩)
      e h₁ h₂
  have hp := h.paste_horiz (polynomialSpecialization_isPullback (R := R) (S := S))
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq] using hp.flip


omit [Nontrivial S] in
private theorem infinityChart_toSpec_baseChange_isPullback (P : R[X]) (t : R)
    (hdeg : (P.map (algebraMap R S)).natDegree = P.natDegree) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (infinityChartMap (algebraMap R S) P t hdeg)))
      (DoubleCover.infinityChart
        (finiteBranchPolynomial (P.map (algebraMap R S))
          (algebraMap R S t))
        (infinityBranchPolynomial (P.map (algebraMap R S))
          (algebraMap R S t))
        ((P.map (algebraMap R S)).natDegree + 1)
        (branch_transition (P.map (algebraMap R S)) (algebraMap R S t)) ≫
        scaledDoubleCoverToSpec (P.map (algebraMap R S)) (algebraMap R S t))
      (DoubleCover.infinityChart
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) ≫
        scaledDoubleCoverToSpec P t)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [infinityChart_scaledDoubleCoverProjection_toSpec,
    infinityChart_scaledDoubleCoverProjection_toSpec,
    DoubleCover.infinityProjection_toSpec, DoubleCover.infinityProjection_toSpec]
  let e : Spec (CommRingCat.of
      (DoubleCover.ChartRing
        (infinityBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t)))) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
        (Spec.map (CommRingCat.ofHom
          (algebraMap R[X] (DoubleCover.ChartRing (infinityBranchPolynomial P t))))) :=
    Scheme.Spec.mapIso
        (infinityChartTensorEquiv (S := S) P t hdeg).toRingEquiv.toCommRingCatIso.op ≪≫
      (pullbackSpecIso R[X] S[X]
        (DoubleCover.ChartRing (infinityBranchPolynomial P t))).symm
  have h₁ : e.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (algebraMap S[X] (DoubleCover.ChartRing
          (infinityBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t))))) := by
    change Spec.map (CommRingCat.ofHom
        (infinityChartTensorEquiv (S := S) P t hdeg).toRingHom) ≫
      (pullbackSpecIso R[X] S[X]
        (DoubleCover.ChartRing (infinityBranchPolynomial P t))).inv ≫
      pullback.fst _ _ = _
    rw [pullbackSpecIso_inv_fst', ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp]
    congr 1
    apply RingHom.ext
    intro s
    exact (infinityChartTensorEquiv (S := S) P t hdeg).commutes s
  have h₂ : e.hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (infinityChartMap (algebraMap R S) P t hdeg)) := by
    change Spec.map (CommRingCat.ofHom
        (infinityChartTensorEquiv (S := S) P t hdeg).toRingHom) ≫
      (pullbackSpecIso R[X] S[X]
        (DoubleCover.ChartRing (infinityBranchPolynomial P t))).inv ≫
      pullback.snd _ _ = _
    rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp]
    congr 1
    apply RingHom.ext
    intro z
    exact infinityChartTensorEquiv_includeRight (S := S) P t hdeg z
  have h : IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap S[X] (DoubleCover.ChartRing
          (infinityBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t))))))
      (Spec.map (CommRingCat.ofHom (infinityChartMap (algebraMap R S) P t hdeg)))
      (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R[X] (DoubleCover.ChartRing (infinityBranchPolynomial P t))))) := by
    apply IsPullback.of_iso_pullback
      (show CommSq _ _ _ _ from ⟨by
        calc
          _ = (e.hom ≫ pullback.fst _ _) ≫ _ := by rw [h₁]
          _ = (e.hom ≫ pullback.snd _ _) ≫ _ := by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
          _ = _ := by rw [h₂]⟩)
      e h₁ h₂
  have hp := h.paste_horiz (polynomialSpecialization_isPullback (R := R) (S := S))
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq] using hp.flip

omit [Nontrivial S] in
/-- The entire scaled cover commutes with a degree-preserving change of
coefficients. The fibre square is checked on the two actual glued charts. -/
theorem scaledDoubleCoverMap_toSpec_isPullback (P : R[X]) (t : R)
    (hdeg : (P.map (algebraMap R S)).natDegree = P.natDegree) :
    IsPullback
      (scaledDoubleCoverMap (algebraMap R S) P t hdeg)
      (scaledDoubleCoverToSpec (P.map (algebraMap R S)) (algebraMap R S t))
      (scaledDoubleCoverToSpec P t)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply Scheme.isPullback_of_openCover _ _ _ _
    (DoubleCover.openCover (finiteBranchPolynomial P t)
      (infinityBranchPolynomial P t) (P.natDegree + 1) (branch_transition P t))
  intro i
  cases i
  · have hchart := finiteChart_scaledDoubleCoverMap_isPullback
      (algebraMap R S) P t hdeg
    have hlocal := finiteChart_toSpec_baseChange_isPullback (S := S) P t
    have h := localBasePullback_of_chart _ _ _ _ _ _ _ hchart hlocal
    simpa only [DoubleCover.openCover, Scheme.Cover.pullbackHom,
      Precoverage.ZeroHypercover.pullback₁,
      PreZeroHypercover.pullback₁] using h
  · have hchart := infinityChart_scaledDoubleCoverMap_isPullback
      (algebraMap R S) P t hdeg
    have hlocal := infinityChart_toSpec_baseChange_isPullback (S := S) P t hdeg
    have h := localBasePullback_of_chart _ _ _ _ _ _ _ hchart hlocal
    simpa only [DoubleCover.openCover, Scheme.Cover.pullbackHom,
      Precoverage.ZeroHypercover.pullback₁,
      PreZeroHypercover.pullback₁] using h

omit [Nontrivial S] in
private theorem scaledDoubleCover_toSpec_pullback_transport
    (Q : S[X]) (P : R[X]) (t : R) (q : S) (hq : q = 0)
    (m : scaledDoubleCover Q q ⟶ scaledDoubleCover P t)
    (h : IsPullback m (scaledDoubleCoverToSpec Q q)
      (scaledDoubleCoverToSpec P t)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    IsPullback (hq ▸ m) (scaledDoubleCoverToSpec Q 0)
      (scaledDoubleCoverToSpec P t)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  cases hq
  exact h

/-- When the parameter vanishes after coefficient specialization, the actual
square-branch scaled cover is the scheme-theoretic fibre of the family. Monicity
keeps the reciprocal chart's projective exponent unchanged. -/
theorem scaledDoubleCoverSpecialization_toSpec_isPullback (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) (hP : P.Monic) :
    IsPullback
      (scaledDoubleCoverSpecializationMap (algebraMap R S) P t ht hP)
      (scaledDoubleCoverToSpec (P.map (algebraMap R S)) 0)
      (scaledDoubleCoverToSpec P t)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have h := scaledDoubleCoverMap_toSpec_isPullback (S := S) P t
    (monic_natDegree_map (algebraMap R S) P hP)
  exact scaledDoubleCover_toSpec_pullback_transport
    (P.map (algebraMap R S)) P t ((algebraMap R S) t) ht
    (scaledDoubleCoverMap (algebraMap R S) P t
      (monic_natDegree_map (algebraMap R S) P hP)) h

/-- The specialization square gives a canonical identification with the
categorical fibre, retaining both projections. -/
def scaledDoubleCoverSpecializationPullbackIso (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) (hP : P.Monic) :
    scaledDoubleCover (P.map (algebraMap R S)) 0 ≅
      pullback (scaledDoubleCoverToSpec P t)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (scaledDoubleCoverSpecialization_toSpec_isPullback (S := S) P t ht hP).isoPullback

end HilbertModularity.Hyperelliptic
