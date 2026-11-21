/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Naturality of projective morphisms defined by global sections

Homogeneous global sections commute with a graded change of coordinates.
This connects concrete projective coordinate substitutions to scheme-valued points.
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  {X : Scheme.{u}} (φ : B →+* Γ(X, ⊤))

/-- On its distinguished basic open, the morphism defined by global sections is the
specified homogeneous chart morphism. -/
@[reassoc]
theorem basicOpen_ι_fromOfGlobalSections
    (hφ : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map φ = ⊤)
    {r : B} {n : ℕ} (hn : 0 < n) (hr : r ∈ ℬ n) :
    (X.basicOpen (φ r)).ι ≫ fromOfGlobalSections ℬ φ hφ =
      toBasicOpenOfGlobalSections ℬ φ rfl hn hr ≫ (basicOpen ℬ r).ι := by
  have h := congrArg (fun f => f ≫ (basicOpen ℬ r).ι)
    (fromOfGlobalSections_resLE ℬ φ hφ hn hr)
  simpa only [Scheme.Hom.resLE_comp_ι] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A graded change of homogeneous coordinates commutes with the corresponding chart map. -/
@[reassoc]
theorem toBasicOpenOfGlobalSections_comp_map
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    toBasicOpenOfGlobalSections ℬ φ rfl hn (f.map_mem hr) ≫
        (basicOpen ℬ (f r)).ι ≫ map f hf =
      toBasicOpenOfGlobalSections 𝒜 (φ.comp f.toRingHom) rfl hn hr ≫ (basicOpen 𝒜 r).ι := by
  simp only [toBasicOpenOfGlobalSections, Category.assoc, basicOpenIsoSpec_inv_ι]
  erw [basicOpenIsoSpec_inv_ι_assoc ℬ (f r) (f.map_mem hr) hn]
  erw [awayι_comp_map f hf hn r hr]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  simp [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk, Localization.mk_eq_mk', IsLocalization.map_mk']

/-- A graded change of coordinates commutes with the actual projective morphism
constructed from homogeneous global sections. -/
@[reassoc]
theorem fromOfGlobalSections_comp_map
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hφ : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map φ = ⊤)
    (hφf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (φ.comp f.toRingHom) = ⊤) :
    fromOfGlobalSections ℬ φ hφ ≫ map f hf =
      fromOfGlobalSections 𝒜 (φ.comp f.toRingHom) hφf := by
  apply (openCoverOfMapIrrelevantEqTop 𝒜 (φ.comp f.toRingHom) hφf).hom_ext
  rintro ⟨n, r, hn, hr⟩
  change (X.basicOpen (φ (f r))).ι ≫ (fromOfGlobalSections ℬ φ hφ ≫ map f hf) =
    (X.basicOpen (φ (f r))).ι ≫ fromOfGlobalSections 𝒜 (φ.comp f.toRingHom) hφf
  erw [← Category.assoc, basicOpen_ι_fromOfGlobalSections ℬ φ hφ hn (f.map_mem hr),
    Category.assoc, toBasicOpenOfGlobalSections_comp_map 𝒜 ℬ φ f hf hn hr,
    basicOpen_ι_fromOfGlobalSections 𝒜 (φ.comp f.toRingHom) hφf hn hr]

end AlgebraicGeometry.Proj
