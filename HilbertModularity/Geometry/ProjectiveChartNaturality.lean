/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveChart
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Graded naturality of affine projective charts -/

@[expose] public noncomputable section
open CategoryTheory HomogeneousLocalization
namespace AlgebraicGeometry.Proj
universe u
variable {A B C σ τ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (φ : B →+* C) (f : 𝒜 →+*ᵍ ℬ)

/-- Evaluation of homogeneous fractions commutes with a graded substitution. -/
theorem homogeneousEvaluation_comp_graded (r : A) (hu : IsUnit (φ (f r))) :
    (homogeneousEvaluation ℬ φ (f r) hu).comp (HomogeneousLocalization.Away.map f r) =
      homogeneousEvaluation 𝒜 (φ.comp f.toRingHom) r hu := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  have h₁ := homogeneousEvaluation_mk_spec ℬ φ (f r) hu
    ⟨c.deg, ⟨f c.num, f.map_mem c.num.property⟩,
      ⟨f c.den, f.map_mem c.den.property⟩, by
        obtain ⟨n, hn⟩ := c.den_mem
        exact ⟨n, by simp [← hn]⟩⟩
  have h₂ := homogeneousEvaluation_mk_spec 𝒜 (φ.comp f.toRingHom) r hu c
  have hden : IsUnit (φ (f c.den)) := by
    obtain ⟨n, hn⟩ := c.den_mem
    rw [← hn, map_pow, map_pow]
    exact hu.pow n
  apply hden.mul_right_cancel
  exact h₁.trans h₂.symm

/-- An affine morphism into a projective chart commutes with graded coordinate changes. -/
@[reassoc]
theorem fromSpecOfUnit_comp_map
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) (hu : IsUnit (φ (f r))) :
    fromSpecOfUnit ℬ φ hn (f.map_mem hr) hu ≫ map f hf =
      fromSpecOfUnit 𝒜 (φ.comp f.toRingHom) hn hr hu := by
  unfold fromSpecOfUnit
  rw [Category.assoc]
  erw [awayι_comp_map f hf hn r hr]
  rw [← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  exact homogeneousEvaluation_comp_graded 𝒜 ℬ φ f r hu

end AlgebraicGeometry.Proj
