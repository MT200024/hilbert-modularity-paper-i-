/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.GaloisAction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Reconstructing a compact natural action from its point orbits

Finite products combine finitely many point constraints. Compactness then gives
one group element realizing a natural automorphism on every finite fibre.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.PreGaloisCategory
namespace CategoryTheory.PreGaloisCategory
universe u v w
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  (F : C ⥤ FintypeCat.{w}) [PreservesFiniteProducts F]
  (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)] [IsNaturalSMul F G]

/-- Orbitwise realization of a natural automorphism can be simultaneous on a finite
family of chosen fibre points. -/
theorem exists_smul_eq_finite_family_of_orbits (α : Aut F)
    (h : ∀ (X : C) (x : F.obj X), ∃ g : G, g • x = α.hom.app X x)
    {ι : Type*} [Finite ι] (X : ι → C) (x : ∀ i, F.obj (X i)) :
    ∃ g : G, ∀ i, g • x i = α.hom.app (X i) (x i) := by
  let P : C := ∏ᶜ X
  let e₁ : F.obj P ≅ ∏ᶜ fun i => F.obj (X i) := PreservesProduct.iso F X
  let e₂ : (∏ᶜ fun i => F.obj (X i) : FintypeCat) ≃ ∀ i, F.obj (X i) :=
    FintypeCat.productEquiv (fun i => F.obj (X i))
  let px : F.obj P := e₁.inv (e₂.symm x)
  have hp (i : ι) : F.map (Pi.π X i) px = x i := by
    simp only [px, e₁, e₂, ← piComparison_comp_π, ← PreservesProduct.iso_hom,
      FintypeCat.comp_apply]
    rw [FintypeCat.inv_hom_id_apply, FintypeCat.productEquiv_symm_comp_π_apply]
  obtain ⟨g, hg⟩ := h P px
  refine ⟨g, fun i => ?_⟩
  rw [← hp i, ← IsNaturalSMul.naturality, hg, FunctorToFintypeCat.naturality]

/-- A continuous compact natural action realizes a fibre automorphism if it can
realize that automorphism separately at each point. -/
theorem exists_toAut_eq_of_orbits [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ X, ContinuousSMul G (F.obj X)] (α : Aut F)
    (h : ∀ (X : C) (x : F.obj X), ∃ g : G, g • x = α.hom.app X x) :
    ∃ g : G, toAut F G g = α := by
  let cl (p : Σ X : C, F.obj X) : Set G := {g | g • p.2 = α.hom.app p.1 p.2}
  have hne : (⋂ p, cl p).Nonempty := by
    rw [← Set.univ_inter (⋂ p, cl p)]
    apply CompactSpace.isCompact_univ.inter_iInter_nonempty
    · intro p
      exact isClosed_eq (continuous_id.smul continuous_const) continuous_const
    · intro s
      rw [Set.univ_inter]
      obtain ⟨g, hg⟩ := exists_smul_eq_finite_family_of_orbits F G α h
        (fun p : s => p.val.1) (fun p : s => p.val.2)
      refine ⟨g, ?_⟩
      simp only [Set.mem_iInter]
      intro p hp
      exact hg ⟨p, hp⟩
  obtain ⟨g, hg⟩ := hne
  refine ⟨g, ?_⟩
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply FintypeCat.hom_ext
  intro x
  exact Set.mem_iInter.mp hg ⟨X, x⟩

end CategoryTheory.PreGaloisCategory
