/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Pro-étale sites under scheme isomorphisms

An isomorphism of schemes induces an equivalence of their actual pro-étale
sites. It preserves the covering families and the continuous-function
coefficient sheaves used in [proetale2015]. These are the site-level maps
needed for the cohomological action in [TripathiGoswamiRevised].
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.ProEt

universe u
variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- Postcomposition of weakly étale schemes with a weakly étale morphism. -/
def map (f : X ⟶ Y) [WeaklyEtale f] : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map ⊤ (show WeaklyEtale f from inferInstance)

/-- Postcomposition leaves the underlying scheme unchanged. -/
@[simp] theorem map_obj_left (f : X ⟶ Y) [WeaklyEtale f] (U : X.ProEt) :
    ((map f).obj U).left = U.left := rfl

/-- The structure map of a transported pro-étale object is its composite. -/
@[simp] theorem map_obj_hom (f : X ⟶ Y) [WeaklyEtale f] (U : X.ProEt) :
    ((map f).obj U).hom = U.hom ≫ f := rfl

/-- A scheme isomorphism identifies the actual categories of weakly étale schemes. -/
def mapEquivalence (e : X ≅ Y) : X.ProEt ≌ Y.ProEt where
  functor := map e.hom
  inverse := map e.inv
  unitIso := NatIso.ofComponents (fun U =>
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 U.left ≫ ((U.hom ≫ e.hom) ≫ e.inv) = U.hom
      simp))
  counitIso := NatIso.ofComponents (fun U =>
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 U.left ≫ U.hom = (U.hom ≫ e.inv) ≫ e.hom
      simp))
  functor_unitIso_comp U := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 U.left ≫ 𝟙 U.left = 𝟙 U.left
    simp

/-- Transport preserves the pro-étale covering families exactly. -/
theorem precoverage_comap_map (f : X ⟶ Y) [WeaklyEtale f] :
    (precoverage Y).comap (map f) = precoverage X := by
  rw [precoverage, ← Precoverage.comap_comp]
  rfl

instance precoverage_isStableUnderBaseChange (X : Scheme.{u}) :
    (precoverage X).IsStableUnderBaseChange :=
  inferInstanceAs (proetalePrecoverage.comap (ProEt.forget X ⋙ Over.forget X)).IsStableUnderBaseChange

/-- The functor induced by a scheme isomorphism is continuous for the pro-étale topology. -/
instance map_isContinuous (e : X ≅ Y) :
    (map e.hom).IsContinuous (topology X) (topology Y) := by
  have : (map e.hom).IsEquivalence := (mapEquivalence e).isEquivalence_functor
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  rw [precoverage_comap_map]

/-- The inverse equivalence also transports covering sieves. -/
instance map_isCocontinuous (e : X ≅ Y) :
    (map e.hom).IsCocontinuous (topology X) (topology Y) := by
  have : (mapEquivalence e).inverse.IsContinuous (topology Y) (topology X) :=
    map_isContinuous e.symm
  exact ((mapEquivalence e).toAdjunction.isCocontinuous_iff_coverPreserving
    (topology X) (topology Y)).2 (CoverPreserving.of_isContinuous _ _ _)

/-- The actual pro-étale site equivalence is a dense subsite in both directions. -/
instance mapEquivalence_inverse_isDenseSubsite (e : X ≅ Y) :
    (mapEquivalence e).inverse.IsDenseSubsite (topology Y) (topology X) := by
  have : (mapEquivalence e).functor.IsCocontinuous (topology X) (topology Y) :=
    map_isCocontinuous e
  have : (mapEquivalence e).inverse.IsCocontinuous (topology Y) (topology X) :=
    map_isCocontinuous e.symm
  exact (mapEquivalence e).isDenseSubsite_inverse_of_isCocontinuous _ _

/-- Pullback of pro-étale sheaves along a scheme isomorphism. -/
def sheafEquivalence (e : X ≅ Y) (A : Type*) [Category* A] :
    Sheaf (topology Y) A ≌ Sheaf (topology X) A :=
  (mapEquivalence e.symm).sheafCongr (topology Y) (topology X) A

/-- Scheme-isomorphism pullback preserves the actual continuous-function coefficient sheaf. -/
def ellAdicSheafIso (e : X ≅ Y) (ℓ : ℕ) [Fact ℓ.Prime] :
    (sheafEquivalence e AddCommGrpCat.{u}).functor.obj (Y.ellAdicSheaf ℓ) ≅
      X.ellAdicSheaf ℓ :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- The coefficient comparison is the identity on the underlying continuous functions. -/
@[simp] theorem ellAdicSheafIso_hom_app (e : X ≅ Y) (ℓ : ℕ) [Fact ℓ.Prime]
    (U : X.ProEt) (s : C(U.left, ℤ_[ℓ])) :
    (ellAdicSheafIso e ℓ).hom.hom.app (Opposite.op U) s = s := rfl

end AlgebraicGeometry.Scheme.ProEt
