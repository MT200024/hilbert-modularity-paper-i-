/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Maps to separated unramified schemes are detected at one point

The relative equalizer is open and closed. On a connected source, one
field-valued point in it forces the entire source to lie in the equalizer.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Hom
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Two maps from a preconnected scheme to a separated unramified target
over the same base agree if they agree after one field-valued point. -/
theorem eq_of_comp_point {S X Y : Scheme.{u}} [PreconnectedSpace X]
    (p : Y ⟶ S) [FormallyUnramified p] [LocallyOfFiniteType p] [IsSeparated p]
    (f g : X ⟶ Y) (hfg : f ≫ p = g ≫ p)
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = x ≫ g) : f = g := by
  let d := pullback.diagonal p
  let h := pullback.lift f g hfg
  let Z := pullback d h
  let q : Z ⟶ X := pullback.snd d h
  have : IsOpenImmersion d := inferInstanceAs (IsOpenImmersion (pullback.diagonal p))
  have : IsClosedImmersion d := inferInstanceAs (IsClosedImmersion (pullback.diagonal p))
  have : IsOpenImmersion q := inferInstanceAs (IsOpenImmersion (pullback.snd d h))
  have : IsClosedImmersion q := inferInstanceAs (IsClosedImmersion (pullback.snd d h))
  have hp : (x ≫ f) ≫ d = x ≫ h := by
    apply pullback.hom_ext
    · simp only [d, h, Category.assoc, pullback.diagonal_fst, pullback.lift_fst,
        Category.comp_id]
    · simpa only [d, h, Category.assoc, pullback.diagonal_snd, pullback.lift_snd,
        Category.comp_id] using hx
  let z : Spec (CommRingCat.of K) ⟶ Z := pullback.lift (x ≫ f) x hp
  have : Nonempty Z := ⟨z (IsLocalRing.closedPoint K)⟩
  have : Surjective q := q.surjective_of_finite_etale
  have : IsIso q := (isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨inferInstance, inferInstance⟩
  apply (cancel_epi q).mp
  have h₁ := congrArg (fun k : Z ⟶ pullback p p => k ≫ pullback.fst p p)
    (pullback.condition (f := d) (g := h))
  have h₂ := congrArg (fun k : Z ⟶ pullback p p => k ≫ pullback.snd p p)
    (pullback.condition (f := d) (g := h))
  have h₁' : pullback.fst d h = q ≫ f := by
    simpa only [d, h, q, Category.assoc, pullback.diagonal_fst, pullback.lift_fst,
      Category.comp_id] using h₁
  have h₂' : pullback.fst d h = q ≫ g := by
    simpa only [d, h, q, Category.assoc, pullback.diagonal_snd, pullback.lift_snd,
      Category.comp_id] using h₂
  exact h₁'.symm.trans h₂'

end AlgebraicGeometry.Scheme.Hom
