/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.BaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Scheme base change of the affine Euler cover

The affine Euler scheme is the categorical pullback of its coefficient structural
map. The comparison uses the affine tensor-product pullback and the actual
Euler root-algebra equivalence of [TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric.EulerCover

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The new Euler scheme is the actual pullback of the old cover along the
coefficient-spectrum morphism. The first projection is to `Spec S`. -/
def affineSchemePullbackIso (N m : ℕ) (t : R) :
    affineScheme N m (algebraMap R S t) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (structureMap N m t) :=
  Scheme.Spec.mapIso
      (coverBaseChangeEquiv (R := R) (S := S) N m t).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R S (CoverRing N m t)).symm

/-- The pullback comparison's coefficient projection is the actual new
coefficient structural morphism. -/
theorem affineSchemePullbackIso_fst (N m : ℕ) (t : R) :
    (affineSchemePullbackIso R S N m t).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (structureMap N m t) =
      structureMap N m (algebraMap R S t) := by
  change Spec.map (CommRingCat.ofHom
      (coverBaseChangeEquiv (R := R) (S := S) N m t).toRingHom) ≫
      (pullbackSpecIso R S (CoverRing N m t)).inv ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R (CoverRing N m t)))) = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp]
  congr 1
  ext s
  exact (coverBaseChangeEquiv (R := R) (S := S) N m t).commutes s

/-- The other pullback projection is the actual Euler coefficient-change map. -/
theorem affineSchemePullbackIso_snd (N m : ℕ) (t : R) :
    (affineSchemePullbackIso R S N m t).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (structureMap N m t) =
      affineSchemeBaseChange (algebraMap R S) N m t := by
  change Spec.map (CommRingCat.ofHom
      (coverBaseChangeEquiv (R := R) (S := S) N m t).toRingHom) ≫
      (pullbackSpecIso R S (CoverRing N m t)).inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R (CoverRing N m t)))) = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  ext a
  · exact coverTensorMap_includeRight (R := R) (S := S) N m t a
  · exact coverTensorMap_includeRight (R := R) (S := S) N m t (coverRoot N m t)

/-- A mapped deck transformation commutes with the actual scheme map of
coefficient change. -/
theorem affineSchemeBaseChange_deck (N : ℕ) [NeZero N] (m : ℕ) (t : R)
    (ζ : rootsOfUnity N R) :
    affineSchemeBaseChange (algebraMap R S) N m t ≫
        (deckTransformation N m t ζ).hom =
      (deckTransformation N m (algebraMap R S t)
        (rootsOfUnity.mapHom N (algebraMap R S) ζ)).hom ≫
          affineSchemeBaseChange (algebraMap R S) N m t := by
  rw [affineSchemeBaseChange, deckTransformation_hom, deckTransformation_hom]
  erw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (coverRingMap_deck (algebraMap R S) N m t ζ)

/-- The old deck action induces the actual pullback automorphism over `Spec S`. -/
def affinePullbackDeckTransformation (N : ℕ) [NeZero N] (m : ℕ) (t : R)
    (ζ : rootsOfUnity N R) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (structureMap N m t) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (structureMap N m t) :=
  pullbackSymmetry _ _ ≪≫
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⋙
      Over.forget (Spec (CommRingCat.of S))).mapIso
        ((deckActionOver N m t ζ).unop)) ≪≫
      (pullbackSymmetry _ _).symm

/-- The pulled-back deck automorphism fixes the coefficient projection. -/
theorem affinePullbackDeckTransformation_fst (N : ℕ) [NeZero N] (m : ℕ) (t : R)
    (ζ : rootsOfUnity N R) :
    (affinePullbackDeckTransformation R S N m t ζ).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (structureMap N m t) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (structureMap N m t) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let g := structureMap N m t
  let d := ((Over.pullback f).map ((deckActionOver N m t ζ).unop.hom)).left
  change (pullbackSymmetry f g).hom ≫ d ≫
      (pullbackSymmetry f g).inv ≫ pullback.fst f g = pullback.fst f g
  rw [pullbackSymmetry_inv_comp_fst]
  have hd : d ≫ pullback.snd g f = pullback.snd g f := by
    change (pullback.lift (pullback.fst g f ≫ (deckTransformation N m t ζ).hom)
      (pullback.snd g f) _) ≫ pullback.snd g f = _
    exact pullback.lift_snd _ _ _
  rw [hd, pullbackSymmetry_hom_comp_snd]

/-- The other projection carries the original deck transformation. -/
theorem affinePullbackDeckTransformation_snd (N : ℕ) [NeZero N] (m : ℕ) (t : R)
    (ζ : rootsOfUnity N R) :
    (affinePullbackDeckTransformation R S N m t ζ).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (structureMap N m t) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (structureMap N m t) ≫ (deckTransformation N m t ζ).hom := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let g := structureMap N m t
  let d := ((Over.pullback f).map ((deckActionOver N m t ζ).unop.hom)).left
  change (pullbackSymmetry f g).hom ≫ d ≫
      (pullbackSymmetry f g).inv ≫ pullback.snd f g =
        pullback.snd f g ≫ (deckTransformation N m t ζ).hom
  rw [pullbackSymmetry_inv_comp_snd]
  have hd : d ≫ pullback.fst g f =
      pullback.fst g f ≫ (deckTransformation N m t ζ).hom := by
    change (pullback.lift (pullback.fst g f ≫ (deckTransformation N m t ζ).hom)
      (pullback.snd g f) _) ≫ pullback.fst g f = _
    exact pullback.lift_fst _ _ _
  rw [hd, ← Category.assoc, pullbackSymmetry_hom_comp_fst]

/-- The pullback comparison intertwines the actual Euler deck transformations
after mapping the root of unity to the new coefficient ring. -/
theorem affineSchemePullbackIso_deck (N : ℕ) [NeZero N] (m : ℕ) (t : R)
    (ζ : rootsOfUnity N R) :
    (affineSchemePullbackIso R S N m t).hom ≫
        (affinePullbackDeckTransformation R S N m t ζ).hom =
      (deckTransformation N m (algebraMap R S t)
        (rootsOfUnity.mapHom N (algebraMap R S) ζ)).hom ≫
          (affineSchemePullbackIso R S N m t).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, affinePullbackDeckTransformation_fst,
      affineSchemePullbackIso_fst, Category.assoc,
      affineSchemePullbackIso_fst, deckTransformation_structureMap]
  · rw [Category.assoc, affinePullbackDeckTransformation_snd,
      ← Category.assoc, affineSchemePullbackIso_snd,
      Category.assoc, affineSchemePullbackIso_snd,
      affineSchemeBaseChange_deck]

end HilbertModularity.Hypergeometric.EulerCover
