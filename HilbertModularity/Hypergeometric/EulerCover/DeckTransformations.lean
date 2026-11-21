/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover
public import HilbertModularity.NumberTheory.PowerResidue

/-! # The actual deck transformations of the affine Euler family

The coefficient roots of unity act by fixing the branch coordinate and scaling
the adjoined coordinate. This is the deck action used with the fixed primitive
character in [TripathiGoswamiRevised].
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry

namespace HilbertModularity.Hypergeometric.EulerCover

universe u
variable {R : Type u} [CommRing R] (N : ℕ) [NeZero N] (m : ℕ) (t : R)

/-- The coefficient roots of unity act on the actual Euler algebra and fix its entire base ring. -/
def deckAlgebraAction :
    rootsOfUnity N R →* (CoverRing N m t ≃ₐ[BaseRing t] CoverRing N m t) :=
  (AdjoinRoot.rootScaling N (radicand N m t)).comp
    (rootsOfUnity.mapHom N ((algebraMap R[X] (BaseRing t)).comp Polynomial.C))

/-- The actual deck action scales the covering coordinate once by the original root of unity. -/
theorem deckAlgebraAction_root (ζ : rootsOfUnity N R) :
    deckAlgebraAction N m t ζ (coverRoot N m t) =
      (algebraMap R[X] (BaseRing t) (C ((ζ : Rˣ) : R))) • coverRoot N m t := by
  exact AdjoinRoot.rootScaling_root N (radicand N m t)
    (rootsOfUnity.mapHom N ((algebraMap R[X] (BaseRing t)).comp Polynomial.C) ζ)

/-- The actual spectrum isomorphism induced by a deck transformation. -/
def deckTransformation (ζ : rootsOfUnity N R) : affineScheme N m t ≅ affineScheme N m t :=
  Scheme.Spec.mapIso (deckAlgebraAction N m t ζ).toRingEquiv.toCommRingCatIso.op

/-- The deck isomorphism is the spectrum map of the specified algebra automorphism. -/
theorem deckTransformation_hom (ζ : rootsOfUnity N R) :
    (deckTransformation N m t ζ).hom =
      Spec.map (CommRingCat.ofHom (deckAlgebraAction N m t ζ).toRingHom) := rfl

/-- Deck transformations preserve the actual coefficient-parameter structural morphism. -/
theorem deckTransformation_structureMap (ζ : rootsOfUnity N R) :
    (deckTransformation N m t ζ).hom ≫ structureMap N m t = structureMap N m t := by
  rw [deckTransformation_hom, structureMap]
  erw [← Spec.map_comp]
  congr 1
  ext a
  exact (deckAlgebraAction N m t ζ).commutes
    ((algebraMap R[X] (BaseRing t)) (C a))

/-- The actual deck transformations form an opposite-automorphism action over
the original coefficient scheme. -/
def deckActionOver :
    rootsOfUnity N R →* (Aut (Over.mk (structureMap N m t)))ᵐᵒᵖ where
  toFun ζ := MulOpposite.op
    (Over.isoMk (deckTransformation N m t ζ) (deckTransformation_structureMap N m t ζ))
  map_one' := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    apply Over.OverMorphism.ext
    change (deckTransformation N m t 1).hom = 𝟙 _
    rw [deckTransformation_hom, map_one]
    exact Spec.map_id _
  map_mul' ζ η := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    apply Over.OverMorphism.ext
    change (deckTransformation N m t (ζ * η)).hom =
      (deckTransformation N m t ζ).hom ≫ (deckTransformation N m t η).hom
    rw [deckTransformation_hom, deckTransformation_hom, deckTransformation_hom]
    erw [← Spec.map_comp]
    congr 1
    exact congrArg (fun φ : CoverRing N m t ≃ₐ[BaseRing t] CoverRing N m t =>
      CommRingCat.ofHom φ.toRingHom) ((deckAlgebraAction N m t).map_mul ζ η)

end HilbertModularity.Hypergeometric.EulerCover
