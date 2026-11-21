/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.FiniteFiber
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Lifting geometric points through finite surjective morphisms

A finite surjective morphism has a nonempty discrete geometric fibre.
Over an algebraically closed field its closed points are rational points,
so every geometric point lifts. This supplies point-surjectivity in the
Tate isogeny comparison of [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.RationalPoint

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]
  {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Surjective f]

/-- Every algebraically closed field-valued point lifts through a finite surjective morphism. -/
theorem nonempty_geometricFiber (x : Spec (CommRingCat.of K) ⟶ S) :
    Nonempty (Over.mk x ⟶ Over.mk f) := by
  let q := pullback.snd f x
  have : IsLocallyArtinian (pullback f x) := IsLocallyArtinian.of_locallyQuasiFinite q
  obtain ⟨y, _⟩ := (Surjective.surj (f := q)) (IsLocalRing.closedPoint K)
  let z : Scheme.RationalPoint q :=
    ⟨pointOfClosedPoint q y isClosed_singleton, pointOfClosedPoint_comp q y isClosed_singleton⟩
  exact ⟨(pullbackEquiv K f x).symm z⟩

end AlgebraicGeometry.Scheme.RationalPoint

namespace AlgebraicGeometry.Scheme.RationalPoint
universe u
variable (K : Type u) [Field K] [IsAlgClosed K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S) {A B : Over S}
  (f : A ⟶ B) [IsFinite f.left] [Surjective f.left]

/-- A finite surjective morphism over any base is surjective on geometric points over that base. -/
theorem over_postcomp_surjective :
    Function.Surjective (fun a : Over.mk x ⟶ A => a ≫ f) := by
  intro b
  obtain ⟨y⟩ := nonempty_geometricFiber K f.left b.left
  let a : Over.mk x ⟶ A := Over.homMk y.left (by
    have hw : y.left ≫ f.left = b.left := y.w
    have hb : b.left ≫ B.hom = x := b.w
    exact (congrArg (fun t => y.left ≫ t) f.w.symm).trans
      ((Category.assoc y.left f.left B.hom).symm.trans
        ((congrArg (fun t => t ≫ B.hom) hw).trans hb)))
  refine ⟨a, ?_⟩
  apply Over.OverMorphism.ext
  exact y.w

end AlgebraicGeometry.Scheme.RationalPoint
