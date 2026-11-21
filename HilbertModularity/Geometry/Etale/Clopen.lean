/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Connected
public import HilbertModularity.Topology.Connected.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Connected clopen subcovers through a geometric fibre point

A clopen part of a finite étale cover is again an actual finite étale cover.
Over a Noetherian source, each geometric fibre point lies on a connected
clopen subcover.
-/

@[expose] public noncomputable section
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme
universe u
variable {S : Scheme.{u}} (X : S.FiniteEtale) (U : X.obj.left.Opens)
  (hU : IsClosed (U : Set X.obj.left))

/-- Finite étale covers of a locally Noetherian affine base have Noetherian topology. -/
instance finiteEtale_noetherianSpace [IsAffine S] [IsLocallyNoetherian S] :
    NoetherianSpace X.obj.left := by
  let f : X.obj.left ⟶ S := X.obj.hom
  have : IsFinite f := X.property
  have : IsAffine X.obj.left := isAffine_of_isAffineHom f
  have : IsLocallyNoetherian X.obj.left := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X.obj.left := {}
  infer_instance

/-- Restriction to a clopen part retains the finite étale cover structure. -/
def finiteEtaleClopenSubcover : S.FiniteEtale := by
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by simpa only [Opens.range_ι] using hU)
  exact ⟨Etale.mk (U.ι ≫ X.obj.hom), by
    change IsFinite (U.ι ≫ X.obj.hom)
    infer_instance⟩

/-- The inclusion of the clopen subcover is its original open-immersion map. -/
def finiteEtaleClopenInclusion : finiteEtaleClopenSubcover X U hU ⟶ X :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk U.ι rfl)

variable (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- A geometric point supported on the clopen part lifts to that subcover. -/
theorem finiteArithmeticFiber_lift_clopen
    (y : (finiteArithmeticFiberFunctor K x).obj X)
    (hy : y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) ∈ U) :
    ∃ z : (finiteArithmeticFiberFunctor K x).obj (finiteEtaleClopenSubcover X U hU),
      (finiteArithmeticFiberFunctor K x).map (finiteEtaleClopenInclusion X U hU) z = y := by
  have hr : Set.range y.left ⊆ Set.range U.ι := by
    rw [Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    have ha : a = IsLocalRing.closedPoint (AlgebraicClosure K) :=
      Subsingleton.elim (α := Spec (CommRingCat.of (AlgebraicClosure K))) _ _
    change y.left a ∈ (U : Set X.obj.left)
    change y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) ∈
      (U : Set X.obj.left) at hy
    simpa only [ha] using hy
  let z : Over.mk (geometricPointOver K x).hom ⟶ Over.mk (U.ι ≫ X.obj.hom) :=
    Over.homMk (IsOpenImmersion.lift U.ι y.left hr) (by
      change IsOpenImmersion.lift U.ι y.left hr ≫ (U.ι ≫ X.obj.hom) =
        (geometricPointOver K x).hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.w)
  refine ⟨z, ?_⟩
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac U.ι y.left hr

set_option backward.isDefEq.respectTransparency false in
/-- A geometric point of a Noetherian finite étale cover lies on a connected
finite étale subcover, with its actual inclusion and point lifting. -/
theorem exists_connected_finiteEtale_subcover [NoetherianSpace X.obj.left]
    (y : (finiteArithmeticFiberFunctor K x).obj X) :
    ∃ (Y : S.FiniteEtale) (i : Y ⟶ X), ConnectedSpace Y.obj.left ∧
      IsOpenImmersion i.hom.left ∧
      ∃ z : (finiteArithmeticFiberFunctor K x).obj Y,
        (finiteArithmeticFiberFunctor K x).map i z = y := by
  obtain ⟨t, hty, _, ht, htc⟩ := exists_connected_clopen_subset_of_noetherian
    (X := X.obj.left) isClopen_univ
    (x := y.left (IsLocalRing.closedPoint (AlgebraicClosure K))) (Set.mem_univ _)
  let U : X.obj.left.Opens := ⟨t, ht.isOpen⟩
  have : ConnectedSpace U.toScheme := isConnected_iff_connectedSpace.mp htc
  refine ⟨finiteEtaleClopenSubcover X U ht.isClosed,
    finiteEtaleClopenInclusion X U ht.isClosed, ?_, ?_, ?_⟩
  · exact inferInstanceAs (ConnectedSpace U.toScheme)
  · exact inferInstanceAs (IsOpenImmersion U.ι)
  · exact finiteArithmeticFiber_lift_clopen X U ht.isClosed K x y hty

end AlgebraicGeometry.Scheme
