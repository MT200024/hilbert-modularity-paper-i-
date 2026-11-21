/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.FiberCoefficients
public import HilbertModularity.Geometry.GroupScheme.EtaleKernel

/-! # Actual coefficient kernels commute with base change

The kernel is the pullback along the unit. A functor preserving pullbacks and
the monoidal unit therefore identifies its image with the kernel of the image
homomorphism. Applied to scheme pullback, this identifies family coefficient
torsion with the actual coefficient torsion of a fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  [HasPullbacks C] [HasPullbacks D]
  (F : C ⥤ D) [F.Braided] [PreservesLimitsOfShape WalkingCospan F]

/-- A pullback-preserving functor also preserves pullbacks of group objects. -/
instance mapGrp_preservesPullbacks : PreservesLimitsOfShape WalkingCospan F.mapGrp := by
  have : PreservesLimitsOfShape WalkingCospan (F.mapGrp ⋙ Grp.forget D) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Grp.forget C ⋙ F))
  exact preservesLimitsOfShape_of_reflects_of_preserves F.mapGrp (Grp.forget D)

set_option backward.isDefEq.respectTransparency false in
/-- The actual group-object kernel is preserved by a pullback-preserving monoidal functor. -/
def mapPullbackKernelIso {A B : Grp C} (f : A ⟶ B) :
    F.mapGrp.obj (Grp.pullbackKernel f) ≅ Grp.pullbackKernel (F.mapGrp.map f) := by
  let e := Functor.Monoidal.εIso F.mapGrp
  have h : F.mapGrp.map (Grp.unitHom B) ≫ 𝟙 (F.mapGrp.obj B) =
      e.inv ≫ Grp.unitHom (F.mapGrp.obj B) := by
    apply (cancel_epi e.hom).1
    exact @Subsingleton.elim (Grp.trivial D ⟶ F.mapGrp.obj B) inferInstance _ _
  exact PreservesPullback.iso F.mapGrp f (Grp.unitHom B) ≪≫
    asIso (pullback.map (F.mapGrp.map f) (F.mapGrp.map (Grp.unitHom B))
      (F.mapGrp.map f) (Grp.unitHom (F.mapGrp.obj B))
      (𝟙 _) e.inv (𝟙 _) (by simp) h)

set_option backward.isDefEq.respectTransparency false in
/-- The preserved kernel isomorphism commutes with its actual first projection. -/
@[reassoc]
theorem mapPullbackKernelIso_fst {A B : Grp C} (f : A ⟶ B) :
    (F.mapPullbackKernelIso f).hom ≫
        pullback.fst (F.mapGrp.map f) (Grp.unitHom (F.mapGrp.obj B)) =
      F.mapGrp.map (pullback.fst f (Grp.unitHom B)) := by
  simp only [mapPullbackKernelIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_fst, Category.comp_id, PreservesPullback.iso_hom_fst]

set_option backward.isDefEq.respectTransparency false in
/-- Actual kernels of commutative group objects are preserved with their group structure. -/
def mapCommPullbackKernelIso {A B : CommGrp C} (f : A ⟶ B) :
    F.mapCommGrp.obj (CommGrp.pullbackKernel f) ≅
      CommGrp.pullbackKernel (F.mapCommGrp.map f) :=
  (CommGrp.fullyFaithfulForget₂Grp D).preimageIso (F.mapPullbackKernelIso f.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The commutative-group kernel comparison preserves the underlying actual inclusion. -/
@[reassoc]
theorem mapCommPullbackKernelIso_inclusion {A B : CommGrp C} (f : A ⟶ B) :
    (F.mapCommPullbackKernelIso f).hom.hom.hom.hom ≫
        Grp.kernelInclusion (F.mapCommGrp.map f).hom =
      F.map (Grp.kernelInclusion f.hom) := by
  exact congrArg (fun k => k.hom.hom) (F.mapPullbackKernelIso_fst f.hom)

end CategoryTheory.Functor

namespace AlgebraicGeometry.GroupScheme

universe u
variable {S T : Scheme.{u}} (x : T ⟶ S) {A B : CommGrp (Over S)} (f : A ⟶ B)

/-- Pulling back the actual group-scheme kernel agrees with the kernel of the pulled-back morphism. -/
def kernelBaseChangeIso :
    (Over.pullback x).mapCommGrp.obj (CommGrp.pullbackKernel f) ≅
      CommGrp.pullbackKernel ((Over.pullback x).mapCommGrp.map f) :=
  (Over.pullback x).mapCommPullbackKernelIso f

/-- The scheme-level base-change comparison preserves the actual kernel inclusion. -/
@[reassoc]
theorem kernelBaseChangeIso_inclusion :
    (kernelBaseChangeIso x f).hom.hom.hom.hom ≫
        Grp.kernelInclusion ((Over.pullback x).mapCommGrp.map f).hom =
      (Over.pullback x).map (Grp.kernelInclusion f.hom) :=
  (Over.pullback x).mapCommPullbackKernelIso_inclusion f

end AlgebraicGeometry.GroupScheme
