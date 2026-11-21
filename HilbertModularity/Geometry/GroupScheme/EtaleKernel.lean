/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.GroupObjectTorsion
public import HilbertModularity.Geometry.Etale.FiniteGroupScheme
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Finite étale kernels of group-scheme homomorphisms

A kernel is the actual base change of the given group-scheme homomorphism
along the unit. Finiteness and étaleness therefore pass to the kernel.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u
variable {S : Scheme.{u}} {A B : CommGrp (Over S)} (f : A ⟶ B)

/-- The second kernel projection is precisely its structure morphism to the base scheme. -/
theorem kernel_structureMap :
    (pullback.snd f.hom (Grp.unitHom B.toGrp)).hom.hom.left =
      (CommGrp.pullbackKernel f).X.hom := by
  have h := (pullback.snd f.hom (Grp.unitHom B.toGrp)).hom.hom.w
  change (pullback.snd f.hom (Grp.unitHom B.toGrp)).hom.hom.left ≫ 𝟙 S =
    (CommGrp.pullbackKernel f).X.hom at h
  exact (Category.comp_id
    (show (CommGrp.pullbackKernel f).X.left ⟶ S from
      (pullback.snd f.hom (Grp.unitHom B.toGrp)).hom.hom.left)).symm.trans h

/-- The underlying kernel square is an actual pullback of schemes along the unit section. -/
theorem kernel_isPullback :
    IsPullback (Grp.kernelInclusion f.hom).left (CommGrp.pullbackKernel f).X.hom
      f.hom.hom.hom.left η[B.X].left := by
  have h := IsPullback.map (Grp.forget (Over S) ⋙ Over.forget S)
    (IsPullback.of_hasPullback f.hom (Grp.unitHom B.toGrp))
  change IsPullback (Grp.kernelInclusion f.hom).left
    (pullback.snd f.hom (Grp.unitHom B.toGrp)).hom.hom.left
    f.hom.hom.hom.left η[B.X].left at h
  rw [kernel_structureMap] at h
  exact h

/-- The kernel of a finite group-scheme homomorphism is finite over the base. -/
instance kernel_isFinite [IsFinite f.hom.hom.hom.left] :
    IsFinite (CommGrp.pullbackKernel f).X.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
    (kernel_isPullback f) inferInstance

/-- The kernel of an étale group-scheme homomorphism is étale over the base. -/
instance kernel_etale [Etale f.hom.hom.hom.left] :
    Etale (CommGrp.pullbackKernel f).X.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
    (kernel_isPullback f) inferInstance

attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory

/-- A finite étale group-scheme homomorphism has an actual finite étale kernel group object. -/
def finiteEtaleKernel [IsFinite f.hom.hom.hom.left] [Etale f.hom.hom.hom.left] :
    CommGrp S.FiniteEtale := Scheme.finiteEtaleGroupObject (CommGrp.pullbackKernel f)

/-- Finite étale multiplication gives the actual finite étale torsion group object. -/
def finiteEtaleTorsionObject (A : CommGrp (Over S)) (n : ℕ)
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left] :
    CommGrp S.FiniteEtale := finiteEtaleKernel (n • 𝟙 A)

end AlgebraicGeometry.GroupScheme
