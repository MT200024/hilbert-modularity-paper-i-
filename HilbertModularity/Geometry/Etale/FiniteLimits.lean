/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Finite limits of finite étale covers

Pullbacks of maps of finite étale covers are their actual scheme pullbacks.
Together with the identity cover, they give all finite limits in the category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u
variable {S : Scheme.{u}}

/-- Every map between finite étale covers is itself finite. -/
instance finiteEtaleMorphism_isFinite {X Y : S.FiniteEtale} (f : X ⟶ Y) :
    IsFinite f.hom.left := by
  have : IsFinite (f.hom.left ≫ Y.obj.hom) := by
    rw [MorphismProperty.Over.w f.hom]
    exact X.property
  exact IsFinite.of_comp f.hom.left Y.obj.hom

/-- The scheme pullback of two maps of finite étale covers, as a cover of the base. -/
def finiteEtalePullbackCover {X Y Z : S.FiniteEtale} (f : X ⟶ Z) (g : Y ⟶ Z) :
    S.FiniteEtale :=
  ⟨Etale.mk (pullback.fst f.hom.left g.hom.left ≫ X.obj.hom), by
    change IsFinite (pullback.fst f.hom.left g.hom.left ≫ X.obj.hom)
    infer_instance⟩

/-- The first projection of a pullback of finite étale covers. -/
def finiteEtalePullbackFst {X Y Z : S.FiniteEtale} (f : X ⟶ Z) (g : Y ⟶ Z) :
    finiteEtalePullbackCover f g ⟶ X :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (pullback.fst f.hom.left g.hom.left) rfl)

/-- The second projection of a pullback of finite étale covers. -/
def finiteEtalePullbackSnd {X Y Z : S.FiniteEtale} (f : X ⟶ Z) (g : Y ⟶ Z) :
    finiteEtalePullbackCover f g ⟶ Y :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (pullback.snd f.hom.left g.hom.left) (by
      change pullback.snd f.hom.left g.hom.left ≫ Y.obj.hom =
        pullback.fst f.hom.left g.hom.left ≫ X.obj.hom
      rw [← MorphismProperty.Over.w f.hom, ← MorphismProperty.Over.w g.hom,
        ← Category.assoc, ← Category.assoc, pullback.condition]))

/-- Compatible maps into two covers lift to their scheme pullback over a third cover. -/
def finiteEtalePullbackLift {W X Y Z : S.FiniteEtale} {f : X ⟶ Z} {g : Y ⟶ Z}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) : W ⟶ finiteEtalePullbackCover f g :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (pullback.lift a.hom.left b.hom.left
      (show a.hom.left ≫ f.hom.left = b.hom.left ≫ g.hom.left from
        congrArg (fun k : W ⟶ Z => k.hom.left) h))
    (by
      change pullback.lift a.hom.left b.hom.left _ ≫
        (pullback.fst f.hom.left g.hom.left ≫ X.obj.hom) = W.obj.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact MorphismProperty.Over.w a.hom))

/-- The two projections form a commuting square of covers. -/
theorem finiteEtalePullback_condition {X Y Z : S.FiniteEtale}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    finiteEtalePullbackFst f g ≫ f = finiteEtalePullbackSnd f g ≫ g := by
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Over.Hom.ext
  exact pullback.condition

/-- The actual scheme pullback satisfies the universal property among finite étale covers. -/
def finiteEtalePullbackIsLimit {X Y Z : S.FiniteEtale} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit (PullbackCone.mk (finiteEtalePullbackFst f g) (finiteEtalePullbackSnd f g)
      (finiteEtalePullback_condition f g)) :=
  PullbackCone.IsLimit.mk _
    (fun s => finiteEtalePullbackLift s.fst s.snd s.condition)
    (fun s => by
      apply ObjectProperty.hom_ext
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift s.fst.hom.left s.snd.hom.left _ ≫
        pullback.fst f.hom.left g.hom.left = s.fst.hom.left
      exact pullback.lift_fst _ _ _)
    (fun s => by
      apply ObjectProperty.hom_ext
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift s.fst.hom.left s.snd.hom.left _ ≫
        pullback.snd f.hom.left g.hom.left = s.snd.hom.left
      exact pullback.lift_snd _ _ _)
    (fun s m hf hg => by
      apply ObjectProperty.hom_ext
      apply MorphismProperty.Over.Hom.ext
      change m.hom.left = pullback.lift s.fst.hom.left s.snd.hom.left _
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        exact congrArg (fun k : _ ⟶ X => k.hom.left) hf
      · rw [pullback.lift_snd]
        exact congrArg (fun k : _ ⟶ Y => k.hom.left) hg)

/-- Any pair of maps of finite étale covers has a pullback. -/
instance finiteEtale_hasPullback {X Y Z : S.FiniteEtale} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback f g :=
  ⟨⟨_, finiteEtalePullbackIsLimit f g⟩⟩

/-- The category of finite étale covers has pullbacks. -/
instance finiteEtale_hasPullbacks (S : Scheme.{u}) : HasPullbacks S.FiniteEtale :=
  hasPullbacks_of_hasLimit_cospan S.FiniteEtale

/-- The category of actual finite étale covers has all finite limits. -/
instance finiteEtale_hasFiniteLimits (S : Scheme.{u}) : HasFiniteLimits S.FiniteEtale :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting a finite étale cover to its scheme preserves the concrete pullbacks. -/
instance finiteEtaleForgetScheme_preservesCospan {X Y Z : S.FiniteEtale}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) (finiteEtaleForget S ⋙ Over.forget S) := by
  apply preservesLimit_of_preserves_limit_cone (finiteEtalePullbackIsLimit f g)
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  exact pullbackIsPullback f.hom.left g.hom.left

/-- Forgetting only the finite étale conditions preserves each pullback square. -/
instance finiteEtaleForget_preservesCospan {X Y Z : S.FiniteEtale}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) (finiteEtaleForget S) :=
  preservesLimit_of_reflects_of_preserves (finiteEtaleForget S) (Over.forget S)

/-- The inclusion of finite étale covers into schemes over the base preserves pullbacks. -/
instance finiteEtaleForget_preservesPullbacks (S : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (finiteEtaleForget S) where
  preservesLimit {K} := preservesLimit_of_iso_diagram (finiteEtaleForget S)
    (diagramIsoCospan K).symm

/-- Finite limits of finite étale covers agree with finite limits of schemes over the base. -/
instance finiteEtaleForget_preservesFiniteLimits (S : Scheme.{u}) :
    PreservesFiniteLimits (finiteEtaleForget S) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (finiteEtaleForget S)

set_option backward.isDefEq.respectTransparency false in
/-- The actual geometric fibre functor preserves all finite limits. -/
instance finiteArithmeticFiberFunctor_preservesFiniteLimits
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S) :
    PreservesFiniteLimits (finiteArithmeticFiberFunctor K x) := by
  let : PreservesFiniteLimits
      (finiteArithmeticFiberFunctor K x ⋙ CategoryTheory.forget FintypeCat.{u}) :=
    inferInstanceAs (PreservesFiniteLimits
      (finiteEtaleForget S ⋙ coyoneda.obj (Opposite.op (geometricPointOver K x))))
  exact preservesFiniteLimits_of_reflects_of_preserves
    (finiteArithmeticFiberFunctor K x) (CategoryTheory.forget FintypeCat.{u})

end AlgebraicGeometry.Scheme
