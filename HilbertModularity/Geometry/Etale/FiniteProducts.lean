/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteFiber
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Yoneda

/-! # Concrete finite products of finite étale covers

The terminal cover is the identity of the base; the product is the actual
scheme fibre product. These choices equip the existing finite étale category
with its cartesian monoidal structure, for group objects and their fibres.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u
variable (S : Scheme.{u})

/-- The identity cover is the terminal finite étale cover. -/
def finiteEtaleTerminal : S.FiniteEtale :=
  ⟨Etale.mk (𝟙 S), by change IsFinite (𝟙 S); infer_instance⟩

/-- The structure morphism is the unique map to the identity cover. -/
def finiteEtaleToTerminal (X : S.FiniteEtale) : X ⟶ finiteEtaleTerminal S :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk X.obj.hom (by
    change X.obj.hom ≫ 𝟙 S = X.obj.hom
    exact Category.comp_id _))

/-- The identity cover has the actual terminal universal property. -/
def finiteEtaleTerminalIsTerminal : IsTerminal (finiteEtaleTerminal S) :=
  IsTerminal.ofUniqueHom (finiteEtaleToTerminal S) (fun X f => by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    change f.hom.left = X.obj.hom
    have h := MorphismProperty.Over.w f.hom
    change f.hom.left ≫ 𝟙 S = X.obj.hom at h
    exact (Category.comp_id (show X.obj.left ⟶ S from f.hom.left)).symm.trans h)

variable {S}

/-- The actual fibre product of two finite étale covers is again a finite étale cover. -/
def finiteEtaleProduct (X Y : S.FiniteEtale) : S.FiniteEtale :=
  ⟨Etale.mk (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom), by
    change IsFinite (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom)
    infer_instance⟩

/-- The first projection of the finite étale fibre product. -/
def finiteEtaleProductFst (X Y : S.FiniteEtale) : finiteEtaleProduct X Y ⟶ X :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (pullback.fst X.obj.hom Y.obj.hom) rfl)

/-- The second projection of the finite étale fibre product. -/
def finiteEtaleProductSnd (X Y : S.FiniteEtale) : finiteEtaleProduct X Y ⟶ Y :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (pullback.snd X.obj.hom Y.obj.hom)
    pullback.condition.symm)

/-- Pair two maps of covers using the actual scheme pullback. -/
def finiteEtaleProductLift {W X Y : S.FiniteEtale} (f : W ⟶ X) (g : W ⟶ Y) :
    W ⟶ finiteEtaleProduct X Y :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (pullback.lift f.hom.left g.hom.left
      ((MorphismProperty.Over.w f.hom).trans (MorphismProperty.Over.w g.hom).symm))
    (by
      change pullback.lift f.hom.left g.hom.left _ ≫
        (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom) = W.obj.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact MorphismProperty.Over.w f.hom))

/-- The actual fibre product satisfies the binary-product universal property in finite étale covers. -/
def finiteEtaleProductIsLimit (X Y : S.FiniteEtale) :
    IsLimit (BinaryFan.mk (finiteEtaleProductFst X Y) (finiteEtaleProductSnd X Y)) :=
  BinaryFan.IsLimit.mk _ finiteEtaleProductLift
    (fun f g => by
      apply ObjectProperty.hom_ext
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift f.hom.left g.hom.left _ ≫
        pullback.fst X.obj.hom Y.obj.hom = f.hom.left
      exact pullback.lift_fst _ _ _)
    (fun f g => by
      apply ObjectProperty.hom_ext
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift f.hom.left g.hom.left _ ≫
        pullback.snd X.obj.hom Y.obj.hom = g.hom.left
      exact pullback.lift_snd _ _ _)
    (fun f g m hf hg => by
      apply ObjectProperty.hom_ext
      apply MorphismProperty.Over.Hom.ext
      change m.hom.left = pullback.lift f.hom.left g.hom.left _
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        exact congrArg (fun h : _ ⟶ X => h.hom.left) hf
      · rw [pullback.lift_snd]
        exact congrArg (fun h : _ ⟶ Y => h.hom.left) hg)

/-- Cartesian products in the existing finite étale category are actual scheme fibre products. -/
abbrev finiteEtaleCartesianMonoidalCategory (S : Scheme.{u}) :
    CartesianMonoidalCategory S.FiniteEtale :=
  .ofChosenFiniteProducts
    ⟨asEmptyCone (finiteEtaleTerminal S), finiteEtaleTerminalIsTerminal S⟩
    (fun X Y => ⟨BinaryFan.mk (finiteEtaleProductFst X Y) (finiteEtaleProductSnd X Y),
      finiteEtaleProductIsLimit X Y⟩)

/-- The finite étale category has all finite products. -/
instance finiteEtale_hasFiniteProducts (S : Scheme.{u}) : HasFiniteProducts S.FiniteEtale := by
  let := finiteEtaleCartesianMonoidalCategory S
  infer_instance

/-- Forget only finiteness and étaleness, retaining the actual scheme over the base. -/
def finiteEtaleForget (S : Scheme.{u}) : S.FiniteEtale ⥤ Over S :=
  (show ObjectProperty S.Etale from fun X => IsFinite X.hom).ι ⋙ Etale.forget S

/-- The finite étale forgetful functor is fully faithful. -/
def finiteEtaleForgetFullyFaithful (S : Scheme.{u}) : (finiteEtaleForget S).FullyFaithful :=
  (show ObjectProperty S.Etale from fun X => IsFinite X.hom).fullyFaithfulι.comp
    (Etale.forgetFullyFaithful S)

instance finiteEtaleForget_full (S : Scheme.{u}) : (finiteEtaleForget S).Full :=
  (finiteEtaleForgetFullyFaithful S).full

instance finiteEtaleForget_faithful (S : Scheme.{u}) : (finiteEtaleForget S).Faithful :=
  (finiteEtaleForgetFullyFaithful S).faithful

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor preserves the actual binary products. -/
instance finiteEtaleForget_preservesPair (S : Scheme.{u}) (X Y : S.FiniteEtale) :
    PreservesLimit (pair X Y) (finiteEtaleForget S) := by
  apply preservesLimit_of_preserves_limit_cone (finiteEtaleProductIsLimit X Y)
  apply (isLimitMapConeBinaryFanEquiv _ _ _).symm _
  exact (pullback.isLimit X.obj.hom Y.obj.hom).pullbackConeEquivBinaryFanFunctor

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor preserves the actual terminal cover. -/
instance finiteEtaleForget_preservesTerminal (S : Scheme.{u}) :
    PreservesLimit (Functor.empty.{0} S.FiniteEtale) (finiteEtaleForget S) := by
  apply preservesLimit_of_preserves_limit_cone (finiteEtaleTerminalIsTerminal S)
  apply (isLimitMapConeEmptyConeEquiv _ _).symm _
  change IsTerminal (Over.mk (𝟙 S))
  exact IsTerminal.ofUniqueHom (fun X => Over.homMk X.hom)
    (fun X f => Over.OverMorphism.ext (by simpa using f.w))

/-- Finite products of finite étale covers agree with their products as schemes over the base. -/
instance finiteEtaleForget_preservesFiniteProducts (S : Scheme.{u}) :
    PreservesFiniteProducts (finiteEtaleForget S) := by
  have : PreservesLimitsOfShape (Discrete WalkingPair) (finiteEtaleForget S) :=
    preservesBinaryProducts_of_isIso_prodComparison (finiteEtaleForget S)
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (finiteEtaleForget S)
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal _

set_option backward.isDefEq.respectTransparency false in
/-- The actual finite geometric fibre functor preserves finite products. -/
instance finiteArithmeticFiberFunctor_preservesFiniteProducts
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S) :
    PreservesFiniteProducts (finiteArithmeticFiberFunctor K x) := by
  let : PreservesFiniteProducts
      (finiteArithmeticFiberFunctor K x ⋙ CategoryTheory.forget FintypeCat.{u}) :=
    inferInstanceAs (PreservesFiniteProducts
      (finiteEtaleForget S ⋙ coyoneda.obj (Opposite.op (geometricPointOver K x))))
  exact preservesFiniteProducts_of_reflects_of_preserves
    (finiteArithmeticFiberFunctor K x) (CategoryTheory.forget FintypeCat.{u})

end AlgebraicGeometry.Scheme
