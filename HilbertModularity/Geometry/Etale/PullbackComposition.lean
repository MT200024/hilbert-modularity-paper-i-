/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-! # Composition of finite étale pullbacks

The usual pullback associativity isomorphism restricts to actual finite étale
covers. Identity and composition give an equivalence under a scheme isomorphism,
and hence a homeomorphism of the actual profinite fundamental groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

universe u
variable {S T U : Scheme.{u}}

local instance etale_hasPullbacksAlong (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong (@AlgebraicGeometry.Etale) f where
  hasPullback _ _ := inferInstance

local instance etale_stableUnderBaseChangeAlong (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@AlgebraicGeometry.Etale) f where
  of_isPullback h hg := MorphismProperty.IsStableUnderBaseChange.of_isPullback h hg

set_option backward.isDefEq.respectTransparency false in
/-- The canonical composition comparison restricts to actual finite étale covers. -/
def finiteEtalePullbackComp (f : S ⟶ T) (g : T ⟶ U) :
    finiteEtalePullback (f ≫ g) ≅ finiteEtalePullback g ⋙ finiteEtalePullback f :=
  NatIso.ofComponents
    (fun X => (show ObjectProperty S.Etale from fun Y => IsFinite Y.hom).isoMk
      ((MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale) (Q := ⊤) f g).app
        X.obj))
    (by
      intro X Y h
      apply ObjectProperty.hom_ext
      exact (MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
        (Q := ⊤) f g).hom.naturality h.hom)

/-- On underlying schemes, the comparison is the usual iterated-pullback isomorphism. -/
theorem finiteEtalePullbackComp_hom_fst_fst (f : S ⟶ T) (g : T ⟶ U) (X : U.FiniteEtale) :
    ((finiteEtalePullbackComp f g).hom.app X).hom.left ≫
      Limits.pullback.fst (Limits.pullback.snd X.obj.hom g) f ≫
        Limits.pullback.fst X.obj.hom g = Limits.pullback.fst X.obj.hom (f ≫ g) :=
  MorphismProperty.Over.pullbackComp_left_fst_fst f g X.obj

set_option backward.isDefEq.respectTransparency false in
/-- Pullback along the identity is naturally the identity on finite étale covers. -/
def finiteEtalePullbackId (S : Scheme.{u}) : finiteEtalePullback (𝟙 S) ≅ 𝟭 S.FiniteEtale :=
  NatIso.ofComponents
    (fun X => (show ObjectProperty S.Etale from fun Y => IsFinite Y.hom).isoMk
      (MorphismProperty.Over.isoMk
        (asIso (Limits.pullback.fst X.obj.hom (𝟙 S)))
        (by
          change Limits.pullback.fst X.obj.hom (𝟙 S) ≫ X.obj.hom =
            Limits.pullback.snd X.obj.hom (𝟙 S)
          exact Limits.pullback.condition.trans (Category.comp_id _))))
    (by
      intro X Y h
      apply ObjectProperty.hom_ext
      apply MorphismProperty.Over.Hom.ext
      change Limits.pullback.lift (Limits.pullback.fst X.obj.hom (𝟙 S) ≫ h.hom.left)
        (Limits.pullback.snd X.obj.hom (𝟙 S)) _ ≫
          Limits.pullback.fst Y.obj.hom (𝟙 S) =
            Limits.pullback.fst X.obj.hom (𝟙 S) ≫ h.hom.left
      simp)

/-- Base change along an actual scheme isomorphism is an equivalence on finite étale covers. -/
def finiteEtalePullbackEquivalence (e : S ≅ T) : T.FiniteEtale ≌ S.FiniteEtale :=
  CategoryTheory.Equivalence.mk (finiteEtalePullback e.hom) (finiteEtalePullback e.inv)
    ((finiteEtalePullbackId T).symm ≪≫
      eqToIso (congrArg finiteEtalePullback e.inv_hom_id.symm) ≪≫
        finiteEtalePullbackComp e.inv e.hom)
    ((finiteEtalePullbackComp e.hom e.inv).symm ≪≫
      eqToIso (congrArg finiteEtalePullback e.hom_inv_id) ≪≫
        finiteEtalePullbackId S)

variable (e : S ≅ T) (K : Type u) [Field K]
  (x : Spec (CommRingCat.of K) ⟶ S)

/-- A scheme isomorphism induces a bijection of the actual fundamental groups. -/
theorem etaleFundamentalGroupMap_bijective_of_iso :
    Function.Bijective (etaleFundamentalGroupMap e.hom K x) := by
  let E := (finiteEtalePullbackEquivalence e).congrLeft (E := FintypeCat.{u})
  have hb := ((Functor.FullyFaithful.ofFullyFaithful E.inverse).autMulEquivOfFullyFaithful
    (finiteArithmeticFiberFunctor K x)).bijective
  exact (finiteArithmeticFiberPullbackIso e.hom K x).symm.conjAut.bijective.comp hb

/-- The actual profinite fundamental groups are homeomorphic under a scheme isomorphism. -/
def etaleFundamentalGroupIsoEquiv :
    etaleFundamentalGroup K x ≃ₜ* etaleFundamentalGroup K (x ≫ e.hom) := by
  let a := MulEquiv.ofBijective (etaleFundamentalGroupMap e.hom K x)
    (etaleFundamentalGroupMap_bijective_of_iso e K x)
  exact
    { a with
      continuous_toFun := continuous_etaleFundamentalGroupMap e.hom K x
      continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
        (f := a.toEquiv) (continuous_etaleFundamentalGroupMap e.hom K x) }

/-- The isomorphism-induced fundamental-group equivalence preserves the actual arithmetic loops. -/
theorem etaleFundamentalGroupIsoEquiv_galois
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    etaleFundamentalGroupIsoEquiv e K x (galoisToEtaleFundamentalGroup K x g) =
      galoisToEtaleFundamentalGroup K (x ≫ e.hom) g :=
  etaleFundamentalGroupMap_galois e.hom K x g

end AlgebraicGeometry.Scheme
