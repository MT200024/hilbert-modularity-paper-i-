/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GroupFiber
public import HilbertModularity.CategoryTheory.GroupObjectReflection

/-! # Finite étale group schemes as group objects in finite covers

The fully faithful inclusion into schemes over the base reflects the given
group law. Forgetting the resulting finite-cover group object recovers the
original group scheme, with the identity on its underlying scheme.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory finiteEtaleBraidedCategory

/-- Forgetting finite étaleness preserves the canonical braided product structure. -/
instance finiteEtaleForget_braided (S : Scheme.{u}) : (finiteEtaleForget S).Braided :=
  Functor.Braided.ofChosenFiniteProducts _

variable {S : Scheme.{u}} (A : CommGrp (Over S))
  [AlgebraicGeometry.Etale A.X.hom] [IsFinite A.X.hom]

/-- Regard the actual underlying finite étale group scheme as a finite cover. -/
def finiteEtaleGroupCover : S.FiniteEtale :=
  ⟨Etale.mk A.X.hom, by change IsFinite A.X.hom; infer_instance⟩

/-- Reflect the given group scheme law to its actual finite étale cover. -/
def finiteEtaleGroupObject : CommGrp S.FiniteEtale := by
  letI : GrpObj ((finiteEtaleForget S).obj (finiteEtaleGroupCover A)) := A.grp
  letI : IsCommMonObj ((finiteEtaleForget S).obj (finiteEtaleGroupCover A)) := A.comm
  exact (finiteEtaleForgetFullyFaithful S).commGrp (finiteEtaleGroupCover A)

/-- The reflected group object recovers the original group scheme after forgetting finiteness. -/
def finiteEtaleGroupObjectIso :
    (finiteEtaleForget S).mapCommGrp.obj (finiteEtaleGroupObject A) ≅ A := by
  letI : GrpObj ((finiteEtaleForget S).obj (finiteEtaleGroupCover A)) := A.grp
  letI : IsCommMonObj ((finiteEtaleForget S).obj (finiteEtaleGroupCover A)) := A.comm
  exact (finiteEtaleForgetFullyFaithful S).commGrpMapIso (finiteEtaleGroupCover A)

/-- The underlying scheme of the comparison is the identity of the given group scheme. -/
@[simp]
theorem finiteEtaleGroupObjectIso_hom :
    (finiteEtaleGroupObjectIso A).hom.hom.hom.hom = 𝟙 A.X := rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory finiteEtaleBraidedCategory
variable {S : Scheme.{u}} {A B D : CommGrp (Over S)}
  [AlgebraicGeometry.Etale A.X.hom] [IsFinite A.X.hom]
  [AlgebraicGeometry.Etale B.X.hom] [IsFinite B.X.hom]

/-- A morphism between finite étale group schemes lifts through the fully faithful inclusion. -/
def finiteEtaleGroupObjectMap (f : A ⟶ B) :
    finiteEtaleGroupObject A ⟶ finiteEtaleGroupObject B :=
  (finiteEtaleForgetFullyFaithful S).mapCommGrp.preimage
    ((finiteEtaleGroupObjectIso A).hom ≫ f ≫ (finiteEtaleGroupObjectIso B).inv)

/-- The lifted morphism recovers the original group-scheme morphism under the comparison maps. -/
@[simp]
theorem finiteEtaleGroupObjectMap_forget (f : A ⟶ B) :
    (finiteEtaleForget S).mapCommGrp.map (finiteEtaleGroupObjectMap f) =
      (finiteEtaleGroupObjectIso A).hom ≫ f ≫ (finiteEtaleGroupObjectIso B).inv :=
  (finiteEtaleForgetFullyFaithful S).mapCommGrp.map_preimage _

/-- Lifting finite étale group schemes preserves identity morphisms. -/
@[simp]
theorem finiteEtaleGroupObjectMap_id :
    finiteEtaleGroupObjectMap (𝟙 A) = 𝟙 (finiteEtaleGroupObject A) := by
  apply (finiteEtaleForgetFullyFaithful S).mapCommGrp.map_injective
  simp

/-- Lifting finite étale group schemes preserves composition. -/
@[simp]
theorem finiteEtaleGroupObjectMap_comp
    [AlgebraicGeometry.Etale D.X.hom] [IsFinite D.X.hom] (f : A ⟶ B) (g : B ⟶ D) :
    finiteEtaleGroupObjectMap (f ≫ g) =
      finiteEtaleGroupObjectMap f ≫ finiteEtaleGroupObjectMap g := by
  apply (finiteEtaleForgetFullyFaithful S).mapCommGrp.map_injective
  simp [Category.assoc]

end AlgebraicGeometry.Scheme
