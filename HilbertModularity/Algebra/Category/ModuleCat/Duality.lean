/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.Category.ModuleCat.FunctorCategory
public import HilbertModularity.LinearAlgebra.CoefficientDual
public import Mathlib.CategoryTheory.Groupoid

/-! # Cohomological duals of module-valued groupoid families

Linear duality reverses module maps. Composing with inversion of paths gives
the covariant contragredient family. Endomorphisms are transposed, without
inverting their coefficient values, as in [TripathiGoswami, dual convention].
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace ModuleCat
universe u v w w'
variable (R : Type u) [CommRing R]

/-- Linear duality as a contravariant functor on modules. -/
def dualFunctor : (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{max u v} R where
  obj M := ModuleCat.of R (Module.Dual R M.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id M := by
    ext φ v
    rfl
  map_comp f g := by
    ext φ v
    rfl

/-- The underlying map of the dual functor is the ordinary transpose. -/
@[simp] theorem dualFunctor_map_hom {M N : (ModuleCat.{v} R)ᵒᵖ} (f : M ⟶ N) :
    ((dualFunctor R).map f).hom = f.unop.hom.dualMap := rfl

variable {C : Type w} [Groupoid.{w'} C]

/-- The cohomological dual of a groupoid family uses inverse paths and ordinary linear duals. -/
def cohDual (F : C ⥤ ModuleCat.{v} R) : C ⥤ ModuleCat.{max u v} R :=
  (Groupoid.invEquivalence C).functor ⋙ F.op ⋙ dualFunctor R

/-- The fibre of the cohomological dual is the ordinary dual of the original fibre. -/
@[simp] theorem cohDual_obj (F : C ⥤ ModuleCat.{v} R) (x : C) :
    (cohDual R F).obj x = ModuleCat.of R (Module.Dual R (F.obj x)) := rfl

/-- The dual family acts by transposing transport along the inverse path. -/
@[simp] theorem cohDual_map_hom (F : C ⥤ ModuleCat.{v} R) {x y : C} (f : x ⟶ y) :
    ((cohDual R F).map f).hom = (F.map (inv f)).hom.dualMap := by
  rw [← Groupoid.inv_eq_inv]
  rfl

/-- A natural family map induces the transposed map between cohomological dual families. -/
def cohDualMap {F G : C ⥤ ModuleCat.{v} R} (η : F ⟶ G) : cohDual R G ⟶ cohDual R F :=
  Functor.whiskerLeft (Groupoid.invEquivalence C).functor
    (Functor.whiskerRight (NatTrans.op η) (dualFunctor R))

/-- Transposing a family endomorphism does not invert that endomorphism. -/
@[simp] theorem cohDualMap_app_hom {F G : C ⥤ ModuleCat.{v} R} (η : F ⟶ G) (x : C) :
    ((cohDualMap R η).app x).hom = (η.app x).hom.dualMap := rfl

/-- Dualizing the identity gives the identity natural transformation. -/
@[simp] theorem cohDualMap_id (F : C ⥤ ModuleCat.{v} R) :
    cohDualMap R (𝟙 F) = 𝟙 (cohDual R F) := by
  apply NatTrans.ext
  funext x
  rfl

/-- Duality reverses composition of natural transformations. -/
@[simp] theorem cohDualMap_comp {F G H : C ⥤ ModuleCat.{v} R}
    (η : F ⟶ G) (θ : G ⟶ H) :
    cohDualMap R (η ≫ θ) = cohDualMap R θ ≫ cohDualMap R η := by
  apply NatTrans.ext
  funext x
  rfl

/-- Transposing a scalar multiple preserves its scalar. -/
@[simp] theorem cohDualMap_smul {F G : C ⥤ ModuleCat.{v} R}
    (r : R) (η : F ⟶ G) : cohDualMap R (r • η) = r • cohDualMap R η := by
  apply NatTrans.ext
  funext x
  apply ModuleCat.hom_ext
  change (r • (η.app x).hom).dualMap = r • (η.app x).hom.dualMap
  ext φ v
  exact φ.map_smul r ((η.app x).hom v)

/-- An isomorphism of families induces the reverse isomorphism of their duals. -/
def cohDualIso {F G : C ⥤ ModuleCat.{v} R} (e : F ≅ G) :
    cohDual R G ≅ cohDual R F where
  hom := cohDualMap R e.hom
  inv := cohDualMap R e.inv
  hom_inv_id := by rw [← cohDualMap_comp, e.inv_hom_id, cohDualMap_id]
  inv_hom_id := by rw [← cohDualMap_comp, e.hom_inv_id, cohDualMap_id]

/-- A commutative coefficient algebra acts on the dual family by transpose. -/
def cohDualEndomorphism {A : Type*} [CommSemiring A] [Algebra R A]
    {F : C ⥤ ModuleCat.{v} R} (a : A →ₐ[R] End F) :
    A →ₐ[R] End (cohDual R F) where
  toFun c := cohDualMap R (a c)
  map_zero' := by
    apply NatTrans.ext
    funext x
    apply ModuleCat.hom_ext
    exact map_zero (AlgHom.dualEndomorphism ((functorEndApp R F x).comp a))
  map_one' := by
    apply NatTrans.ext
    funext x
    apply ModuleCat.hom_ext
    exact map_one (AlgHom.dualEndomorphism ((functorEndApp R F x).comp a))
  map_add' c d := by
    apply NatTrans.ext
    funext x
    apply ModuleCat.hom_ext
    exact map_add (AlgHom.dualEndomorphism ((functorEndApp R F x).comp a)) c d
  map_mul' c d := by
    apply NatTrans.ext
    funext x
    apply ModuleCat.hom_ext
    exact map_mul (AlgHom.dualEndomorphism ((functorEndApp R F x).comp a)) c d
  commutes' r := by
    apply NatTrans.ext
    funext x
    apply ModuleCat.hom_ext
    exact (AlgHom.dualEndomorphism ((functorEndApp R F x).comp a)).commutes r

/-- A dual coefficient acts by the transpose of the original natural endomorphism. -/
@[simp] theorem cohDualEndomorphism_apply {A : Type*} [CommSemiring A] [Algebra R A]
    {F : C ⥤ ModuleCat.{v} R} (a : A →ₐ[R] End F) (c : A) :
    cohDualEndomorphism R a c = cohDualMap R (a c) := rfl

/-- A scalar-labelled subfamily becomes a quotient with the same scalar label on the dual. -/
theorem cohDualEndomorphism_quotient {A : Type*} [CommSemiring A] [Algebra R A]
    {F G : C ⥤ ModuleCat.{v} R} (a : A →ₐ[R] End G) (i : F ⟶ G)
    (c : A) (r : R) (h : i ≫ a c = r • i) :
    cohDualEndomorphism R a c ≫ cohDualMap R i = r • cohDualMap R i := by
  rw [cohDualEndomorphism_apply, ← cohDualMap_comp, h, cohDualMap_smul]

end ModuleCat
