/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.FiniteFiber
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup

/-! # Finite étale fibres at arbitrary field-valued points

The fibre functor is defined directly by morphisms from the chosen spectrum.
Arithmetic fibres are its specialization to the algebraic closure of a rational point.
-/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme
universe u

/-- The full subcategory of the small étale category consisting of finite covers. -/
abbrev FiniteEtale (S : Scheme.{u}) :=
  (show ObjectProperty S.Etale from fun X => IsFinite X.hom).FullSubcategory

instance finiteEtale_isFinite {S : Scheme.{u}} (X : S.FiniteEtale) : IsFinite X.obj.hom :=
  X.property

variable (Ω : Type u) [Field Ω] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of Ω) ⟶ S)

/-- The fibre of a finite cover is a finite set at any field-valued point. -/
instance finite_geometricFiber (X : S.FiniteEtale) :
    Finite (Over.mk x ⟶ (Etale.forget S).obj X.obj) :=
  RationalPoint.finite_geometricFiber Ω X.obj.hom x

/-- The finite-set-valued fibre functor at the given field-valued point. -/
def finiteEtaleFiberFunctor : S.FiniteEtale ⥤ FintypeCat.{u} where
  obj X := FintypeCat.of (Over.mk x ⟶ (Etale.forget S).obj X.obj)
  map f := FintypeCat.homMk (fun y => y ≫ (Etale.forget S).map f.hom)
  map_id X := by
    apply FintypeCat.hom_ext
    intro y
    change y ≫ (Etale.forget S).map (𝟙 X.obj) = y
    rw [(Etale.forget S).map_id, Category.comp_id]
  map_comp f g := by
    apply FintypeCat.hom_ext
    intro y
    change y ≫ (Etale.forget S).map (f.hom ≫ g.hom) =
      (y ≫ (Etale.forget S).map f.hom) ≫ (Etale.forget S).map g.hom
    rw [(Etale.forget S).map_comp, Category.assoc]

variable (Ω' : Type u) [Field Ω'] (j : Ω →+* Ω')

/-- Extension of a field-valued point acts on every finite étale fibre by
precomposition with the actual spectrum map. -/
def finiteEtaleFiberFieldMap : finiteEtaleFiberFunctor Ω x ⟶
    finiteEtaleFiberFunctor Ω' (Spec.map (CommRingCat.ofHom j) ≫ x) where
  app X := FintypeCat.homMk (fun y =>
    (Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom j) ≫ x))
      (V := Over.mk x) (Spec.map (CommRingCat.ofHom j)) rfl) ≫ y)
  naturality {X Y} f := by
    apply FintypeCat.hom_ext
    intro y
    exact (Category.assoc (Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom j) ≫ x))
      (V := Over.mk x) (Spec.map (CommRingCat.ofHom j)) rfl)
      y ((Etale.forget S).map f.hom)).symm

end AlgebraicGeometry.Scheme
