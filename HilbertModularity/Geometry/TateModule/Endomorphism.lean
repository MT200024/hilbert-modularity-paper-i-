/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule
public import HilbertModularity.Algebra.TateModule.Endomorphism
public import Mathlib.RepresentationTheory.Intertwining

/-! # Morphisms of group schemes acting on Tate modules

A morphism of commutative group schemes acts covariantly on geometric points
and their integral and rational Tate modules. These maps commute with the
absolute Galois action because postcomposition commutes with precomposition.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K E : Type u) [Field K] [Field E] [Algebra K E]
  {A B C : Over (Spec (CommRingCat.of K))}
  [GrpObj A] [GrpObj B] [GrpObj C]

/-- Postcomposition by a group-scheme morphism is additive on geometric points. -/
def pointsMap (f : A ⟶ B) [IsMonHom f] : Points K E A →+ Points K E B where
  toFun x := Additive.ofMul (x.toMul ≫ f)
  map_zero' := MonObj.one_comp f
  map_add' x y := MonObj.mul_comp x.toMul y.toMul f

@[simp]
theorem pointsMap_apply (f : A ⟶ B) [IsMonHom f] (x : Points K E A) :
    (pointsMap K E f x).toMul = x.toMul ≫ f := rfl

@[simp]
theorem pointsMap_id : pointsMap K E (𝟙 A) = AddMonoidHom.id (Points K E A) := by
  ext x
  exact Category.comp_id _

/-- Maps on points compose covariantly. -/
@[simp]
theorem pointsMap_comp (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g] :
    pointsMap K E (f ≫ g) = (pointsMap K E g).comp (pointsMap K E f) := by
  ext x
  exact (Category.assoc _ _ _).symm

/-- A morphism defined over the base field commutes with the Galois action on points. -/
theorem pointsMap_galois (f : A ⟶ B) [IsMonHom f] (g : E ≃ₐ[K] E) (x : Points K E A) :
    pointsMap K E f (g • x) = g • pointsMap K E f x := by
  change (fieldPointMap K E g ≫ x.toMul) ≫ f = fieldPointMap K E g ≫ (x.toMul ≫ f)
  exact Category.assoc _ _ _

variable [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj C]
  (p : ℕ) [Fact p.Prime]

/-- A group-scheme morphism acts covariantly on the integral Tate module. -/
def integralTateMap (f : A ⟶ B) [IsMonHom f] :
    integralTate K A p →ₗ[ℤ_[p]] integralTate K B p :=
  TateModule.map p (pointsMap K (AlgebraicClosure K) f)

/-- A group-scheme morphism acts covariantly on the rational Tate module. -/
def rationalTateMap (f : A ⟶ B) [IsMonHom f] :
    rationalTate K A p →ₗ[ℚ_[p]] rationalTate K B p :=
  TateModule.rationalMap p (pointsMap K (AlgebraicClosure K) f)

@[simp]
theorem integralTateMap_id : integralTateMap K p (𝟙 A) = LinearMap.id := by
  simp [integralTateMap, TateModule.map_id]

@[simp]
theorem integralTateMap_comp (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g] :
    integralTateMap K p (f ≫ g) = (integralTateMap K p g).comp (integralTateMap K p f) := by
  simp [integralTateMap, TateModule.map_comp]

@[simp]
theorem rationalTateMap_id : rationalTateMap K p (𝟙 A) = LinearMap.id := by
  simp [rationalTateMap, TateModule.rationalMap_id]

@[simp]
theorem rationalTateMap_comp (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g] :
    rationalTateMap K p (f ≫ g) = (rationalTateMap K p g).comp (rationalTateMap K p f) := by
  simp [rationalTateMap, TateModule.rationalMap_comp]

/-- The map induced on integral Tate modules is Galois equivariant. -/
theorem integralTateMap_galois (f : A ⟶ B) [IsMonHom f]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : integralTate K A p) :
    integralTateMap K p f (integralTateRepresentation K A p g x) =
      integralTateRepresentation K B p g (integralTateMap K p f x) := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact pointsMap_galois K (AlgebraicClosure K) f g (x.val n)

/-- The map induced on rational Tate modules is Galois equivariant. -/
theorem rationalTateMap_galois (f : A ⟶ B) [IsMonHom f]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : rationalTate K A p) :
    rationalTateMap K p f (tateRepresentation K A p g x) =
      tateRepresentation K B p g (rationalTateMap K p f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x =>
    change c ⊗ₜ[ℤ_[p]] integralTateMap K p f (integralTateRepresentation K A p g x) =
      c ⊗ₜ[ℤ_[p]] integralTateRepresentation K B p g (integralTateMap K p f x)
    rw [integralTateMap_galois]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A geometric morphism gives an intertwiner of integral Galois representations. -/
def integralTateIntertwiningMap (f : A ⟶ B) [IsMonHom f] :
    (integralTateRepresentation K A p).IntertwiningMap (integralTateRepresentation K B p) where
  toLinearMap := integralTateMap K p f
  isIntertwining' g := LinearMap.ext (integralTateMap_galois K p f g)

/-- A geometric morphism gives an intertwiner of rational Galois representations. -/
def rationalTateIntertwiningMap (f : A ⟶ B) [IsMonHom f] :
    (tateRepresentation K A p).IntertwiningMap (tateRepresentation K B p) where
  toLinearMap := rationalTateMap K p f
  isIntertwining' g := LinearMap.ext (rationalTateMap_galois K p f g)

end AlgebraicGeometry.GroupScheme
