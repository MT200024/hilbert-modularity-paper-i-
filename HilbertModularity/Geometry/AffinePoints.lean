/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.IsAlgClosed.IntegralPoints
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Affine geometric points and field extension

The existing affine spectrum/algebra correspondence also identifies morphisms
in the category over the ground-field spectrum.
-/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Spec
universe u
section Algebras
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- Affine points in the category over `Spec R` are precisely algebra homomorphisms. -/
def overHomEquivAlgHom :
    (Over.mk (Spec.algebraMap R B) ⟶ Over.mk (Spec.algebraMap R A)) ≃ (A →ₐ[R] B) :=
  (show (Over.mk (Spec.algebraMap R B) ⟶ Over.mk (Spec.algebraMap R A)) ≃
      {f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) //
        f ≫ Spec.algebraMap R A = Spec.algebraMap R B} from
    { toFun := fun f => ⟨f.left, f.w⟩
      invFun := fun f => Over.homMk f.val f.property
      left_inv := fun f => by apply Over.OverMorphism.ext; rfl
      right_inv := fun f => by apply Subtype.ext; rfl }).trans Spec.homEquivAlgHom

/-- The algebra map corresponding to an affine over-morphism is its spectrum preimage. -/
@[simp]
theorem overHomEquivAlgHom_toRingHom
    (f : Over.mk (Spec.algebraMap R B) ⟶ Over.mk (Spec.algebraMap R A)) :
    (overHomEquivAlgHom R A B f).toRingHom = (Spec.preimage f.left).hom := rfl

/-- The affine over-morphism attached to an algebra point is its spectrum map. -/
@[simp]
theorem overHomEquivAlgHom_symm_left (φ : A →ₐ[R] B) :
    ((overHomEquivAlgHom R A B).symm φ).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  have h := congrArg AlgHom.toRingHom ((overHomEquivAlgHom R A B).apply_symm_apply φ)
  change (Spec.preimage ((overHomEquivAlgHom R A B).symm φ).left).hom = φ.toRingHom at h
  rw [← Spec.map_preimage ((overHomEquivAlgHom R A B).symm φ).left]
  congr 1
  ext a
  exact DFunLike.congr_fun h a

variable {R A B} {C : Type u} [CommRing C] [Algebra R C]

/-- Extending an affine point corresponds to postcomposing its algebra homomorphism. -/
theorem overHomEquivAlgHom_comp (j : B →ₐ[R] C)
    (f : Over.mk (Spec.algebraMap R B) ⟶ Over.mk (Spec.algebraMap R A)) :
    overHomEquivAlgHom R A C ((overHomEquivAlgHom R B C).symm j ≫ f) =
      j.comp (overHomEquivAlgHom R A B f) := by
  apply AlgHom.coe_ringHom_injective
  change (Spec.preimage (((overHomEquivAlgHom R B C).symm j).left ≫ f.left)).hom = _
  rw [Spec.preimage_comp]
  have hj := congrArg AlgHom.toRingHom ((overHomEquivAlgHom R B C).apply_symm_apply j)
  change (Spec.preimage ((overHomEquivAlgHom R B C).symm j).left).hom = j.toRingHom at hj
  change (Spec.preimage ((overHomEquivAlgHom R B C).symm j).left).hom.comp
    (Spec.preimage f.left).hom = j.toRingHom.comp (Spec.preimage f.left).hom
  rw [hj]

end Algebras

variable (R A B C : Type u) [Field R] [CommRing A] [Field B] [IsAlgClosed B] [Field C]
  [Algebra R A] [Algebra.IsIntegral R A] [Algebra R B] [Algebra R C]
  [Algebra B C] [IsScalarTower R B C]

/-- An integral algebra has the same affine geometric points after enlargement
of an algebraically closed geometric field. -/
theorem bijective_precomp_of_isAlgClosed :
    Function.Bijective (fun f :
      Over.mk (Spec.algebraMap R B) ⟶ Over.mk (Spec.algebraMap R A) =>
        (overHomEquivAlgHom R B C).symm (IsScalarTower.toAlgHom R B C) ≫ f) := by
  let e := overHomEquivAlgHom R A B
  let e' := overHomEquivAlgHom R A C
  have h := (AlgHom.bijective_comp_of_isAlgClosed R A B C).comp e.bijective
  have h' := e'.symm.bijective.comp h
  convert h' using 1
  funext f
  apply e'.injective
  exact (overHomEquivAlgHom_comp _ f).trans (e'.apply_symm_apply _).symm

end AlgebraicGeometry.Spec
