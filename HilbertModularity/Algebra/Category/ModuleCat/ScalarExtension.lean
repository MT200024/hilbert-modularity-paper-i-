/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Native tensor products and categorical scalar extension -/

@[expose] public noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat
universe u v w
variable (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{v} R)

/-- Scalar extension along the algebra map is the native tensor-product module. -/
def extendScalarsTensorIso :
    (extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  let T (a : Algebra R S) : ModuleCat S := by
    letI := a
    exact ModuleCat.of S (S ⊗[R] M)
  exact eqToIso (congrArg T (toAlgebra_algebraMap (R := R) (S := S)))

/-- The canonical tensor comparison preserves pure tensors. -/
@[simp]
theorem extendScalarsTensorIso_tmul (s : S) (m : M) :
    (extendScalarsTensorIso R S M).hom (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m := by
  let T (a : Algebra R S) : ModuleCat S := by
    letI := a
    exact ModuleCat.of S (S ⊗[R] M)
  let t (a : Algebra R S) : T a := by
    letI := a
    exact s ⊗ₜ[R] m
  have ht (a b : Algebra R S) (h : a = b) :
      (eqToIso (congrArg T h)).hom (t a) = t b := by
    subst b
    rfl
  exact ht _ _ (toAlgebra_algebraMap (R := R) (S := S))

/-- The native tensor comparison is natural for every original module morphism. -/
@[reassoc]
theorem extendScalarsTensorIso_naturality {N : ModuleCat.{v} R} (f : M ⟶ N) :
    (extendScalars (algebraMap R S)).map f ≫ (extendScalarsTensorIso R S N).hom =
      (extendScalarsTensorIso R S M).hom ≫ ModuleCat.ofHom (f.hom.baseChange S) := by
  apply ExtendScalars.hom_ext
  intro m
  change (extendScalarsTensorIso R S N).hom
      ((extendScalars (algebraMap R S)).map f ((1 : S) ⊗ₜ[R, algebraMap R S] m)) =
    f.hom.baseChange S ((extendScalarsTensorIso R S M).hom
      ((1 : S) ⊗ₜ[R, algebraMap R S] m))
  rw [ExtendScalars.map_tmul]
  have h := congrArg (f.hom.baseChange S) (extendScalarsTensorIso_tmul R S M 1 m)
  exact (extendScalarsTensorIso_tmul R S N 1 (f m)).trans h.symm

end ModuleCat
