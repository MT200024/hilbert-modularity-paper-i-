/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Coefficients on the actual pro-étale cohomology groups

Multiplication on the sheaf of continuous p-adic integer-valued functions
induces the natural p-adic integer action on mathlib's pro-étale cohomology.
Rationalization uses this action, as required for the relative cohomological
realization in [TripathiGoswamiRevised].
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u
variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Scalar multiplication on the actual p-adic coefficient sheaf. -/
def ellAdicSheafScalar (a : ℤ_[ℓ]) : X.ellAdicSheaf ℓ ⟶ X.ellAdicSheaf ℓ where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom (Module.toAddMonoidEnd ℤ_[ℓ] _ a)
      naturality := by
        intro U V f
        ext g
        rfl }

/-- The unit scalar induces the identity of the coefficient sheaf. -/
@[simp] theorem ellAdicSheafScalar_one : ellAdicSheafScalar X ℓ 1 = 𝟙 _ := by
  ext U f
  change C(U.unop.left, ℤ_[ℓ]) at f
  change (1 : ℤ_[ℓ]) • f = f
  exact one_smul ℤ_[ℓ] f

/-- The zero scalar induces the zero morphism of the coefficient sheaf. -/
@[simp] theorem ellAdicSheafScalar_zero : ellAdicSheafScalar X ℓ 0 = 0 := by
  ext U f
  change C(U.unop.left, ℤ_[ℓ]) at f
  change (0 : ℤ_[ℓ]) • f = 0
  exact zero_smul ℤ_[ℓ] f

/-- Addition of p-adic coefficients is addition of the actual sheaf endomorphisms. -/
@[simp] theorem ellAdicSheafScalar_add (a b : ℤ_[ℓ]) :
    ellAdicSheafScalar X ℓ (a + b) = ellAdicSheafScalar X ℓ a + ellAdicSheafScalar X ℓ b := by
  ext U f
  change C(U.unop.left, ℤ_[ℓ]) at f
  change (a + b) • f = a • f + b • f
  exact add_smul a b f

/-- Multiplication of coefficients is composition in the actual coefficient sheaf. -/
@[simp] theorem ellAdicSheafScalar_mul (a b : ℤ_[ℓ]) :
    ellAdicSheafScalar X ℓ (a * b) = ellAdicSheafScalar X ℓ b ≫ ellAdicSheafScalar X ℓ a := by
  ext U f
  change C(U.unop.left, ℤ_[ℓ]) at f
  change (a * b) • f = a • (b • f)
  exact mul_smul a b f

private abbrev cohomologyCoefficients : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (sheafCompose (ProEt.topology X) AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ)

local instance ellAdicSheafLift_additive :
    (sheafCompose (ProEt.topology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).Additive where
  map_add := by
    intro F G f g
    ext U x
    rfl

/-- The induced scalar endomorphism of the actual pro-étale cohomology group. -/
def ellAdicCohomologyScalar (n : ℕ) (a : ℤ_[ℓ]) :
    X.EllAdicCohomology ℓ n →+ X.EllAdicCohomology ℓ n :=
  Sheaf.H.map ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map
    (ellAdicSheafScalar X ℓ a)) n

/-- The p-adic coefficient ring acts on the existing cohomology group through its actual sheaf action. -/
def ellAdicCohomologyScalarAction (n : ℕ) :
    ℤ_[ℓ] →+* AddMonoid.End (X.EllAdicCohomology ℓ n) where
  toFun := ellAdicCohomologyScalar X ℓ n
  map_one' := by
    ext x
    change Sheaf.H (cohomologyCoefficients X ℓ) n at x
    simp only [ellAdicCohomologyScalar, ellAdicSheafScalar_one]
    exact Sheaf.H.map_id_apply (F := cohomologyCoefficients X ℓ) x
  map_zero' := by
    ext x
    change Sheaf.H.map ((sheafCompose (ProEt.topology X)
      AddCommGrpCat.uliftFunctor.{u + 1}).map (ellAdicSheafScalar X ℓ 0)) n x = 0
    simp only [ellAdicSheafScalar_zero, Functor.map_zero]
    change Abelian.Ext.comp x (Abelian.Ext.mk₀
      (0 : cohomologyCoefficients X ℓ ⟶ cohomologyCoefficients X ℓ)) (add_zero n) = 0
    rw [Abelian.Ext.mk₀_zero]
    exact Abelian.Ext.comp_zero x _ _ _ _
  map_add' a b := by
    ext x
    change Sheaf.H (cohomologyCoefficients X ℓ) n at x
    simp only [ellAdicCohomologyScalar, ellAdicSheafScalar_add, Functor.map_add]
    exact Sheaf.H.map_add_apply (F := cohomologyCoefficients X ℓ)
      (G := cohomologyCoefficients X ℓ) _ _ x
  map_mul' a b := by
    ext x
    change Sheaf.H (cohomologyCoefficients X ℓ) n at x
    change ellAdicCohomologyScalar X ℓ n (a * b) x =
      ellAdicCohomologyScalar X ℓ n a (ellAdicCohomologyScalar X ℓ n b x)
    simp only [ellAdicCohomologyScalar, ellAdicSheafScalar_mul, Functor.map_comp]
    exact Sheaf.H.map_comp_apply (F := cohomologyCoefficients X ℓ)
      (G := cohomologyCoefficients X ℓ) (G' := cohomologyCoefficients X ℓ) _ _ x

/-- Natural p-adic coefficients on mathlib's pro-étale cohomology groups. -/
instance ellAdicCohomologyModule (n : ℕ) : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n) :=
  Module.compHom _ (ellAdicCohomologyScalarAction X ℓ n)

/-- The coefficient action is induced by the actual multiplication map of coefficient sheaves. -/
theorem ellAdicCohomology_smul (n : ℕ) (a : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ n) :
    a • x = Sheaf.H.map ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map
      (ellAdicSheafScalar X ℓ a)) n x := rfl

/-- Rational p-adic cohomology obtained from the actual integral pro-étale cohomology. -/
abbrev RationalEllAdicCohomology (n : ℕ) :=
  ℚ_[ℓ] ⊗[ℤ_[ℓ]] X.EllAdicCohomology ℓ n

end AlgebraicGeometry.Scheme
