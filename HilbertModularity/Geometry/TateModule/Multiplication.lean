/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.FiniteIsogeny
public import HilbertModularity.Geometry.TateModule.Reduction

/-! # Multiplication morphisms and actual Tate reduction

Multiplication is constructed inside the cartesian monoid-object category.
Its action on geometric points is ordinary repeated addition. When this actual
morphism is finite and surjective, geometric point lifting supplies the
divisibility needed for the Tate reduction comparison in [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K] (A : Over (Spec (CommRingCat.of K)))
  [GrpObj A] [IsCommMonObj A]

/-- The actual multiplication-by-`n` morphism of a commutative group scheme. -/
def multiplicationMap (n : ℕ) : A ⟶ A := ((𝟙 (Mon.mk A)) ^ n).hom

instance multiplicationMap_isMonHom (n : ℕ) : IsMonHom (multiplicationMap K A n) :=
  inferInstanceAs (IsMonHom (((𝟙 (Mon.mk A)) ^ n).hom))

/-- Multiplication as a scheme morphism acts by repeated addition on actual points. -/
@[simp]
theorem pointsMap_multiplication (E : Type u) [Field E] [Algebra K E]
    (n : ℕ) (x : Points K E A) : pointsMap K E (multiplicationMap K A n) x = n • x := by
  change x.toMul ≫ ((𝟙 (Mon.mk A)) ^ n).hom = x.toMul ^ n
  rw [Mon.Hom.hom_pow]
  change x.toMul ≫ (𝟙 A) ^ n = x.toMul ^ n
  rw [MonObj.comp_pow, Category.comp_id]

/-- A finite surjective multiplication morphism makes the geometric point group divisible by `n`. -/
theorem points_nsmul_surjective (n : ℕ)
    [IsFinite (multiplicationMap K A n).left] [Surjective (multiplicationMap K A n).left] :
    Function.Surjective (fun x : Points K (AlgebraicClosure K) A => n • x) := by
  intro x
  obtain ⟨y, hy⟩ := pointsMap_surjective_of_finite_surjective K (multiplicationMap K A n) x
  exact ⟨y, (pointsMap_multiplication K A (AlgebraicClosure K) n y).symm.trans hy⟩

variable (p : ℕ) [Fact p.Prime]
  [IsFinite (multiplicationMap K A p).left] [Surjective (multiplicationMap K A p).left]

attribute [local instance] TateModule.torsionCoefficientAlgebra TateModule.torsionCoefficientScalarTower

/-- Actual finite-surjective multiplication supplies the geometric torsion comparison. -/
def residualTateEquivOfMultiplication :
    ((integralTateRepresentation K A p).baseChange (ZMod (p ^ 1))).Equiv
      (pTorsionRepresentation K A p) :=
  residualIntegralTateEquiv K A p (points_nsmul_surjective K A p)

/-- The actual geometric torsion determinant is the reduction of an exact integral-valued Tate determinant. -/
theorem det_pTorsion_of_multiplication [Module.Finite ℤ_[p] (integralTate K A p)]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : ℤ_[p])
    (h : LinearMap.det (tateRepresentation K A p g) = algebraMap ℤ_[p] ℚ_[p] a) :
    LinearMap.det (pTorsionRepresentation K A p g) = PadicInt.toZModPow 1 a :=
  TateModule.det_torsionRepresentation_eq_of_rational p _ _ (points_nsmul_surjective K A p) g a h

end AlgebraicGeometry.GroupScheme
