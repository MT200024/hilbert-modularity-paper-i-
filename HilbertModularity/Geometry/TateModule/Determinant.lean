/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.FiniteGeneration
public import HilbertModularity.RepresentationTheory.TateModule.Determinant

/-! # Actual geometric Tate determinant characters

Finite-surjective multiplication and the actual geometric Galois action yield
continuous determinant characters on the rational Tate module and all finite
torsion levels. Exact integral-valued rational identities specialize to these
finite characters, as required in [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K] (A : Over (Spec (CommRingCat.of K)))
  [GrpObj A] [IsCommMonObj A] [IsSeparated A.hom] [LocallyOfFiniteType A.hom]
  (p : ℕ) [Fact p.Prime]
  [IsFinite (multiplicationMap K A p).left] [Surjective (multiplicationMap K A p).left]

/-- The continuous determinant of the actual geometric rational Tate representation. -/
def continuousTateDeterminantCharacter :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* ℚ_[p]ˣ :=
  TateModule.rationalDeterminantCharacter p _ (Points K (AlgebraicClosure K) A)

/-- This character evaluates to the determinant of the actual geometric Tate action. -/
@[simp]
theorem continuousTateDeterminantCharacter_coe (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (continuousTateDeterminantCharacter K A p g : ℚ_[p]) =
      LinearMap.det (tateRepresentation K A p g) := rfl

/-- The continuous determinant of the actual geometric p-power torsion action. -/
def finiteTateDeterminantCharacter (n : ℕ) :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* (ZMod (p ^ n))ˣ :=
  TateModule.finiteLevelDeterminantCharacter p _ (Points K (AlgebraicClosure K) A)
    (points_nsmul_surjective K A p) n

/-- An exact integral-valued identity for the actual rational character specializes to every finite level. -/
theorem finiteTateDeterminantCharacter_eq_of_rational (n : ℕ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : ℤ_[p])
    (h : (continuousTateDeterminantCharacter K A p g : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] a) :
    (finiteTateDeterminantCharacter K A p n g : ZMod (p ^ n)) = PadicInt.toZModPow n a :=
  TateModule.det_finiteLevelRepresentation_eq_of_rational p _ _
    (points_nsmul_surjective K A p) n g a h

end AlgebraicGeometry.GroupScheme
