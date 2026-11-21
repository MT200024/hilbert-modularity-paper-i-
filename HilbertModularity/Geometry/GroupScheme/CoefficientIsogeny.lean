/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.EtaleKernel
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Isogenies defined by integral coefficients

If an integral coefficient divides a finite étale multiplication map on a
separated commutative group scheme, its endomorphism and actual kernel are
finite étale. The multiplication hypotheses concern the same scheme and
remain explicit; see [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u

variable {S : Scheme.{u}} (A : CommGrp (Over S))
  (R : Type*) [CommRing R] (φ : R →+* End A)

/-- A factorization of an integer in the coefficient ring factors the actual multiplication morphism. -/
theorem coefficientEndomorphism_comp (n : ℕ) (a b : R) (hab : a * b = (n : R)) :
    (φ a).hom.hom.hom.left ≫ (φ b).hom.hom.hom.left = (n • 𝟙 A).hom.hom.hom.left := by
  have h : φ a ≫ φ b = n • 𝟙 A := by
    calc
      φ a ≫ φ b = φ (b * a) := (map_mul φ b a).symm
      _ = φ (n : R) := congrArg φ (by simpa only [mul_comm] using hab)
      _ = n • 𝟙 A := by
        rw [map_natCast]
        exact (nsmul_one n : n • (1 : End A) = n).symm
  exact congrArg (fun f : A ⟶ A => f.hom.hom.hom.left) h

/-- A coefficient dividing finite multiplication is finite on the same separated group scheme. -/
theorem coefficientEndomorphism_isFinite [IsSeparated A.X.hom]
    (n : ℕ) (a b : R) (hab : a * b = (n : R))
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] : IsFinite (φ a).hom.hom.hom.left := by
  have : IsSeparated ((φ b).hom.hom.hom.left ≫ A.X.hom) := by
    rw [(φ b).hom.hom.hom.w]
    infer_instance
  have := IsSeparated.of_comp (φ b).hom.hom.hom.left A.X.hom
  have : IsFinite ((φ a).hom.hom.hom.left ≫ (φ b).hom.hom.hom.left) := by
    rw [coefficientEndomorphism_comp A R φ n a b hab]
    infer_instance
  exact IsFinite.of_comp (φ a).hom.hom.hom.left (φ b).hom.hom.hom.left

/-- A coefficient dividing finite étale multiplication is itself étale. -/
theorem coefficientEndomorphism_etale [IsSeparated A.X.hom]
    (n : ℕ) (a b : R) (hab : a * b = (n : R))
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left] :
    Etale (φ a).hom.hom.hom.left := by
  have hba : b * a = (n : R) := by simpa only [mul_comm] using hab
  have := coefficientEndomorphism_isFinite A R φ n b a hba
  have : Etale ((φ b).hom.hom.hom.left ≫ (φ a).hom.hom.hom.left) := by
    rw [coefficientEndomorphism_comp A R φ n b a hba]
    infer_instance
  have := FormallyUnramified.of_comp (φ b).hom.hom.hom.left (φ a).hom.hom.hom.left
  have : Etale ((φ a).hom.hom.hom.left ≫ (φ b).hom.hom.hom.left) := by
    rw [coefficientEndomorphism_comp A R φ n a b hab]
    infer_instance
  exact Etale.of_comp (φ a).hom.hom.hom.left (φ b).hom.hom.hom.left

/-- A coefficient dividing surjective multiplication is surjective on the same group scheme. -/
theorem coefficientEndomorphism_surjective
    (n : ℕ) (a b : R) (hab : a * b = (n : R))
    [Surjective (n • 𝟙 A).hom.hom.hom.left] : Surjective (φ a).hom.hom.hom.left := by
  have : Surjective ((φ b).hom.hom.hom.left ≫ (φ a).hom.hom.hom.left) := by
    rw [coefficientEndomorphism_comp A R φ n b a (by simpa only [mul_comm] using hab)]
    infer_instance
  exact Surjective.of_comp (φ b).hom.hom.hom.left (φ a).hom.hom.hom.left

/-- A coefficient dividing finite multiplication has an actual finite kernel. -/
theorem coefficientKernel_isFinite [IsSeparated A.X.hom]
    (n : ℕ) (a b : R) (hab : a * b = (n : R))
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] :
    IsFinite (CommGrp.pullbackKernel (φ a)).X.hom := by
  have := coefficientEndomorphism_isFinite A R φ n a b hab
  infer_instance

/-- A coefficient dividing finite étale multiplication has an actual étale kernel. -/
theorem coefficientKernel_etale [IsSeparated A.X.hom]
    (n : ℕ) (a b : R) (hab : a * b = (n : R))
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left] :
    Etale (CommGrp.pullbackKernel (φ a)).X.hom := by
  have := coefficientEndomorphism_etale A R φ n a b hab
  infer_instance

attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory

/-- The actual coefficient kernel is a finite étale group object whenever it divides finite étale multiplication. -/
def finiteEtaleCoefficientKernel [IsSeparated A.X.hom]
    (n : ℕ) (a b : R) (hab : a * b = (n : R))
    [IsFinite (n • 𝟙 A).hom.hom.hom.left] [Etale (n • 𝟙 A).hom.hom.hom.left] :
    CommGrp S.FiniteEtale := by
  haveI := coefficientEndomorphism_isFinite A R φ n a b hab
  haveI := coefficientEndomorphism_etale A R φ n a b hab
  exact finiteEtaleKernel (φ a)

end AlgebraicGeometry.GroupScheme
