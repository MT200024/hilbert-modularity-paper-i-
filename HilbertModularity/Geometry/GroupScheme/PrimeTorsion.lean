/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.CoefficientTorsion
public import HilbertModularity.RepresentationTheory.PrimeTorsion

/-! # Geometric RM-prime lattices and actual torsion

Ground-field coefficient endomorphisms and total ramification identify the
residual actual RM-prime Tate action with the actual coefficient-torsion
Galois action. See [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (R : Type*) [CommRing R] [Module R (Points K (AlgebraicClosure K) A)]

variable
  (hφ : ∀ r, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    Module.toAddMonoidEnd R (Points K (AlgebraicClosure K) A) r =
      pointsMap K (AlgebraicClosure K) f)
  (p : ℕ) [Fact p.Prime]

/-- Actual geometric Galois action on the Tate lattice over the RM-prime completion. -/
def primeIntegralTateRepresentation (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A) J e he hJ
    Representation (AdicCompletion J R) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (integralTate K A p) := by
  haveI := points_coefficient_galois_comm K A R hφ
  exact TateModule.coefficientPrimeRepresentation p R _
    (Points K (AlgebraicClosure K) A) J e he hJ

variable [IsFinite (multiplicationMap K A p).left] [Surjective (multiplicationMap K A p).left]

/-- The actual geometric RM-prime lattice reduces equivariantly to actual coefficient torsion. -/
def primeResidualIntegralTateEquiv (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)}) :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
    ((primeIntegralTateRepresentation K A R hφ p (Ideal.span {a}) e he hJ).baseChange
      (R ⧸ Ideal.span {a})).Equiv (coefficientTorsionRepresentation K A R hφ a) := by
  haveI := points_coefficient_galois_comm K A R hφ
  exact TateModule.coefficientPrimeResidualRepresentationEquiv p R _
    (Points K (AlgebraicClosure K) A) a b hab e he hJ (points_nsmul_surjective K A p)

/-- Actual coefficient-torsion determinant is the residue of the actual RM-prime lattice determinant. -/
theorem det_coefficientTorsion_of_primeLattice (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    ∀ [Module.Free (AdicCompletion (Ideal.span {a}) R) (integralTate K A p)]
      [Module.Finite (AdicCompletion (Ideal.span {a}) R) (integralTate K A p)],
    LinearMap.det (coefficientTorsionRepresentation K A R hφ a g) =
      AdicCompletion.evalOneₐ (Ideal.span {a})
        (LinearMap.det (primeIntegralTateRepresentation K A R hφ p (Ideal.span {a}) e he hJ g)) := by
  let := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
    (Ideal.span {a}) e he hJ
  intro _ _
  have := points_coefficient_galois_comm K A R hφ
  exact TateModule.det_coefficientPrimeResidualRepresentation p R _
    (Points K (AlgebraicClosure K) A) a b hab e he hJ (points_nsmul_surjective K A p) g

/-- Actual residual dimension equals the rank of the actual RM-prime lattice. -/
theorem coefficientTorsion_prime_finrank (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal] :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    ∀ [Module.Free (AdicCompletion (Ideal.span {a}) R) (integralTate K A p)],
    Module.finrank (R ⧸ Ideal.span {a}) (coefficientTorsion K A R a) =
      Module.finrank (AdicCompletion (Ideal.span {a}) R) (integralTate K A p) := by
  let := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
    (Ideal.span {a}) e he hJ
  intro _
  exact TateModule.coefficientPrimeTorsion_finrank p R (Points K (AlgebraicClosure K) A)
    a b hab e he hJ (points_nsmul_surjective K A p)

end AlgebraicGeometry.GroupScheme
