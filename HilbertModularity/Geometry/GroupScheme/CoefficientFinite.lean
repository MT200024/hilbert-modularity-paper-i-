/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.CoefficientFinite
public import HilbertModularity.Geometry.GroupScheme.PrimeTorsion
public import HilbertModularity.Geometry.TateModule.FiniteGeneration

/-! # Finite actual RM-prime Tate lattices

Finite-surjective multiplication gives finite generation of the actual
Tate lattice over its RM-prime completion. Consequently determinant
specialization only requires freeness of that lattice. See
[TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (R : Type*) [CommRing R] [Module R (Points K (AlgebraicClosure K) A)]
  (p : ℕ) [Fact p.Prime]
  [IsFinite (multiplicationMap K A p).left] [Surjective (multiplicationMap K A p).left]

/-- The actual geometric RM-prime Tate lattice is finite over its completed coefficient ring. -/
theorem primeIntegralTate_finite (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A) J e he hJ
    Module.Finite (AdicCompletion J R) (integralTate K A p) :=
  TateModule.coefficientPrime_finite p R (Points K (AlgebraicClosure K) A) J e he hJ

variable
  (hφ : ∀ r, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    Module.toAddMonoidEnd R (Points K (AlgebraicClosure K) A) r =
      pointsMap K (AlgebraicClosure K) f)

/-- Freeness suffices for actual torsion determinant specialization; geometric finiteness supplies finite generation. -/
theorem det_coefficientTorsion_of_free_primeLattice (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    ∀ [Module.Free (AdicCompletion (Ideal.span {a}) R) (integralTate K A p)],
    LinearMap.det (coefficientTorsionRepresentation K A R hφ a g) =
      AdicCompletion.evalOneₐ (Ideal.span {a})
        (LinearMap.det (primeIntegralTateRepresentation K A R hφ p (Ideal.span {a}) e he hJ g)) := by
  let := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
    (Ideal.span {a}) e he hJ
  intro _
  have := primeIntegralTate_finite K A R p (Ideal.span {a}) e he hJ
  exact det_coefficientTorsion_of_primeLattice K A R hφ p a b hab e he hJ g

end AlgebraicGeometry.GroupScheme
