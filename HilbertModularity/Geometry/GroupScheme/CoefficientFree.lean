/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.CoefficientFree
public import HilbertModularity.Geometry.GroupScheme.CoefficientFinite
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Free actual RM-prime Tate lattices over DVR coefficients

The actual geometric lattice is finite free over a DVR completion at a
principal RM prime. Its determinant and rank therefore specialize to the
actual coefficient-torsion action. See [TripathiGoswami].
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

/-- The actual geometric RM-prime Tate lattice is free over its DVR completion. -/
theorem primeIntegralTate_free (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal]
    [IsDomain (AdicCompletion (Ideal.span {a}) R)]
    [IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R)] :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    Module.Free (AdicCompletion (Ideal.span {a}) R) (integralTate K A p) :=
  TateModule.coefficientPrime_free p R (Points K (AlgebraicClosure K) A) a b hab e he hJ

/-- The actual residue-field dimension equals the proved free RM-prime lattice rank. -/
theorem coefficientTorsion_dvr_finrank (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal]
    [IsDomain (AdicCompletion (Ideal.span {a}) R)]
    [IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R)] :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    Module.finrank (R ⧸ Ideal.span {a}) (coefficientTorsion K A R a) =
      Module.finrank (AdicCompletion (Ideal.span {a}) R) (integralTate K A p) := by
  let := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
    (Ideal.span {a}) e he hJ
  have := primeIntegralTate_free K A R p a b hab e he hJ
  exact coefficientTorsion_prime_finrank K A R p a b hab e he hJ

/-- A principal RM prime in the actual integral coefficient domain gives a free geometric lattice. -/
theorem primeIntegralTate_free_of_domain [IsDomain R]
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal] :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    Module.Free (AdicCompletion (Ideal.span {a}) R) (integralTate K A p) :=
  TateModule.coefficientPrime_free_of_domain p R (Points K (AlgebraicClosure K) A)
    a b ha hab e he hJ

variable
  (hφ : ∀ r, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    Module.toAddMonoidEnd R (Points K (AlgebraicClosure K) A) r =
      pointsMap K (AlgebraicClosure K) f)

/-- Actual geometric coefficient torsion specializes the determinant of the actual DVR lattice. -/
theorem det_coefficientTorsion_of_dvr (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal]
    [IsDomain (AdicCompletion (Ideal.span {a}) R)]
    [IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R)]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    LinearMap.det (coefficientTorsionRepresentation K A R hφ a g) =
      AdicCompletion.evalOneₐ (Ideal.span {a})
        (LinearMap.det (primeIntegralTateRepresentation K A R hφ p (Ideal.span {a}) e he hJ g)) := by
  let := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
    (Ideal.span {a}) e he hJ
  have := primeIntegralTate_free K A R p a b hab e he hJ
  exact det_coefficientTorsion_of_free_primeLattice K A R p hφ a b hab e he hJ g

/-- Actual torsion determinant specializes from the lattice at a nonzero principal RM prime. -/
theorem det_coefficientTorsion_of_principal_prime [IsDomain R]
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    LinearMap.det (coefficientTorsionRepresentation K A R hφ a g) =
      AdicCompletion.evalOneₐ (Ideal.span {a})
        (LinearMap.det (primeIntegralTateRepresentation K A R hφ p (Ideal.span {a}) e he hJ g)) := by
  have := AdicCompletion.isDomain_of_isMaximal_span a ha
  have := AdicCompletion.isDiscreteValuationRing_of_isMaximal_span a ha
  exact det_coefficientTorsion_of_dvr K A R p hφ a b hab e he hJ g

/-- An exact determinant identity over the actual coefficient fraction field specializes to actual RM-prime torsion. -/
theorem det_coefficientTorsion_of_fractionField [IsDomain R]
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal]
    (L : Type*) [Field L] [Algebra (AdicCompletion (Ideal.span {a}) R) L]
    [IsFractionRing (AdicCompletion (Ideal.span {a}) R) L]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (d : AdicCompletion (Ideal.span {a}) R)
    (hd :
      letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
        (Ideal.span {a}) e he hJ
      LinearMap.det ((primeIntegralTateRepresentation K A R hφ p
        (Ideal.span {a}) e he hJ).baseChange L g) =
          algebraMap (AdicCompletion (Ideal.span {a}) R) L d) :
    LinearMap.det (coefficientTorsionRepresentation K A R hφ a g) =
      AdicCompletion.evalOneₐ (Ideal.span {a}) d := by
  let := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
    (Ideal.span {a}) e he hJ
  have := AdicCompletion.isDomain_of_isMaximal_span a ha
  have := primeIntegralTate_free_of_domain K A R p a b ha hab e he hJ
  have := primeIntegralTate_finite K A R p (Ideal.span {a}) e he hJ
  rw [det_coefficientTorsion_of_principal_prime K A R p hφ a b ha hab e he hJ]
  congr 1
  apply IsFractionRing.injective (AdicCompletion (Ideal.span {a}) R) L
  exact (LinearMap.det_baseChange
    (primeIntegralTateRepresentation K A R hφ p (Ideal.span {a}) e he hJ g)).symm.trans hd

end AlgebraicGeometry.GroupScheme
