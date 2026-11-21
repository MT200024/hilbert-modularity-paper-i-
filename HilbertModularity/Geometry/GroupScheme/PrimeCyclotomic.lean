/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.PrimeScalars
public import HilbertModularity.Geometry.GroupScheme.CoefficientFree

/-! # Cyclotomic determinants on actual RM-prime torsion

An exact cyclotomic determinant identity on the fraction field of the actual
RM-prime Tate lattice specializes to the ordinary residual cyclotomic character
on the actual coefficient torsion. The characteristic-zero arithmetic identity
remains an explicit hypothesis; see [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (R : Type*) [CommRing R] [IsDomain R] [Module R (Points K (AlgebraicClosure K) A)]
  (p : ℕ) [Fact p.Prime]
  [IsFinite (multiplicationMap K A p).left] [Surjective (multiplicationMap K A p).left]
  (hφ : ∀ r, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    Module.toAddMonoidEnd R (Points K (AlgebraicClosure K) A) r =
      pointsMap K (AlgebraicClosure K) f)

/-- The actual RM-prime torsion determinant is the residual cyclotomic character when its actual fraction-field Tate factor has exact cyclotomic determinant. -/
theorem det_coefficientTorsion_eq_cyclotomic
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal]
    (j : ZMod p →+* R ⧸ Ideal.span {a})
    (L : Type*) [Field L] [Algebra (AdicCompletion (Ideal.span {a}) R) L]
    [IsFractionRing (AdicCompletion (Ideal.span {a}) R) L]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hd :
      letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
        (Ideal.span {a}) e he hJ
      LinearMap.det ((primeIntegralTateRepresentation K A R hφ p
        (Ideal.span {a}) e he hJ).baseChange L g) =
          algebraMap (AdicCompletion (Ideal.span {a}) R) L
            (TateModule.coefficientPrimeRingEquiv p R (Ideal.span {a}) e he hJ
              (PadicInt.toAdicCompletion p R (Field.cyclotomicCharacter K p g : ℤ_[p])))) :
    LinearMap.det (coefficientTorsionRepresentation K A R hφ a g) =
      j (Field.cyclotomicCharacter K p g : ℤ_[p]).toZMod := by
  rw [det_coefficientTorsion_of_fractionField K A R p hφ a b ha hab e he hJ L g _ hd]
  exact TateModule.coefficientPrimeRingEquiv_padic_residue p R a b hab e he hJ j _

end AlgebraicGeometry.GroupScheme
