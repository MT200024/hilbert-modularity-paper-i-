/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicTorsion
public import HilbertModularity.Algebra.TateModule.CoefficientRank

/-! # Rank of actual canonical-prime torsion

The cardinality of reduction modulo the rational prime compares the two ranks
of the actual Tate lattice. Total ramification then determines the dimension
of the actual canonical-prime scheme kernel, as used in [TripathiGoswami].
-/

@[expose] public noncomputable section
open CategoryTheory HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace AlgebraicGeometry.GroupScheme

variable (K : Type*) [Field K]
  (A : CommGrp (Over (Spec (CommRingCat.of K))))
  (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
  (φ : 𝓞 (realCyclotomicField p) →+* End A)
  [IsFinite (multiplicationMap K A.X p).left]
  [Surjective (multiplicationMap K A.X p).left]

include hp in
/-- The rational Tate rank divided by the real coefficient degree is the dimension of actual canonical-prime torsion. -/
theorem finrank_realPrimeKernel_of_rational_rank (n : ℕ)
    (hrank : Module.finrank ℚ_[p] (rationalTate K A.X p) = ((p - 1) / 2) * n) :
    letI := realPrimeGenerator_isMaximal p hp
    letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
    letI := coefficientKernelModule K A (𝓞 (realCyclotomicField p)) φ (realPrimeGenerator p)
    Module.finrank (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
      (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ (realPrimeGenerator p))).X) = n := by
  let := realPrimeGenerator_isMaximal p hp
  let := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
  let := pointsCoefficientModule K A (𝓞 (realCyclotomicField p)) φ
  let := coefficientKernelModule K A (𝓞 (realCyclotomicField p)) φ (realPrimeGenerator p)
  have hcard : Nat.card (𝓞 (realCyclotomicField p) ⧸ Ideal.span {(p : 𝓞 (realCyclotomicField p))}) =
      p ^ ((p - 1) / 2) := by
    change Ideal.absNorm (Ideal.span {(p : 𝓞 (realCyclotomicField p))}) = _
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, finrank_realCyclotomicField p hp]
  change Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] integralTate K A.X p) = _ at hrank
  rw [Module.finrank_baseChange] at hrank
  exact (coefficientKernelLinearEquiv K A (𝓞 (realCyclotomicField p)) φ
    (realPrimeGenerator p)).finrank_eq.trans
      (TateModule.principalTorsion_finrank_of_integral_rank p (𝓞 (realCyclotomicField p))
        (Points K (AlgebraicClosure K) A.X) (realPrimeGenerator p) (realPrimeCofactor p hp)
        (realPrimeGenerator_ne_zero p hp) (realPrimeGenerator_mul_cofactor p hp)
        ((p - 1) / 2) (realPrimeRamification_pos p hp) (span_realPrimeGenerator_pow p hp)
        (points_nsmul_surjective K A.X p) ((p - 1) / 2) n
        (realPrimeRamification_pos p hp) hcard hrank)

end AlgebraicGeometry.GroupScheme
