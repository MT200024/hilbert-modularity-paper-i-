/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.CoefficientFree
public import HilbertModularity.RepresentationTheory.PrimeDual

/-! # Actual geometric RM-prime dual reduction

The actual integral RM-prime Tate dual reduces equivariantly to the dual of
actual geometric coefficient torsion, with its canonical residue pairing.
This supplies a concrete prerequisite for the cohomological convention in
[TripathiGoswami]; the etale-cohomology comparison remains separate.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (R : Type*) [CommRing R] [IsDomain R] [Module R (Points K (AlgebraicClosure K) A)]
  (hφ : ∀ r, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    Module.toAddMonoidEnd R (Points K (AlgebraicClosure K) A) r =
      pointsMap K (AlgebraicClosure K) f)
  (p : ℕ) [Fact p.Prime]
  [IsFinite (multiplicationMap K A p).left] [Surjective (multiplicationMap K A p).left]

/-- The actual geometric prime Tate dual reduces to the actual torsion contragredient. -/
def primeResidualDualIntegralTateEquiv
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal] :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
    ((primeIntegralTateRepresentation K A R hφ p (Ideal.span {a}) e he hJ).dual.baseChange
      (R ⧸ Ideal.span {a})).Equiv (coefficientTorsionRepresentation K A R hφ a).dual := by
  haveI := points_coefficient_galois_comm K A R hφ
  exact TateModule.coefficientPrimeResidualDualEquiv p R _
    (Points K (AlgebraicClosure K) A) a b ha hab e he hJ (points_nsmul_surjective K A p)

/-- The actual geometric residual pairing is the residue of the actual integral RM-prime pairing. -/
theorem primeResidualDualIntegralTateEquiv_tmul
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal] (c : R ⧸ Ideal.span {a})
    (φ :
      letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
        (Ideal.span {a}) e he hJ
      Module.Dual (AdicCompletion (Ideal.span {a}) R) (integralTate K A p))
    (x : integralTate K A p) :
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A)
      (Ideal.span {a}) e he hJ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
    primeResidualDualIntegralTateEquiv K A R hφ p a b ha hab e he hJ
      (c ⊗ₜ[AdicCompletion (Ideal.span {a}) R] φ)
      (TateModule.principalProjection p R (Points K (AlgebraicClosure K) A) a b hab x) =
        c * AdicCompletion.evalOneₐ (Ideal.span {a}) (φ x) := by
  have := points_coefficient_galois_comm K A R hφ
  exact TateModule.coefficientPrimeResidualDualEquiv_tmul p R _
    (Points K (AlgebraicClosure K) A) a b ha hab e he hJ (points_nsmul_surjective K A p) c φ x

end AlgebraicGeometry.GroupScheme
