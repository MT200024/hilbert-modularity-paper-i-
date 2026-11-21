/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveDualPolynomialBaseChange

/-! # Scalar extension of the selected plus Jacobian's full polynomial

The two selected specializations implement coefficient extension in
[TripathiGoswamiRevised, Example `ex:p5-numerical-check`]. The original
Jacobian, geometric Frobenius and scalar maps are retained.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain Polynomial
open scoped NumberField TensorProduct

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

/-- Scalar extension preserves a specified full cohomological polynomial
of the same selected plus Jacobian, without transporting a chosen basis. -/
theorem primePlus_fullDualPolynomial_baseChange
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))
    (R : Polynomial ℚ_[ℓ])
    (hR : ((tateRepresentation (realCyclotomicField p)
      (primePlusFiber p hp ξ).X ℓ).dual g).charpolyRev = R) :
    (((tateRepresentation (realCyclotomicField p)
      (primePlusFiber p hp ξ).X ℓ).baseChange L).dual g).charpolyRev =
        R.map (algebraMap ℚ_[ℓ] L) := by
  exact Examples.dualTate_charpolyRev_baseChange_of_polynomial
    (L := L) (tateRepresentation (realCyclotomicField p)
      (primePlusFiber p hp ξ).X ℓ) g R hR


open Examples

local instance fullPolynomialFivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The eleven-prime polynomial of the actual selected Jacobian after
extension to the field used for its two real-multiplication labels. -/
theorem primeFive_fullDualPolynomial11_baseChange
    (L : Type*) [Field L] [Algebra ℚ_[5] L]
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    (((tateRepresentation (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5).baseChange L).dual
      (NumberField.geometricFrobenius (realCyclotomicField 5)
        (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)).charpolyRev =
      primeFiveNumericalPolynomial11 L := by
  have hR := selectedFullPolynomial11_intrinsic P W hk Q h5P
  have h := primePlus_fullDualPolynomial_baseChange 5
    selectedRMProductFiveLowerBound primeFiveParameter 5 L
    (NumberField.geometricFrobenius (realCyclotomicField 5)
      (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)
    (primeFiveNumericalPolynomial11 ℚ_[5])
  with_reducible
    exact (h hR).trans (primeFiveNumericalPolynomial11_baseChange L)

/-- The forty-one-prime polynomial of the actual selected Jacobian after
extension to the field used for its two real-multiplication labels. -/
theorem primeFive_fullDualPolynomial41_baseChange
    (L : Type*) [Field L] [Algebra ℚ_[5] L]
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 41)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    (((tateRepresentation (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5).baseChange L).dual
      (NumberField.geometricFrobenius (realCyclotomicField 5)
        (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)).charpolyRev =
      primeFiveNumericalPolynomial41 L := by
  have hR := selectedFullPolynomial41_intrinsic P W hk Q h5P
  have h := primePlus_fullDualPolynomial_baseChange 5
    selectedRMProductFiveLowerBound primeFiveParameter 5 L
    (NumberField.geometricFrobenius (realCyclotomicField 5)
      (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)
    (primeFiveNumericalPolynomial41 ℚ_[5])
  with_reducible
    exact (h hR).trans (primeFiveNumericalPolynomial41_baseChange L)

end HilbertModularity.Hypergeometric
