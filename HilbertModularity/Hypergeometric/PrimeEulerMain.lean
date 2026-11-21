/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ChosenEulerDeepCuspModularity
public import HilbertModularity.Hypergeometric.PrimePlusConductorEulerIrreducibility

/-! # Conditional prime-level manuscript main results

These deductions use the precise named literature inputs documented in the
project assumption inventory. The actual conductor irreducibility, lifting
checklist, coefficient maps and finite comparison character are proved or
constructed internally; no such application premise remains.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic HilbertModularForms

variable (p : ℕ) [Fact p.Prime]

/-- Either valuation-depth-three condition gives the finite-field Hilbert modularity property of the actual chosen Euler family. See
[TripathiGoswamiRevised, Theorems `thm:prime`,
`thm:prime-deep-modular` and `thm:intro-main`]. -/
theorem finiteFieldHilbertModularAt_of_deep_cusp
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ₀ : ProjectiveLine.Parameter ℚ)
    (hdeep : 3 ≤ padicValRat p ξ₀.val ∨ 3 ≤ padicValRat p (1 - ξ₀.val)) :
    FiniteFieldHilbertModularAt p m (darmonRationalParameter p ξ₀).val := by
  exact finiteFieldHilbertModularAt_of_deep_cusp_of_irreducible p hp m hmPos hmLt ξ₀ hdeep
    (chosenConductorPlusCoordinate_isIrreducible p hp m hmPos hmLt (darmonRationalParameter p ξ₀))

/-- The labelled weight-zero quotient condition gives the finite-field Hilbert modularity property. See
[TripathiGoswamiRevised, Theorems `thm:prime`,
`thm:prime-deep-modular` and `thm:intro-main`]. -/
theorem finiteFieldHilbertModularAt_of_ordinary
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (W : PrimePlusOrdinaryQuotient p hp ξ m
      (by simpa using (eulerExponent_coprime_of_prime p m
        (Fact.out : p.Prime) hmPos hmLt))) :
    FiniteFieldHilbertModularAt p m ξ.val := by
  exact finiteFieldHilbertModularAt_of_ordinary_of_irreducible p hp m hmPos hmLt ξ W
    (chosenConductorPlusCoordinate_isIrreducible p hp m hmPos hmLt ξ)

/-- Either reduced cubic-divisibility condition gives one eigenform identifying the actual Euler system at every coefficient place. See
[TripathiGoswamiRevised, Theorems `thm:prime`,
`thm:prime-deep-modular` and `thm:intro-main`]. -/
theorem exists_chosenEuler_allPlaceEigenform_of_cubic
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A)) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (j : cyclotomicField p →+* B)
        (level : FiniteLevel (realCyclotomicField p))
        (μ : AdditiveQuotientMeasure (realCyclotomicField p))
        (ψ : AlgebraicGoodPrimeEigenform level μ B),
        letI : Algebra (cyclotomicField p) B := j.toAlgebra
        ∃ T : EigenformCohomologicalActions ψ,
          ψ.complexEmbedding = B.val.toRingHom ∧
          (∃ b : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ b) ∧
          (Set.range ψ.form.central_character).Finite ∧
          (∀ q, q ∉ (chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt (darmonRationalParameter p ξ₀)).bad →
            ∃ hψ : q ∉ ψ.form.bad,
              ((chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt (darmonRationalParameter p ξ₀)).polynomial q).map
                j = ψ.heckePolynomial q hψ) ∧
          ∀ v : HeightOneSpectrum (𝓞 B),
            Nonempty ((((chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt (darmonRationalParameter p ξ₀)
              ).extendCoefficients (L := B)).action v).Equiv (T.action v)) := by
  exact exists_chosenEuler_allPlaceEigenform_of_cubic_of_irreducible p hp m hmPos hmLt ξ₀ hξ hA hB hAB hdeep
    (chosenConductorPlusCoordinate_isIrreducible p hp m hmPos hmLt (darmonRationalParameter p ξ₀))

/-- The local-to-global prime-level criterion: the labelled weight-zero
quotient gives one eigenform for the actual chosen Euler system at all places.
[TripathiGoswamiRevised, Theorem `thm:prime`]. -/
theorem exists_chosenEuler_allPlaceEigenform_of_ordinary
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (W : PrimePlusOrdinaryQuotient p hp ξ m
      (by simpa using (eulerExponent_coprime_of_prime p m
        (Fact.out : p.Prime) hmPos hmLt))) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (j : cyclotomicField p →+* B)
        (level : FiniteLevel (realCyclotomicField p))
        (μ : AdditiveQuotientMeasure (realCyclotomicField p))
        (ψ : AlgebraicGoodPrimeEigenform level μ B),
        letI : Algebra (cyclotomicField p) B := j.toAlgebra
        ∃ T : EigenformCohomologicalActions ψ,
          ψ.complexEmbedding = B.val.toRingHom ∧
          (∃ b : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ b) ∧
          (Set.range ψ.form.central_character).Finite ∧
          (∀ q, q ∉ (chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt ξ).bad →
            ∃ hψ : q ∉ ψ.form.bad,
              ((chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt ξ).polynomial q).map
                j = ψ.heckePolynomial q hψ) ∧
          ∀ v : HeightOneSpectrum (𝓞 B),
            Nonempty ((((chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt ξ
              ).extendCoefficients (L := B)).action v).Equiv (T.action v)) := by
  exact exists_chosenEuler_allPlaceEigenform_of_chosenConductorChecklist p hp m hmPos hmLt ξ
    (chosenConductorOrdinaryWeightTwoInput_of_irreducible p hp m _ ξ W
      (chosenConductorPlusCoordinate_isIrreducible p hp m hmPos hmLt ξ))

end HilbertModularity.Hypergeometric
