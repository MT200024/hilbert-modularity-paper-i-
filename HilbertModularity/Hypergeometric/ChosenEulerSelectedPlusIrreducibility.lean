/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ChosenEulerIrreducibility
public import HilbertModularity.Hypergeometric.PrimePlusNativeChecklist
public import HilbertModularity.NumberTheory.ComplexConjugation

/-! # The chosen Euler and selected plus-Jacobian irreducibility application

The character comparison is an explicit same-fibre input until the
native coordinate identity is constructed. The exact determinant is derived
from the existing native Tate comparison of that same selected Jacobian.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

local instance selectedPlusIrreducibilityCompletionNorm (p : ℕ) [Fact p.Prime]
    (w : HeightOneSpectrum (𝓞 (cyclotomicField p))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField p)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField p))
    (WithZero (Multiplicative ℤ))

/-- The actual selected plus-Jacobian coordinates and the chosen Euler
completion are absolutely irreducible after a single field extension,
conditional on the explicit same-fibre comparison and native Tate coordinate
equivalence. The latter supplies the exact determinant; neither conclusion
is a literature premise. See [TripathiGoswamiRevised, Lemma
`prime-absolute-irred`]. -/
theorem chosenEuler_selectedPlus_absoluteIrreducible_of_comparison
    (p m : ℕ) [NeZero p] [Fact p.Prime]
    (hN : p.Prime) (hp : 5 ≤ p) (hm : 0 < m) (hmN : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (w : HeightOneSpectrum (𝓞 (cyclotomicField p)))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)))
      (w.adicCompletion (cyclotomicField p))]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+*
        𝒪[w.adicCompletion (cyclotomicField p)])
    (C : PrimePlusNativeTateComparison p hp ξ
      (w.adicCompletion (cyclotomicField p)) β)
    (ν : AbsoluteGalois (realCyclotomicField p) →*
      (w.adicCompletion (cyclotomicField p))ˣ)
    (e : let 𝒞 := chosenSmoothProperEulerFamily p m hN hp hm hmN
      let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN hp hm hmN
      ((Representation.ofCharacter ν).tprod
        (primePlusTateFieldCoordinateAction p hp ξ β).dual).Equiv
          (commonEulerCompletionAction p m 𝒞 R ξ w)) :
    let 𝒞 := chosenSmoothProperEulerFamily p m hN hp hm hmN
    let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN hp hm hmN
    ((commonEulerCompletionAction p m 𝒞 R ξ w).baseChange
        (AlgebraicClosure (w.adicCompletion (cyclotomicField p)))).IsIrreducible ∧
      ((primePlusTateFieldCoordinateAction p hp ξ β).baseChange
        (AlgebraicClosure (w.adicCompletion (cyclotomicField p)))).IsIrreducible := by
  let L := w.adicCompletion (cyclotomicField p)
  let σ := primePlusTateFieldCoordinateAction p hp ξ β
  let := primePlusIntegralTateModule p hp ξ
  obtain ⟨ι, c, hc, hconj⟩ :=
    NumberField.exists_complexConjugation (realCyclotomicField p)
  have hTateDet (g : AbsoluteGalois (realCyclotomicField p)) :
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) L
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))) :=
    primePlusIntegralTate_det_of_nativeComparison p hp ξ L
      C.localMap C.actionEquiv C.integerCoefficients g
  have hcyclo :
      (Field.cyclotomicCharacter (realCyclotomicField p) p c : ℤ_[p]) = -1 :=
    cyclotomicCharacter.coe_eq_neg_one_of_complexConjugation
      p ι c.toRingEquiv hconj
  have hnative :
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange L c) = -1 := by
    rw [hTateDet c, hcyclo]
    simp
  have hσdet : LinearMap.det (σ c) = -1 :=
    ((primePlusTateFieldCoordinateEquiv p hp ξ β C.integralEmbedding).determinant_eq c).trans
      hnative
  exact chosenEulerConductor_absoluteIrreducible_of_comparison
    p m hN hp hm hmN ξ w σ ν e c hc hσdet (AlgebraicClosure L)

end HilbertModularity.Hypergeometric
