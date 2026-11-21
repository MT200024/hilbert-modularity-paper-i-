/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalCompatibleSystem
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Canonical one-place view of a Hilbert compatible system

The completion field uses its canonical normed-field instance. A compatible
system's action then gives the one-place cohomological realization at a place
whose residue characteristic is the chosen rational prime. This conversion
does not construct the actions or their `p`-adic scalar structure.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- Regard a canonical completion action as the corresponding one-place
cohomological realization, preserving its independent Hecke normalization. -/
def EigenformCohomologicalActions.onePlaceRealization
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] (w.adicCompletion E)]
    (hp : p = D.residueCharacteristic w) :
    CohomologicalRealization φ p (w.adicCompletion E) where
  coefficientEmbedding := algebraMap E (w.adicCompletion E)
  action := D.action w
  continuous := D.continuous w
  unramified := by
    intro q hq P _ hP hprime Q _ _ g hg
    exact D.unramified w q hq P hP (hp ▸ hprime) Q g hg
  frobenius_trace := by
    intro q hq P _ hP hprime Q
    exact D.frobenius_trace w q hq P hP (hp ▸ hprime) Q
  frobenius_det := by
    intro q hq P _ hP hprime Q
    exact D.frobenius_det w q hq P hP (hp ▸ hprime) Q

end HilbertModularity.HilbertModularForms
