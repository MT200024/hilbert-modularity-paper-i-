/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalCompatibleSystem

/-! # Galois actions attached to a bounded weight-two Hilbert eigenform

This is the named literature input for the existence of the local Galois
actions. Their shared polynomial is proved separately by
`EigenformCohomologicalActions.toCompatibleSystem`.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
  [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The weight-two Hilbert eigenform Galois construction, in the
geometric-Frobenius and cohomological normalization of
[src_skinner_hilbert_2009, §1, (1), pp. 241–242]. The source constructs a
continuous semisimple representation at each coefficient place, with the
unramified Hecke roots. The precise one-field formulation also uses the local
field-of-definition observation in §2 (p. 244), the spherical Hecke parameter
in §2.4.2 (pp. 252–255), and odd-involution descent (p. 256). The bounded
adelic vector with finite-image center gives a classical cuspidal vector by
the dictionary of [SkinnerWiles, §3.1, pp. 27–29]. These correspondence and
descent steps are included in this admitted literature input; the theorem is
not claimed to appear verbatim in either source. In particular, the output
supplies trace and determinant separately, not a presumed common polynomial. -/
theorem exists_eigenformCohomologicalActions
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (hbounded : ∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C)
    (hcentral : (Set.range φ.form.central_character).Finite) :
    Nonempty (EigenformCohomologicalActions φ) := by
  sorry

end HilbertModularity.HilbertModularForms
