/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CoefficientCompositum
public import HilbertModularity.NumberTheory.HilbertModularForms.CoefficientExtension
public import HilbertModularity.NumberTheory.HilbertModularForms.FiniteTwistExistence

/-! # Finite twists with independent coefficient fields

The form and the finite character need not initially have the same algebraic
coefficient field. Their given embeddings into the local field determine a
finite compositum; extending the complex embedding and applying the finite-twist
construction proves the application in [TripathiGoswami, §6].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F A B : Type*} [Field F] [NumberField F]
  [Field A] [NumberField A] [Field B] [NumberField B]
  {K : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  {φ : AlgebraicGoodPrimeEigenform K μ A}
  {p : ℕ} [Fact p.Prime] {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]

/-- Twisting by a finite character in an independent number field produces an
actual eigenform and Galois realization over the compositum inside `E`. The
comparison uses the original Galois action and the specified character embedding.
The extended complex embedding agrees with the original form embedding. -/
theorem CohomologicalRealization.exists_finiteTwist_over_compositum
    (ρ : CohomologicalRealization φ p E) (χ : FiniteAlgebraicGaloisCharacter F B)
    (k : B →+* E) :
    letI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[p] E).injective
    let C := coefficientCompositum ρ.coefficientEmbedding k
    let χC := χ.mapCoefficients (coefficientCompositum.right ρ.coefficientEmbedding k)
    ∃ (c : C →+* ℂ)
      (r : ArithmeticIdeleRealization χC c)
      (s : HeckeLevelRefinement K r.geometricCharacter)
      (ψ : AlgebraicGoodPrimeEigenform s.level μ C)
      (ρ' : CohomologicalRealization ψ p E),
      c.comp (coefficientCompositum.left ρ.coefficientEmbedding k) = φ.complexEmbedding ∧
      (∀ g, ψ.form.toFun g = (r.geometricCharacter.onGL2 g : ℂ) * φ.form.toFun g) ∧
      ψ.form.central_character =
        φ.form.central_character * r.geometricCharacter.toHom * r.geometricCharacter.toHom ∧
      ψ.complexEmbedding = c ∧
      ψ.form.bad = (φ.form.bad ∪ s.bad) ∪ χ.bad ∧
      ρ'.coefficientEmbedding = C.val.toRingHom ∧
      Nonempty (((Representation.ofCharacter
        ((Units.map k.toMonoidHom).comp χ.toMonoidHom)).tprod ρ.action).Equiv
          ρ'.action) := by
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[p] E).injective
  dsimp only
  obtain ⟨c, hc⟩ := coefficientCompositum.exists_complexEmbedding
    ρ.coefficientEmbedding k φ.complexEmbedding
  let ρC := ρ.extendCoefficients
    (coefficientCompositum.left ρ.coefficientEmbedding k) c hc
    (coefficientCompositum ρ.coefficientEmbedding k).val.toRingHom
    (coefficientCompositum.val_comp_left ρ.coefficientEmbedding k)
  have h := ρC.exists_finiteTwist
      (χ.mapCoefficients (coefficientCompositum.right ρ.coefficientEmbedding k))
  rw [AlgebraicGoodPrimeEigenform.extendCoefficients_complexEmbedding] at h
  simp only [ρC,
    AlgebraicGoodPrimeEigenform.extendCoefficients_form,
    CohomologicalRealization.extendCoefficients_action,
    CohomologicalRealization.extendCoefficients_coefficientEmbedding,
    FiniteAlgebraicGaloisCharacter.mapCoefficients_bad,
    FiniteAlgebraicGaloisCharacter.mapCoefficients_embedding,
    coefficientCompositum.val_comp_right] at h
  obtain ⟨r, s, ψ, ρ', hfun, hcentral, hcomplex, hbad, hcoeff, hequiv⟩ := h
  exact ⟨c, r, s, ψ, ρ', hc, hfun, hcentral, hcomplex, hbad, hcoeff, hequiv⟩

end HilbertModularity.HilbertModularForms
