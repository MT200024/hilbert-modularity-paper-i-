/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.EigenformLevelRefinement
public import HilbertModularity.NumberTheory.HilbertModularForms.TwistedGaloisRealization
public import HilbertModularity.RepresentationTheory.FiniteCharacterContinuity

/-! # Existence of finite twists with their Galois realizations

Global reciprocity and unramified level compatibility are the two named
literature inputs. The actual adelic eigenfunction and its tensor-product
Galois realization are constructed from them. This is the finite-twist
application in [TripathiGoswami, §3], with geometric Frobenius.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F A : Type*} [Field F] [NumberField F] [Field A] [NumberField A]
  {K : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  {φ : AlgebraicGoodPrimeEigenform K μ A}
  {p : ℕ} [Fact p.Prime] {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]

/-- Every finite algebraic character twist is realized by an actual cuspidal
weight-two eigenfunction at a smaller level. Both coefficient embeddings are
preserved. The Galois compatibility is an equivariant linear isomorphism with
the character-line tensor product, not just equality of good-prime traces.
Local constancy of the finite character supplies continuity at the unchanged
coefficient embedding. -/
theorem CohomologicalRealization.exists_finiteTwist
    (ρ : CohomologicalRealization φ p E) (χ : FiniteAlgebraicGaloisCharacter F A) :
    ∃ (r : ArithmeticIdeleRealization χ φ.complexEmbedding)
      (s : HeckeLevelRefinement K r.geometricCharacter)
      (ψ : AlgebraicGoodPrimeEigenform s.level μ A)
      (ρ' : CohomologicalRealization ψ p E),
      (∀ g, ψ.form.toFun g = (r.geometricCharacter.onGL2 g : ℂ) * φ.form.toFun g) ∧
      ψ.form.central_character =
        φ.form.central_character * r.geometricCharacter.toHom * r.geometricCharacter.toHom ∧
      ψ.complexEmbedding = φ.complexEmbedding ∧
      ψ.form.bad = (φ.form.bad ∪ s.bad) ∪ χ.bad ∧
      ρ'.coefficientEmbedding = ρ.coefficientEmbedding ∧
      Nonempty (((Representation.ofCharacter
        ((Units.map ρ.coefficientEmbedding.toMonoidHom).comp χ.toMonoidHom)).tprod
          ρ.action).Equiv ρ'.action) := by
  obtain ⟨r⟩ := nonempty_arithmeticIdeleRealization χ φ.complexEmbedding
  obtain ⟨s⟩ := nonempty_heckeLevelRefinement K r.geometricCharacter
  have hι : (φ.refineLevel s).complexEmbedding = φ.complexEmbedding :=
    φ.refineLevel_complexEmbedding s
  have hc := χ.continuous_embedding (ρ.refineLevel s).coefficientEmbedding
  refine ⟨r, s, r.algebraicTwist (φ.refineLevel s) hι s.character_trivial,
    (ρ.refineLevel s).finiteTwist r hι s.character_trivial hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    rw [r.algebraicTwist_apply]
    rw [AlgebraicGoodPrimeEigenform.refineLevel_apply]
  · rw [r.algebraicTwist_central_character,
      AlgebraicGoodPrimeEigenform.refineLevel_central_character]
  · exact r.algebraicTwist_complexEmbedding _ _ _
  · rw [r.algebraicTwist_bad, AlgebraicGoodPrimeEigenform.refineLevel_bad]
  · rw [CohomologicalRealization.finiteTwist_coefficientEmbedding,
      CohomologicalRealization.refineLevel_coefficientEmbedding]
  · have he := (ρ.refineLevel s).finiteTwistTensorEquiv r hι s.character_trivial hc
    simpa only [CohomologicalRealization.refineLevel_action,
      CohomologicalRealization.refineLevel_coefficientEmbedding] using (Nonempty.intro he)

end HilbertModularity.HilbertModularForms
