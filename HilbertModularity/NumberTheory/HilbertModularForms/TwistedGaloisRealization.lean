/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.AlgebraicFiniteTwist
public import HilbertModularity.NumberTheory.HilbertModularForms.GaloisTwist

/-! # Galois realizations of finite twists

The actual scalar twist satisfies the cohomological realization identities for
the twisted eigenform. This proves the finite-twist dictionary used in
[TripathiGoswami, §3], retaining the level and coefficient embeddings.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F A : Type*} [Field F] [NumberField F] [Field A] [NumberField A]
  {χ : FiniteAlgebraicGaloisCharacter F A} {ι : A →+* ℂ}
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  {φ : AlgebraicGoodPrimeEigenform level μ A}
  {p : ℕ} [Fact p.Prime] {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]

/-- A finite twist of the given realization realizes the actual twisted
algebraic eigenform. Continuity is stated at its specified coefficient
embedding; for canonical completions this is part of the algebraic character.
No existence or uniqueness theorem for automorphic Galois representations is
assumed here. -/
def CohomologicalRealization.finiteTwist
    (ρ : CohomologicalRealization φ p E)
    (r : ArithmeticIdeleRealization χ ι) (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1)
    (hχ : Continuous (fun g : AbsoluteGalois F =>
      ρ.coefficientEmbedding (χ.toMonoidHom g : A))) :
    CohomologicalRealization (r.algebraicTwist φ hι hK) p E where
  coefficientEmbedding := ρ.coefficientEmbedding
  action := ρ.action.characterTwist
    ((Units.map ρ.coefficientEmbedding.toMonoidHom).comp χ.toMonoidHom)
  continuous i j := by
    convert hχ.mul (ρ.continuous i j) using 1
    funext g
    simp [Representation.characterTwist_apply]
  unramified q hq P _ hP hp Q _ _ g hg := by
    have hgood : q ∉ φ.form.bad ∪ χ.bad := by
      simpa only [ArithmeticIdeleRealization.algebraicTwist_bad] using hq
    have hρ := ρ.unramified q (fun h => hgood (Or.inl h)) P hP hp Q g hg
    have hc := χ.unramified q (fun h => hgood (Or.inr h)) P hP Q g hg
    ext v
    simp [Representation.characterTwist_apply, hρ, hc]
  frobenius_trace q hq P _ hP hp Q _ _ := by
    have hgood : q ∉ φ.form.bad ∪ χ.bad := by
      simpa only [ArithmeticIdeleRealization.algebraicTwist_bad] using hq
    rw [r.algebraicTwist_heckeCoefficient φ hι hK q hgood P hP Q]
    rw [trace_characterTwist,
      ρ.frobenius_trace q (fun h => hgood (Or.inl h)) P hP hp Q, map_mul]
    rfl
  frobenius_det q hq P _ hP hp Q _ _ := by
    have hgood : q ∉ φ.form.bad ∪ χ.bad := by
      simpa only [ArithmeticIdeleRealization.algebraicTwist_bad] using hq
    rw [r.algebraicTwist_centralCoefficient φ hι hK q hgood P hP Q]
    change LinearMap.det
      (ρ.coefficientEmbedding (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : A) •
          ρ.action (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) = _
    rw [LinearMap.det_smul,
      ρ.frobenius_det q (fun h => hgood (Or.inl h)) P hP hp Q, map_mul, map_pow]
    simp only [Module.finrank_pi,
      Fintype.card_fin]
    ring

@[simp]
theorem CohomologicalRealization.finiteTwist_coefficientEmbedding
    (ρ : CohomologicalRealization φ p E)
    (r : ArithmeticIdeleRealization χ ι) (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1)
    (hχ : Continuous (fun g : AbsoluteGalois F =>
      ρ.coefficientEmbedding (χ.toMonoidHom g : A))) :
    (ρ.finiteTwist r hι hK hχ).coefficientEmbedding = ρ.coefficientEmbedding := (rfl)

/-- The constructed realization is the character-line tensor product of the
original action, not merely a trace-level restatement. -/
def CohomologicalRealization.finiteTwistTensorEquiv
    (ρ : CohomologicalRealization φ p E)
    (r : ArithmeticIdeleRealization χ ι) (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1)
    (hχ : Continuous (fun g : AbsoluteGalois F =>
      ρ.coefficientEmbedding (χ.toMonoidHom g : A))) :
    ((Representation.ofCharacter
      ((Units.map ρ.coefficientEmbedding.toMonoidHom).comp χ.toMonoidHom)).tprod
        ρ.action).Equiv (ρ.finiteTwist r hι hK hχ).action :=
  Representation.characterTwistTensorEquiv _ _

end HilbertModularity.HilbertModularForms
