/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.GaloisRealization
public import HilbertModularity.RepresentationTheory.FiniteCharacterContinuity

/-! # Enlarging the coefficients of an eigenform and a finite character

The complex eigenfunction and the local Galois action stay fixed. Only their
algebraic coefficient field changes, through compatible embeddings. This is
the coefficient step before the finite twist in [TripathiGoswami, §6].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F A B : Type*} [Field F] [NumberField F]
  [Field A] [NumberField A] [Field B] [NumberField B]

/-- Map a finite algebraic character into a larger coefficient number field.
Local constancy supplies continuity at every new coefficient place. -/
def FiniteAlgebraicGaloisCharacter.mapCoefficients
    (χ : FiniteAlgebraicGaloisCharacter F A) (i : A →+* B) :
    FiniteAlgebraicGaloisCharacter F B where
  toMonoidHom := (Units.map i.toMonoidHom).comp χ.toMonoidHom
  finite_range := by
    change (Set.range ((Units.map i.toMonoidHom) ∘ χ.toMonoidHom)).Finite
    rw [Set.range_comp]
    exact χ.finite_range.image _
  local_continuous w := χ.continuous_embedding ((algebraMap B (w.adicCompletion B)).comp i)
  bad := χ.bad
  bad_finite := χ.bad_finite
  unramified q hq P _ hP Q _ _ g hg := by
    change Units.map i.toMonoidHom (χ.toMonoidHom g) = 1
    rw [χ.unramified q hq P hP Q g hg, map_one]

@[simp]
theorem FiniteAlgebraicGaloisCharacter.mapCoefficients_apply
    (χ : FiniteAlgebraicGaloisCharacter F A) (i : A →+* B)
    (g : HilbertModularForms.AbsoluteGalois F) :
    ((χ.mapCoefficients i).toMonoidHom g : B) = i (χ.toMonoidHom g : A) := (rfl)

@[simp]
theorem FiniteAlgebraicGaloisCharacter.mapCoefficients_bad
    (χ : FiniteAlgebraicGaloisCharacter F A) (i : A →+* B) :
    (χ.mapCoefficients i).bad = χ.bad := (rfl)

/-- Realizing the transported character is composition of coefficient maps. -/
theorem FiniteAlgebraicGaloisCharacter.mapCoefficients_embedding
    {L : Type*} [Field L] (χ : FiniteAlgebraicGaloisCharacter F A)
    (i : A →+* B) (k : B →+* L) :
    (Units.map k.toMonoidHom).comp (χ.mapCoefficients i).toMonoidHom =
      (Units.map (k.comp i).toMonoidHom).comp χ.toMonoidHom := by
  ext g
  rfl

namespace HilbertModularForms

variable {K : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The same eigenfunction with its coefficients embedded into a number field. -/
def AlgebraicGoodPrimeEigenform.extendCoefficients
    (φ : AlgebraicGoodPrimeEigenform K μ A) (i : A →+* B)
    (j : B →+* ℂ) (hj : j.comp i = φ.complexEmbedding) :
    AlgebraicGoodPrimeEigenform K μ B where
  form := φ.form
  complexEmbedding := j
  heckeCoefficient q hq := i (φ.heckeCoefficient q hq)
  heckeCoefficient_spec q hq := by
    change (j.comp i) _ = _
    rw [hj, φ.heckeCoefficient_spec]
  centralCoefficient q hq := i (φ.centralCoefficient q hq)
  centralCoefficient_spec q hq := by
    change (j.comp i) _ = _
    rw [hj, φ.centralCoefficient_spec]

@[simp]
theorem AlgebraicGoodPrimeEigenform.extendCoefficients_form
    (φ : AlgebraicGoodPrimeEigenform K μ A) (i : A →+* B)
    (j : B →+* ℂ) (hj : j.comp i = φ.complexEmbedding) :
    (φ.extendCoefficients i j hj).form = φ.form := (rfl)

@[simp]
theorem AlgebraicGoodPrimeEigenform.extendCoefficients_complexEmbedding
    (φ : AlgebraicGoodPrimeEigenform K μ A) (i : A →+* B)
    (j : B →+* ℂ) (hj : j.comp i = φ.complexEmbedding) :
    (φ.extendCoefficients i j hj).complexEmbedding = j := (rfl)

variable {φ : AlgebraicGoodPrimeEigenform K μ A}
  {p : ℕ} [Fact p.Prime] {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]

/-- An extension of the local coefficient embedding preserves the actual
continuous rank-two Galois action and all its good-prime identities. -/
def CohomologicalRealization.extendCoefficients
    (ρ : CohomologicalRealization φ p E) (i : A →+* B)
    (j : B →+* ℂ) (hj : j.comp i = φ.complexEmbedding)
    (k : B →+* E) (hk : k.comp i = ρ.coefficientEmbedding) :
    CohomologicalRealization (φ.extendCoefficients i j hj) p E where
  coefficientEmbedding := k
  action := ρ.action
  continuous := ρ.continuous
  unramified := ρ.unramified
  frobenius_trace q hq P _ hP hp Q _ _ := by
    change _ = (k.comp i) _
    rw [hk]
    exact ρ.frobenius_trace q hq P hP hp Q
  frobenius_det q hq P _ hP hp Q _ _ := by
    change _ = _ * (k.comp i) _
    rw [hk]
    exact ρ.frobenius_det q hq P hP hp Q

@[simp]
theorem CohomologicalRealization.extendCoefficients_action
    (ρ : CohomologicalRealization φ p E) (i : A →+* B)
    (j : B →+* ℂ) (hj : j.comp i = φ.complexEmbedding)
    (k : B →+* E) (hk : k.comp i = ρ.coefficientEmbedding) :
    (ρ.extendCoefficients i j hj k hk).action = ρ.action := (rfl)

@[simp]
theorem CohomologicalRealization.extendCoefficients_coefficientEmbedding
    (ρ : CohomologicalRealization φ p E) (i : A →+* B)
    (j : B →+* ℂ) (hj : j.comp i = φ.complexEmbedding)
    (k : B →+* E) (hk : k.comp i = ρ.coefficientEmbedding) :
    (ρ.extendCoefficients i j hj k hk).coefficientEmbedding = k := (rfl)

end HilbertModularForms
end HilbertModularity
