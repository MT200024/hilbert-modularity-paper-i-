/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.FiniteCharacterReciprocity
public import HilbertModularity.NumberTheory.HilbertModularForms.GaloisRealization

/-! # Algebraic coefficients of finite character twists

The arithmetic reciprocity input gives the geometric character values in the
fixed number field. The actual cusp-form twist therefore has algebraic Hecke
and central coefficients, with respective character powers one and two.
These are the normalizations used in [TripathiGoswami, §3].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms.ArithmeticIdeleRealization

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
  {χ : FiniteAlgebraicGaloisCharacter F E} {ι : E →+* ℂ}

/-- Reciprocity places every unramified normalized prime value in the
specified coefficient field, without changing its embedding. -/
theorem exists_geometricPrimeValue (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ χ.bad)
    (d : PrimeHeckeDatum level q) :
    ∃ a : E, ι a = (r.geometricCharacter.onGL2 d.element : ℂ) := by
  obtain ⟨Q, hQ, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (AlgebraicClosure F)) q.asIdeal
  let : Q.IsMaximal := hQ
  let : Q.LiesOver q.asIdeal := hOver
  exact ⟨_, (r.geometricCharacter_frobenius q hq d q.asIdeal rfl Q).symm⟩

/-- The algebraic geometric-Artin value of a normalized prime coset. -/
def geometricPrimeValue (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ χ.bad)
    (d : PrimeHeckeDatum level q) : E :=
  (r.exists_geometricPrimeValue q hq d).choose

theorem geometricPrimeValue_spec (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ χ.bad)
    (d : PrimeHeckeDatum level q) :
    ι (r.geometricPrimeValue q hq d) = (r.geometricCharacter.onGL2 d.element : ℂ) :=
  (r.exists_geometricPrimeValue q hq d).choose_spec

/-- The chosen algebraic value agrees with every absolute Frobenius choice. -/
theorem geometricPrimeValue_eq_frobenius (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ χ.bad)
    (d : PrimeHeckeDatum level q)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    r.geometricPrimeValue q hq d =
      (χ.toMonoidHom (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) := by
  apply ι.injective
  rw [r.geometricPrimeValue_spec, r.geometricCharacter_frobenius q hq d P hP Q]

/-- The actual twisted eigenform with coefficients in the original field.
Its exceptional set is exactly the union of the two supplied finite sets.
The level is assumed to kill the twisting character. -/
def algebraicTwist (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1) :
    AlgebraicGoodPrimeEigenform level μ E where
  form :=
    { r.twist φ.form hK with
      bad := φ.form.bad ∪ χ.bad
      bad_finite := φ.form.bad_finite.union χ.bad_finite
      spherical_level := fun q hq => φ.form.spherical_level q (fun h => hq (Or.inl h))
      hecke_data := fun q hq => φ.form.hecke_data q (fun h => hq (Or.inl h))
      hecke_value := fun q hq =>
        (r.twist φ.form hK).hecke_value q
          (by simpa only [twist_bad] using (fun h => hq (Or.inl h)))
      hecke_eigen := fun q hq => by
        have he := (r.twist φ.form hK).hecke_eigen q
          (by simpa only [twist_bad] using (fun h => hq (Or.inl h)))
        have hd := GoodPrimeEigenform.twist_hecke_data φ.form
          r.geometricCharacter hK r.geometricCharacter_trivial_positive_infinity
          q (fun h => hq (Or.inl h))
        change (r.twist φ.form hK).hecke_data q _ = φ.form.hecke_data q _ at hd
        rw [hd] at he
        exact he }
  complexEmbedding := ι
  heckeCoefficient q hq :=
    r.geometricPrimeValue q (fun h => hq (Or.inr h))
      (φ.form.hecke_data q (fun h => hq (Or.inl h))) *
        φ.heckeCoefficient q (fun h => hq (Or.inl h))
  heckeCoefficient_spec q hq := by
    have hc := φ.heckeCoefficient_spec q (fun h => hq (Or.inl h))
    rw [hι] at hc
    rw [map_mul, r.geometricPrimeValue_spec, hc]
    exact (GoodPrimeEigenform.twist_hecke_value _ _ _ _ _ _).symm
  centralCoefficient q hq :=
    φ.centralCoefficient q (fun h => hq (Or.inl h)) *
      r.geometricPrimeValue q (fun h => hq (Or.inr h))
        (φ.form.hecke_data q (fun h => hq (Or.inl h))) ^ 2
  centralCoefficient_spec q hq := by
    have hc := φ.centralCoefficient_spec q (fun h => hq (Or.inl h))
    rw [hι] at hc
    rw [map_mul, map_pow, r.geometricPrimeValue_spec, hc]
    change _ = ((r.twist φ.form hK).central_character
      (adelicDeterminant F (φ.form.hecke_data q (fun h => hq (Or.inl h))).element) : ℂ)
    rw [GoodPrimeEigenform.twist_central_character]
    simp only [MonoidHom.mul_apply, Units.val_mul,
      FiniteIdeleClassCharacter.onGL2_apply]
    ring

@[simp]
theorem algebraicTwist_apply (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    (φ : AlgebraicGoodPrimeEigenform level μ E) (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1)
    (g : AdelicGL2 F) :
    (r.algebraicTwist φ hι hK).form.toFun g =
      (r.geometricCharacter.onGL2 g : ℂ) * φ.form.toFun g :=
  GoodPrimeEigenform.twist_apply _ _ _ _ _

/-- The central character acquires the square of the twisting character. -/
@[simp]
theorem algebraicTwist_central_character (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    (φ : AlgebraicGoodPrimeEigenform level μ E) (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1) :
    (r.algebraicTwist φ hι hK).form.central_character =
      φ.form.central_character * r.geometricCharacter.toHom * r.geometricCharacter.toHom :=
  GoodPrimeEigenform.twist_central_character _ _ _ _

@[simp]
theorem algebraicTwist_complexEmbedding (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    (φ : AlgebraicGoodPrimeEigenform level μ E) (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1) :
    (r.algebraicTwist φ hι hK).complexEmbedding = ι := (rfl)

/-- The algebraic twist retains the precise union of bad sets. -/
@[simp]
theorem algebraicTwist_bad (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    (φ : AlgebraicGoodPrimeEigenform level μ E) (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1) :
    (r.algebraicTwist φ hι hK).form.bad = φ.form.bad ∪ χ.bad := by
  rfl

/-- The algebraic Hecke coefficient has the geometric-Frobenius multiplier. -/
theorem algebraicTwist_heckeCoefficient (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    (φ : AlgebraicGoodPrimeEigenform level μ E) (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad ∪ χ.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (r.algebraicTwist φ hι hK).heckeCoefficient q
        (by simpa only [algebraicTwist_bad] using hq) =
      (χ.toMonoidHom (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) *
        φ.heckeCoefficient q (fun h => hq (Or.inl h)) := by
  change r.geometricPrimeValue q _ _ * _ = _
  rw [r.geometricPrimeValue_eq_frobenius q _ _ P hP Q]

/-- The central coefficient has the square of the same multiplier. -/
theorem algebraicTwist_centralCoefficient (r : ArithmeticIdeleRealization χ ι)
    {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
    (φ : AlgebraicGoodPrimeEigenform level μ E) (hι : φ.complexEmbedding = ι)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad ∪ χ.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (r.algebraicTwist φ hι hK).centralCoefficient q
        (by simpa only [algebraicTwist_bad] using hq) =
      φ.centralCoefficient q (fun h => hq (Or.inl h)) *
        (χ.toMonoidHom (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) ^ 2 := by
  change _ * r.geometricPrimeValue q _ _ ^ 2 = _
  rw [r.geometricPrimeValue_eq_frobenius q _ _ P hP Q]

end HilbertModularity.HilbertModularForms.ArithmeticIdeleRealization
