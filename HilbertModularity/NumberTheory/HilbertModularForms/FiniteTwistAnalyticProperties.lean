/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.FiniteTwistCoefficientExtension
public import HilbertModularity.NumberTheory.HilbertModularForms.EigenformCohomologicalExistence

/-! # Boundedness and all-place realizations of finite twists

A finite character preserves boundedness and finiteness of the central image.
Thus the actual finite twist in [TripathiGoswami, §6] satisfies the analytic
hypotheses of the existing all-place cohomological construction.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- Multiplication by a finite idele character preserves boundedness. -/
theorem FiniteIdeleClassCharacter.bounded_twist
    (χ : FiniteIdeleClassCharacter F) (f : AdelicGL2 F → ℂ)
    (hf : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) :
    ∃ C : ℝ, ∀ g, ‖(χ.onGL2 g : ℂ) * f g‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := (χ.finite_range.image (fun z : ℂˣ => ‖(z : ℂ)‖)).bddAbove
  have hd (g : AdelicGL2 F) : ‖(χ.onGL2 g : ℂ)‖ ≤ D :=
    hD ⟨χ.onGL2 g, ⟨adelicDeterminant F g, (χ.onGL2_apply g).symm⟩, rfl⟩
  refine ⟨D * C, fun g => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hd g) (hC g) (norm_nonneg _) ((norm_nonneg _).trans (hd g))

/-- The central character of a finite twist still has finite image. -/
theorem FiniteIdeleClassCharacter.finite_range_twisted_center
    (χ : FiniteIdeleClassCharacter F) (ω : (AdeleRing F)ˣ →* ℂˣ)
    (hω : (Set.range ω).Finite) :
    (Set.range (ω * χ.toHom * χ.toHom)).Finite := by
  apply ((hω.prod χ.finite_range).image
    (fun z : ℂˣ × ℂˣ => z.1 * z.2 * z.2)).subset
  rintro _ ⟨z, rfl⟩
  exact ⟨(ω z, χ.toHom z), ⟨⟨z, rfl⟩, ⟨z, rfl⟩⟩, rfl⟩

variable {A B : Type*} [Field A] [NumberField A] [Field B] [NumberField B]
  [NumberField.IsTotallyReal F]
  {K : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  {φ : AlgebraicGoodPrimeEigenform K μ A}
  {p : ℕ} [Fact p.Prime] {E : Type*} [NormedField E] [NormedAlgebra ℚ_[p] E]

/-- A bounded eigenform with finite central image admits its actual finite twist
and an all-place compatible system over a constructed common coefficient field.
The specified local realization is the character tensor the original action;
the all-place system has the same twisted eigenform's Hecke polynomials. -/
theorem CohomologicalRealization.exists_finiteTwist_compatibleSystem
    (ρ : CohomologicalRealization φ p E) (χ : FiniteAlgebraicGaloisCharacter F B)
    (k : B →+* E)
    (hbounded : ∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C)
    (hcentral : (Set.range φ.form.central_character).Finite) :
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
      (∃ D : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ D) ∧
      (Set.range ψ.form.central_character).Finite ∧
      Nonempty (EigenformCompatibleSystem ψ) ∧
      Nonempty (((Representation.ofCharacter
        ((Units.map k.toMonoidHom).comp χ.toMonoidHom)).tprod ρ.action).Equiv
          ρ'.action) := by
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[p] E).injective
  dsimp only
  obtain ⟨c, r, s, ψ, ρ', hc, hfun, hcenter, hcomplex, hbad, hcoeff, hequiv⟩ :=
    ρ.exists_finiteTwist_over_compositum χ k
  have hb : ∃ D : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ D := by
    simpa only [hfun] using r.geometricCharacter.bounded_twist φ.form.toFun hbounded
  have hz : (Set.range ψ.form.central_character).Finite := by
    rw [hcenter]
    exact r.geometricCharacter.finite_range_twisted_center _ hcentral
  obtain ⟨D⟩ := exists_eigenformCohomologicalActions ψ hb hz
  exact ⟨c, r, s, ψ, ρ', hc, hfun, hcenter, hcomplex, hbad, hcoeff,
    hb, hz, ⟨D.toCompatibleSystem⟩, hequiv⟩

end HilbertModularity.HilbertModularForms
